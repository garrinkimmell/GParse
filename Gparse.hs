{-# LANGUAGE NoMonomorphismRestriction #-}
module Gparse where


import Text.Parsec
import Text.Parsec.Indent
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Text.Parsec.Token as Token
import Text.Parsec.Error(messageString)
import Control.Applicative hiding ((<|>),many)
import Data.Functor.Identity
import Data.Maybe(catMaybes)
import Control.Monad(guard)
import Data.List(partition,intersperse)
import Data.Char(isAlpha)

-- emptyDef   :: Token.GenLanguageDef st
emptyDef    = Token.LanguageDef
               { Token.commentStart   = "(%"
               , Token.commentEnd     = "%)"
               , Token.commentLine    = "%"
               , Token.nestedComments = True
               , Token.identStart     = letter <|> char '_'
               , Token.identLetter    = alphaNum <|> oneOf "_'"
               , Token.opStart        = Token.opLetter emptyDef
               , Token.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~()[],{};" <|> alphaNum
               , Token.reservedOpNames= ["::","::="]
               , Token.reservedNames  = ["grammar","defns","defn"]
               , Token.caseSensitive  = True
               }




tokenizer = Token.makeTokenParser emptyDef
identifier = Token.identifier tokenizer
reserved = Token.reserved tokenizer
reservedOp = Token.reservedOp tokenizer
commaSep1 = Token.commaSep1 tokenizer
symbol = Token.symbol tokenizer
operator = Token.operator tokenizer
whiteSpace = Token.whiteSpace tokenizer

doubleColon = reservedOp "::"
doubleColonEqual = reservedOp "::="
-- This isn't right, it doesn't handle spacing right around the quotes
prefix = between  (char '\'') (char '\'') (many1 (alphaNum <|> char '_')) <* whiteSpace

endWithDoubleColon = manyTill (identifier <|> operator) (try (reservedOp "::"))


grammar = reserved "grammar" >> many nonterm

-- A nonterminal production
nonterm = do idAndHom <- commaSep1 nontermName <?> "Non-terminal Names"
             -- FIXME: Do something with the homs, like save them in
             -- the noterm data structure.
             let ids = map fst idAndHom
             doubleColon
             prefix
             doubleColonEqual
             homs <- many hom
             prods <- many rhs
             return (NonTerm ids prods homs)

nontermName = do id <- identifier
                 h <- option Nothing (Just <$> many hom)
                 return (id,h)


hom = do symbol "{{"
         n <- identifier
         txt <- manyTill anyChar (try (symbol "}}"))
         return (n,txt)
-- FIXME: Do something interesting with the binding
bind = do symbol "(+"
          n <- identifier
          txt <- manyTill anyChar (try (symbol "+)"))
          return (n,txt)



-- The right-hand-side of a nonterminal production.
rhs = do
  symbol "|" <?> "Beginning of RHS"
  tokens <- manyTill (identifier <|> operator) (try (reservedOp "::")) <?> "RHS terms"
  manyTill (identifier <|> operator) (try (reservedOp "::"))
  constructor <- identifier <?> "Constructor name" -- Should check
                 -- this begins uppercase
  binds <- many bind
  homs <- many hom
  return $ RHS tokens constructor homs

data Language a = Language Grammar (Judgments a)

language = do g <- grammar
              let gp = makeTermParsers g
              rawJs <- concat <$> many (judgments gp)
              let (jmtsParsers,jmts) = unzip rawJs
              let premiseParser = choice (map try jmtsParsers) <?> "Judgment or Formula"
              js' <- mapM (fixRawRules premiseParser) jmts <?> "Fixing Rules"
              return $ (Language g js',premiseParser)


type Grammar = [NonTerm]
type Hom = (String,String)
data NonTerm = NonTerm [String] [RHS] [Hom]

instance Show NonTerm where
  show (NonTerm ns rhs homs) = concat (intersperse "," ns) ++ "->\n" ++
                               unlines ["\t" ++ show r | r <- rhs ]


data RHS = RHS [String] String [Hom]
instance Show RHS where
  show (RHS tokens nm homs) = unwords tokens ++ " :: " ++ nm

type Judgments a = [Judgment a]

data Judgment a = Judgment String String -- Name, prefix,
                  [String] -- Tokens
                  (Rules a)
                  [Hom]

instance Show a => Show (Judgment a) where
    show (Judgment n1 n2 tokens rules homs) = "Judgment " ++ n1 ++ " " ++ n2 ++ "\n" ++ unlines ((map show rules) ++ map show homs)

type Rules a = [Rule a]
data Rule a = Rule String -- Name
            [a] -- Premises
            AST -- Conclusion
            deriving Show
judgments gp = do
  symbol "defns"
  n <- identifier
  doubleColon
  pfx <- prefix
  doubleColonEqual
  many (judgment gp)


judgment gp = do
  symbol "defn"
  tokens <- endWithDoubleColon
  junk <- endWithDoubleColon
  name <- identifier
  doubleColon
  let jp = makeJudgmentParser name tokens gp <?> ("Judgment " ++ name)
  pfx <- prefix
  homs <- many hom
  symbol "by"
  rules <- manyTill (rule jp <?> "Rule") (lookAhead (reserved "defn" <|> eof))
  return $ (jp,Judgment name pfx tokens rules homs)

rule jp = do
  hyp <- premises
  many1 (symbol "-") <?> "Rule Divider"
  doubleColon
  name <- identifier
  conclusion <- jp <?> "Rule Conclusion"
  whiteSpace
  return $ Rule name hyp conclusion


premises = (lookAhead (try divider) >> return []) <|>
           do l <- lineParser
              ls <- premises
              return (l:ls)
divider = do cs <- many1 (char '-') <?> "dash"
             guard (length cs > 3)
             return cs


lineParser = do pos <- getPosition
                cs <- manyTill anyChar (try newline) <* whiteSpace
                return (pos,cs)


anyterm = (operator <|> identifier) <?> "Any Term"


-- | Gather all of the non-terminals in a grammar.
nontermNames :: [NonTerm] -> S.Set String
nontermNames rules = S.fromList (concat [ns | NonTerm ns _ _ <- rules])


type Parser a = ParsecT String () Identity a
data AST = Leaf String |
           Node String [AST] | -- Constructor, Arguments
           MetaVar String String
         deriving Show

-- Take a grammar definition, and turn it into a bunch of parsers, one
-- for each nonterminal.
makeTermParsers :: Grammar -> M.Map String (Parser AST)
makeTermParsers g = parsers
  where parsers = M.fromList (concatMap parseNonterm g)
        nonterms = nontermNames g
        parseNonterm :: NonTerm -> [(String,Parser AST)]
        parseNonterm (NonTerm ns rhss _) = let p = choice $ (map metavar ns) ++ (map parseRHS rhss)
                                         in [(n,p) | n <- ns]

        parseRHS :: RHS -> Parser AST
        parseRHS (RHS tokens cons _) = Node cons <$> sequence (map parseToken tokens)
        parseToken :: String -> Parser AST
        parseToken t
          | t `S.member` nonterms = let ~(Just p) = M.lookup t parsers in p
          | otherwise = Leaf <$> symbol t

metavar nm = do symbol nm
                suffix <- many (digit <|> char '\'')
                return $ MetaVar nm suffix


makeJudgmentParser :: String -> [String] -> M.Map String (Parser AST) -> Parser AST
makeJudgmentParser name tokens termParsers  = Node name <$> mapM mkTokenParser tokens
  where mkTokenParser token
          | Just nt <- M.lookup (stripSuffix token) termParsers = nt
          | otherwise = Leaf <$> symbol token
        stripSuffix t =
          -- FIXME: This doesn't accurately capture metavar syntax
          case partition isAlpha t of
            ([],_) -> t
            (p,_) -> p


fixRawRules :: Parser AST -> Judgment (SourcePos,String) -> Parser (Judgment AST)
fixRawRules parser (Judgment a b c rules homs) = do
  flip (Judgment a b c) homs  <$> mapM (fixRawRule parser) rules

fixRawRule :: Parser AST -> Rule (SourcePos,String) -> Parser (Rule AST)
fixRawRule parser (Rule nm premises conclusion) = do
  p <- getPosition
  let fixed = sequence [runP (setPosition pos >> parser) () "wtf" string |  (pos,string) <- premises]
  case fixed of
    Left err -> fail ""
    Right good ->  setPosition p >> return (Rule nm good conclusion)



parseGrammar fname = do
  f <- readFile fname
  case runIdentity (runPT (whiteSpace *> language <* eof) () fname f) of
    Left err ->  fail (show err)
    Right (Language grammar judgments,parser) -> return $ (grammar, judgments, parser)


-- Printing


run p s = runIndent "<test>" (runPT (whiteSpace *> p <* whiteSpace <* eof) () "<test>" s)
test  = unlines [
  "grammar",
  "t :: '_foo' ::=  {{com What is this }}",
  "\t| a t :: :: App",
  "\t| b v :: :: App",
  "v :: '_foo' ::=  {{com What is this }}",
  "\t| x  :: :: App"

  ]
