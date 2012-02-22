{-# LANGUAGE NoMonomorphismRestriction, TransformListComp #-}
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
import Data.List(partition,intersperse,groupBy,sortBy,elemIndex)
import Data.Char(isAlpha,isAlphaNum,toUpper)
import Data.Maybe(fromJust)
import qualified  Text.PrettyPrint as PP
import Text.PrettyPrint(text,(<+>),hang,(<>),punctuate,vcat,hcat,hsep)
import qualified Data.Text as T

import GHC.Exts(the,groupWith)
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
symbol i = (Token.symbol tokenizer i) <?> ("Literal Symbol: " ++ i)
operator = Token.operator tokenizer
whiteSpace = Token.whiteSpace tokenizer

doubleColon = reservedOp "::"
doubleColonEqual = reservedOp "::="
-- This isn't right, it doesn't handle spacing right around the quotes
prefix = between  (char '\'') (char '\'') (many (alphaNum <|> char '_')) <* whiteSpace

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
  opts <- manyTill (symbol "S" <|> symbol "M") (try (reservedOp "::"))
  constructor <- identifier <?> "Constructor name" -- Should check
                 -- this begins uppercase
  binds <- many bind
  homs <- many hom
  return $ RHS tokens constructor homs opts

data Language a = Language Grammar (Judgments a)

language = do g <- grammar
              let gp = makeTermParsers g
              rawJs <- concat <$> many (judgments gp)
              let (jmtsParsers,jmts) = unzip rawJs
              let premiseParser = choice (map try jmtsParsers) <?> "Judgment or Formula"
              js' <- mapM (fixRawRules premiseParser) jmts <?> "Fixing Rules"
              return $ (Language g js', premiseParser)


type Grammar = [NonTerm]
type Hom = (String,String)
data NonTerm = NonTerm [String] [RHS] [Hom]

instance Show NonTerm where
  show (NonTerm ns rhs homs) = concat (intersperse "," ns) ++ "->\n" ++
                               unlines ["\t" ++ show r | r <- rhs ]


data RHS = RHS [String] String [Hom] [String]
instance Show RHS where
  show (RHS tokens nm homs _) = unwords tokens ++ " :: " ++ nm ++ (concat $ map show homs)

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
           Node String String [AST] | -- Constructor, Type, Arguments
           MetaVar String String
         deriving Show



-- Take a grammar definition, and turn it into a bunch of parsers, one
-- for each nonterminal.
makeTermParsers :: Grammar -> M.Map String (Parser AST)
makeTermParsers g = parsers
  where parsers = M.fromList (concatMap parseNonterm g)
        nonterms = nontermNames g


        -- Build a parser for a particular non-terminal
        parseNonterm :: NonTerm -> [(String,Parser AST)]
        parseNonterm (NonTerm ns rhss _) =
          let isLeftRecursive (RHS (e:es) _ _ _) = (stripMeta e) `elem` ns
              isLeftRecursive r = error $ show r
              (rec,base) = partition isLeftRecursive rhss
              rec' = [RHS es b r meta | RHS (e:es) b r meta <- rec]
              -- Whole lot of try's required here. Left-factoring the
              -- grammar should eliminate those.
              baseParser = choice $ map metavar ns ++
                           [try $ parseRHS (head ns) r | r <- base]
              restParser = choice [try $ parseRHS' (head ns) r | r <- rec']
              p = do hd <- baseParser
                     rest <- many restParser
                     return $ foldl (\l r -> r l) hd rest
          in  [(n,p) | n <- ns]


        parseRHS ::  String -> RHS -> Parser AST
        parseRHS ty (RHS tokens cons _ _) =
          Node cons ty <$> sequence (map parseToken tokens)

        parseRHS' :: String -> RHS -> Parser (AST -> AST)
        parseRHS' ty (RHS tokens cons _ _) = do
          args <- sequence (map parseToken tokens)
          return $ \arg -> Node cons ty (arg:args)

        parseToken :: String -> Parser AST
        parseToken t
          | (stripMeta t) `S.member` nonterms =
            let ~(Just p) = M.lookup (stripMeta t) parsers in (p <?> "nonterminal: " ++ stripMeta t)
          | otherwise = Leaf <$> symbol t

        -- Remove the metavariable indices. FIXME: This is temporary,
        -- until we handle index variables properly.
        stripMeta t = let t'= takeWhile isAlpha t
                      in if t' `S.member` nonterms then t' else t

metavar nm = try $ do
  symbol nm
  suffix <- many (digit <|> char '\'')
  whiteSpace
  return $ MetaVar nm suffix


makeJudgmentParser :: String -> [String] -> M.Map String (Parser AST) -> Parser AST
makeJudgmentParser name tokens termParsers  = Node name "judgment" <$> mapM mkTokenParser tokens
  where mkTokenParser token
          | Just nt <- M.lookup (stripSuffix token) termParsers = nt
          | otherwise = Leaf <$> symbol token
        stripSuffix t =
          -- FIXME: This doesn't accurately capture metavar syntax
          case partition isAlpha t of
            ([],_) -> t
            (p,_) -> p

-- Given a bunch of judgments with unparsed premises, run the
-- judgments parser on each premisew.
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
    Right (Language grammar judgments,parser) -> do
      let homs = homGrammar grammar
          pprint htype = applyHom homs htype
      return $ (grammar, judgments, makeTermParsers grammar,pprint)


-- Printing


run p s = runIndent "<test>" (runPT (whiteSpace *> p <* whiteSpace <* eof) () "<test>" s)
run' p s =
  case runIdentity (runPT (whiteSpace *> p <* whiteSpace <* eof) () "<test>" s) of
    Left err -> error $ show err
    Right val -> return val
test  = unlines [
  "grammar",
  "t :: '_foo' ::=  {{com What is this }}",
  "\t| a t :: :: App",
  "\t| b v :: :: App",
  "v :: '_foo' ::=  {{com What is this }}",
  "\t| x  :: :: App"

  ]

anotherTest = do
  (g,js,ps,pprint)  <- parseGrammar "sep.ott"
  let Just p = M.lookup "P" ps
  r <- run' p "(\\ L x : A' .\\ L x1 : A. P1 )"
  print $ pprint "tex" r

{-

data Factored = FLeaf RHS
              | FCommon String Factored
              | FAlt [Factored] deriving Show


-- factor :: NonTerm -> [NonTerm]
norec nt@(NonTerm ns rhs homs) = (removed, simple)
  where isLeftRecursive (RHS (e:es) _ [] _) = e `elem` ns
        (rec,base) = partition isLeftRecursive rhs
        simple = NonTerm (map (++ "_term") ns) base homs
        removed = NonTerm ns
                  [RHS ((n ++ "_term"):es) nm hom meta | RHS (e:es) nm hom meta <- rec, n <- ns] []

factorNT (NonTerm ns rhs _) = (ns,factor rhs)



factor [r] = FLeaf r
factor rhs = FAlt (map mkNode rest)
  where groupHead (RHS (x:xs) _ _ _) (RHS (y:ys) _ _ _) = x == y
        groupHead _ _ = False
        ruleHead (RHS (x:_) _ _ _) = x
        ruleTail (RHS (_:xs) a b c) = RHS xs a b c
        compareHead (RHS (x:xs) _ _ _) (RHS (y:ys) _ _ _) = compare x y
        mkNode (n,[r]) = FLeaf r
        mkNode (n,ts) = FCommon n (factor (map ruleTail ts))
        rest = [ (head (head tokens), rule) | rule@(RHS tokens _ _ _) <- rhs, then group by (head tokens) using groupWith]

parseRHS :: [AST] -> RHS -> Parser AST
parseRHS accum (RHS tokens cons _ _) = do
  args <- sequence (map parseToken tokens)
  return (Node cons (accum ++ args))

parseToken t = Leaf <$> symbol t

parseFactored :: [AST] -> Factored -> Parser AST
parseFactored accum (FLeaf rhs) = parseRHS accum rhs
parseFactored accum (FCommon t rest) = do
  tast <- parseToken t
  parseFactored (accum ++ [tast]) rest
parseFactored accum (FAlt fs) = choice (map (parseFactored accum) fs)

-}

-- * Hom support
homGrammar g =
  [((cty,cname),rhsHom rule) | NonTerm (cty:ns) rhss _ <- g,
   rule@(RHS tokens cname homs _) <- rhss
   ]
applyHom _ _ n@(MetaVar t "'") = text t <> text "'"
applyHom _ _ n@(MetaVar t "") = text t
applyHom _ _ n@(MetaVar t s) = text t <> text "_" <> PP.braces (text s)
applyHom _ _ (Leaf s) = text s
applyHom table htype n@(Node cname tname args) =
  case lookup htype homs of
    Just hom -> subHom hom
    Nothing -> hsep $ map (applyHom table htype) args
  where Just homs = lookup (tname,cname) table
        subHom ((HomLit s):rest) = text s <> subHom rest
        subHom ((HomVar i):rest) =
          applyHom table htype (args !! i) <> subHom rest
        subHom [] = PP.empty


rhsHom (RHS tokens cnm homs _) = parsedHoms
  -- Build a map from metavar to list position
  where
    parsedHoms = [(n,locHoms $ parseHom (T.pack h)) | (n,h) <- homs]
    locHoms [] = []
    locHoms ((HomLit s):hs) = HomLit s:locHoms hs
    locHoms ((HomVar n):hs) = let Just loc = elemIndex n tokens
                              in HomVar loc:locHoms hs


data HomSpec a = HomLit String | HomVar a deriving Show

parseHom str = s1 str
  where s1 s =
          case T.breakOn (T.pack "[[") s of
            (start,rest)
              | T.null rest -> [HomLit (T.unpack start)]
              | otherwise -> HomLit (T.unpack start):(st2 (T.drop 2 rest))
        st2 s =
          case T.breakOn (T.pack "]]") s of
            (start,rest)
              | T.null start -> [HomLit $ "[[" ++ (T.unpack s)]
              | otherwise ->
                   (HomVar (T.unpack (T.strip start))):s1 (T.drop 2 rest)


-- * Generate Haskell Datatypes
toHask  g = PP.cat $ map toData g
  where nonterms = S.fromList [n | NonTerm ns rhs homs <- g, n <- ns]
        ucase (n:ns) = toUpper n:ns
        toData (NonTerm (n:ns) rhs _) =
          hang (text "data" <+> (text $ ucase n) <+> text "=") 2
            (vcat $ punctuate (text "|") [toCons r (typeName n) | r <- rhs, notMeta r])

        toCons (RHS tokens nm _  []) ty =
          constructor nm ty <+>
          hsep [text $ typeName (stripMeta t) | t <- tokens,
                   stripMeta t `S.member` nonterms]

        typeNames = M.fromList [(from,ucase to) | NonTerm nms@(to:ns) _ _ <- g, from <- nms]
        typeName t = let (Just nm) = M.lookup t typeNames in nm
        stripMeta t = let t'= takeWhile isAlpha t
                      in if t' `S.member` nonterms then t' else t
        notMeta (RHS _ _ _ []) = True
        notMeta _ = False
        -- If a constructor appears in more than one type then we have
        -- to do something to make it unique. We just prepend the name
        -- of the constructor.
        constructors :: [(String,Int)]
        constructors = [(the (map ucase cname),length cname) | NonTerm _ rhss _ <- g,
                        RHS _ cname _ _ <- rhss,
                        then group by (ucase cname) using groupWith]
        constructor n ty
          | Just i <- lookup (ucase n) constructors, i > 1 =
              text ty <> text "_" <> text (ucase n)
          | otherwise = text (ucase n)
