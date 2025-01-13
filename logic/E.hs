-- myparser.hs

{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Data.Maybe
import Data.Set
import Data.List
import Data.Char
import Control.Applicative

--Tools--
showListOf :: [Expr] -> String
showListOf [] = ""
showListOf [h] = show h
showListOf (h:t) = show h ++ "," ++ showListOf t 


{-

S ::= E

E ::= D E'

E' ::= -> D E'
      | <eps>

D ::= C D'

D' ::= | C D'
      | <eps>

C ::= I C'

C' ::= & I C'
      | <eps>

I ::= ! I
      | ( E )
      | @ <var> . E
      | ? <var> . E
      | P

P ::= <pvar> PA

PA ::= '(' A ')'
      | <eps>

A ::= T T' 
      | <eps>

T ::= '(' T ')'
       | <var> PA

T' ::= ',' T T'
       | <eps>

-}

data Expr
  = E_Var String
  | Expr :| Expr
  | Expr :& Expr
  | Expr :-> Expr
  | E_Inverse Expr
  | Forall Expr Expr
  | Exists Expr Expr
  | Term String [Expr]
  | Predicate String [Expr]
  deriving Eq

instance Show Expr where
    show = \case
      E_Var s -> id s
      lhs :|  rhs -> "(" ++ show lhs ++ "|" ++ show rhs ++ ")"
      lhs :&  rhs -> "(" ++ show lhs ++ "&" ++ show rhs ++ ")"
      lhs :-> rhs -> "(" ++ show lhs ++ "->" ++ show rhs ++ ")"
      E_Inverse e -> "(!" ++ show e ++ ")"
      Forall var e -> "(@" ++ show var ++ "." ++ show e ++ ")"
      Exists var e -> "(?" ++ show var ++ "." ++ show e ++ ")"
      Term name vars      -> id name ++ "(" ++ showListOf vars ++ ")"
      Predicate name vars -> id name ++ "(" ++ showListOf vars ++ ")"

data Token 
    = T_Var String
    | T_Pred String
    | T_Disj
    | T_Conj
    | T_Impl
    | T_Inverse
    | T_COMMA
    | T_POINT
    | T_FORALL
    | T_EXISTS
    | T_LPAR
    | T_RPAR
    | T_HALT_
    deriving (Eq, Show)

isUCAlpha :: Char -> Bool
isUCAlpha c = ord 'A' <= ord c && ord c <= ord 'Z'

isLCAlpha :: Char -> Bool
isLCAlpha c = ord 'a' <= ord c && ord c <= ord 'z'

isVarSymbol :: Char -> Bool
isVarSymbol c = isLCAlpha c || isDigit c

isPredSymbol :: Char -> Bool
isPredSymbol c = isUCAlpha c || isDigit c

tokenize :: String -> [Token]
tokenize [] = []
tokenize (',' : rest)       = T_COMMA   : tokenize rest
tokenize ('.' : rest)       = T_POINT   : tokenize rest
tokenize ('@' : rest)       = T_FORALL  : tokenize rest
tokenize ('?' : rest)       = T_EXISTS  : tokenize rest
tokenize ('|' : rest)       = T_Disj    : tokenize rest
tokenize ('&' : rest)       = T_Conj    : tokenize rest
tokenize ('-' : '>' : rest) = T_Impl    : tokenize rest
tokenize ('!' : rest)       = T_Inverse : tokenize rest
tokenize ('(' : rest)       = T_LPAR    : tokenize rest
tokenize (')' : rest)       = T_RPAR    : tokenize rest
tokenize s@(h : _)
    | isSpace h   = let(spaces, rest)     = span isSpace     s
                    in tokenize rest     
    | isUCAlpha h = let(varSymbols, rest) = span isPredSymbol s
                    in T_Pred varSymbols : tokenize rest
    | isLCAlpha h = let(varSymbols, rest) = span isVarSymbol s
                    in T_Var varSymbols : tokenize rest
tokenize _ = [T_HALT_]


newtype Parser s a = Parser { runParser :: [s] -> Maybe (a, [s]) }

instance Functor (Parser s) where
    fmap f (Parser p) = Parser $ \ss -> case p ss of
        Nothing -> Nothing
        Just (x, ss') -> Just (f x, ss')

instance Applicative (Parser s) where
    pure x = Parser $ \ss -> Just (x, ss)

    Parser pf <*> Parser px = Parser $ \ss -> case pf ss of
        Nothing -> Nothing
        Just (f, ss') -> case px ss' of
            Nothing -> Nothing
            Just (x, ss'') -> Just (f x, ss'')

instance Monad (Parser s) where
    Parser p >>= f = Parser $ \ss -> case p ss of
        Nothing -> Nothing
        Just (x, ss') -> runParser (f x) ss'

instance Alternative (Parser s) where
    empty = Parser $ const Nothing

    Parser p1 <|> Parser p2 = Parser $ \ss -> case p1 ss of
        Nothing -> p2 ss
        def -> def

instance MonadFail (Parser s) where
    fail _ = Control.Applicative.empty

ok :: Parser s ()
ok = pure ()

eof :: Parser s ()
eof = Parser $ \case
  [] -> Just ((), [])
  _ -> Nothing

pHead :: Parser s s
pHead = Parser $ \case
  [] -> Nothing
  (s : ss') -> Just (s, ss')

satisfies :: (s -> Bool) -> Parser s s
satisfies predicate = Parser $ \case
  [] -> Nothing
  (s : ss') -> if predicate s then Just (s, ss') else Nothing

element :: Eq s => s -> Parser s s
element s = satisfies (== s)

stream :: Eq s => [s] -> Parser s [s]
stream [] = pure []
stream (s : ss') = element s >>= \ps -> stream ss' >>= \pss' -> pure (ps : pss')

parseE :: Parser Token Expr
parseE     = (do d <- parseD
                 element T_Impl
                 e <- parseE
                 pure (d :-> e)) <|>
              parseD

parseD :: Parser Token Expr
parseD = parseC >>= parseD'

parseD' :: Expr -> Parser Token Expr
parseD' acc = (do element T_Disj
                  c <- parseC
                  parseD' (acc :| c)) <|>
              pure acc 

parseC :: Parser Token Expr
parseC = parseI >>= parseC'

parseC' :: Expr -> Parser Token Expr
parseC' acc = (do element T_Conj
                  i <- parseI
                  parseC' (acc :& i)) <|>
              pure acc 

parseI :: Parser Token Expr
parseI = (do element T_Inverse
             E_Inverse <$> parseI) <|>
         (do element T_LPAR
             e <- parseE
             element T_RPAR
             pure e) <|>
         (do element T_FORALL
             T_Var s <- satisfies (\case { T_Var _ -> True; _ -> False })
             element T_POINT
             e <- parseE
             pure (Forall (E_Var s) e)) <|>
         (do element T_EXISTS
             T_Var s <- satisfies (\case { T_Var _ -> True; _ -> False })
             element T_POINT
             e <- parseE
             pure (Exists (E_Var s) e)) <|>
         (do p <- parseP
             pure p)

parseP :: Parser Token Expr
parseP = (do T_Pred s <- satisfies (\case { T_Pred _ -> True; _ -> False })
             args <- parsePA
             pure (Predicate s args))

parsePA :: Parser Token [Expr]
parsePA = (do element T_LPAR
              args <- parseA
              element T_RPAR
              pure args) <|>
          pure []

parseTA :: Parser Token (Maybe [Expr])
parseTA = (do element T_LPAR
              args <- parseA
              element T_RPAR
              pure $ Just args) <|>
          pure Nothing

parseA :: Parser Token [Expr]
parseA = (do t <- parseT
             t' <- parseT'
             pure (t : t')) <|>
         pure []

parseT :: Parser Token Expr
parseT = (do element T_LPAR
             t <- parseT
             element T_RPAR
             pure t) <|>
         (do T_Var s <- satisfies (\case { T_Var _ -> True; _ -> False })
             args <- parseTA
             if args == Nothing then pure (E_Var s)
             else pure $ Term s (fromJust $ args))

parseT' :: Parser Token [Expr]
parseT' = (do element T_COMMA
              t <- parseT
              t' <- parseT'
              pure (t : t')) <|>
          pure []

parseExpr :: String -> Maybe Expr
parseExpr s = fst <$> runParser (parseE <* eof) (tokenize s)

data KindOfExpr 
  = Change (Maybe Expr) (Maybe Expr) -- free, unfree
  | Else
  deriving Show

data TypeByScheme
  = Axiom Expr
  | Similar Expr
  | Unknown
  deriving Show

getType :: String -> KindOfExpr -> TypeByScheme
getType var Else = Unknown
getType var (Change (Just f) (Just u)) = if u == f
                                         then Similar u
                                         else Unknown
getType var (Change Nothing (Just u))  = Similar u
getType var (Change (Just f) Nothing)  = Axiom f
getType var (Change Nothing Nothing)   = Axiom (E_Var var)

(<&>) :: KindOfExpr -> KindOfExpr -> KindOfExpr
(<&>) (Else) _ = Else
(<&>) _ (Else) = Else
(<&>) (Change (Just f) (Just u)) (Change (Just f2) (Just u2)) = if f == f2 && u == u2 then (Change (Just f) (Just u)) else Else
(<&>) (Change (Just f) (Just u)) (Change (Just f2) Nothing)   = if f == f2 then (Change (Just f) (Just u)) else Else
(<&>) (Change (Just f) (Just u)) (Change Nothing (Just u2))   = if u == u2 then (Change (Just f) (Just u)) else Else
(<&>) (Change (Just f) (Just u)) (Change Nothing Nothing)     = (Change (Just f) (Just u))
(<&>) (Change (Just f) Nothing) (Change (Just f2) (Just u2))  = if f == f2 then (Change (Just f) (Just u2)) else Else
(<&>) (Change (Just f) Nothing) (Change (Just f2) Nothing)    = if f == f2 then (Change (Just f) Nothing) else Else
(<&>) (Change (Just f) Nothing) (Change Nothing (Just u2))    = (Change (Just f) (Just u2)) 
(<&>) (Change (Just f) Nothing) (Change Nothing Nothing)      = (Change (Just f) Nothing)
(<&>) (Change Nothing (Just u)) (Change (Just f2) (Just u2))  = if u == u2 then (Change (Just f2) (Just u)) else Else
(<&>) (Change Nothing (Just u)) (Change (Just f2) Nothing)    = (Change (Just f2) (Just u)) 
(<&>) (Change Nothing (Just u)) (Change Nothing (Just u2))    = if u == u2 then (Change Nothing (Just u)) else Else
(<&>) (Change Nothing (Just u)) (Change Nothing Nothing)      = (Change Nothing (Just u))
(<&>) (Change Nothing Nothing) (Change (Just f2) (Just u2))   = (Change (Just f2) (Just u2))
(<&>) (Change Nothing Nothing) (Change (Just f2) Nothing)     = (Change (Just f2) Nothing)
(<&>) (Change Nothing Nothing) (Change Nothing (Just u2))     = (Change Nothing (Just u2))
(<&>) (Change Nothing Nothing) (Change Nothing Nothing)       = (Change Nothing Nothing)

acceptTerms :: [Expr] -> Set String -> Bool
acceptTerms [] vars = True
acceptTerms (h : t) vars = (acceptTerm h vars) && (acceptTerms t vars)

acceptTerm :: Expr -> Set String -> Bool
acceptTerm (E_Var s)      vars = if Data.Set.member s vars then False else True
acceptTerm (Term name le) vars = acceptTerms le vars

getThetaTerms :: [Expr] -> String -> [Expr] -> Set String -> KindOfExpr
getThetaTerms [] _ [] _ = Change Nothing Nothing
getThetaTerms _  _ [] _ = Else
getThetaTerms [] _ _  _ = Else
getThetaTerms (sh : st) var (eh : et) underVar = (getTheta sh var eh underVar) <&> (getThetaTerms st var et underVar)

getTheta :: Expr -> String -> Expr -> Set String -> KindOfExpr
getTheta (sl :| sr)         var (el :| er)         underVar = (getTheta sl var el underVar) <&> (getTheta sr var er underVar)
getTheta (sl :& sr)         var (el :& er)         underVar = (getTheta sl var el underVar) <&> (getTheta sr var er underVar)
getTheta (sl :-> sr)        var (el :-> er)        underVar = (getTheta sl var el underVar) <&> (getTheta sr var er underVar)
getTheta (E_Inverse sch)    var (E_Inverse e)      underVar = getTheta sch var e underVar
getTheta (Forall (E_Var sv) se) var (Forall (E_Var ev) ee) underVar = if sv == ev 
                                                                      then getTheta se var ee (Data.Set.insert sv underVar)
                                                                      else Else
getTheta (Exists (E_Var sv) se) var (Exists (E_Var ev) ee) underVar = if sv == ev 
                                                                      then getTheta se var ee (Data.Set.insert sv underVar)
                                                                      else Else
getTheta (Predicate sv sle) var (Predicate ev ele) underVar = if sv == ev 
                                                              then getThetaTerms sle var ele underVar
                                                              else Else
getTheta (Term sv sle)      var (Term ev ele)      underVar = if sv == ev
                                                              then getThetaTerms sle var ele underVar
                                                              else Else
                                                              -- если связаны х-ом, и при этом подставляем х, то ничего
getTheta (E_Var s)          var e                  underVar = if s == var
                                                              then if Data.Set.member var underVar
                                                                   then if E_Var var == e 
                                                                        then Change Nothing Nothing
                                                                        else Else
                                                                   else if acceptTerm e underVar -- free
                                                                        then Change (Just e) Nothing
                                                                        else Change Nothing (Just e)
                                                              else if (E_Var s == e) 
                                                                   then Change Nothing Nothing
                                                                   else Else
getTheta _ _ _ _ = Else

--Если х связан, то должен быть х
--Если х не связан, и терм свободен, то лево
--Если х не связан, и терм не свободен, то право

axiom11 :: Expr -> Maybe (Expr, Expr, Expr)
axiom11 ((Forall (E_Var var) phi) :-> r) = case (getType var $ getTheta phi var r Data.Set.empty) of
                                             (Axiom theta) -> Just (phi, (E_Var var), theta)
                                             _ -> Nothing
axiom11 _ = Nothing

axiom12 :: Expr -> Maybe (Expr, Expr, Expr)
axiom12 (l :-> (Exists (E_Var var) phi)) = case (getType var $ getTheta phi var l Data.Set.empty) of
                                             (Axiom theta) -> Just (phi, (E_Var var), theta)
                                             _ -> Nothing
axiom12 _ = Nothing

similar11 :: Expr -> Maybe (Expr, Expr, Expr)
similar11 ((Forall (E_Var var) phi) :-> r) = case (getType var $ getTheta phi var r Data.Set.empty) of
                                               (Similar theta) -> Just (phi, (E_Var var), theta)
                                               _ -> Nothing
similar11 _ = Nothing

similar12 :: Expr -> Maybe (Expr, Expr, Expr)
similar12 (l :-> (Exists (E_Var var) phi)) = case (getType var $ getTheta phi var l Data.Set.empty) of
                                               (Similar theta) -> Just (phi, (E_Var var), theta)
                                               _ -> Nothing
similar12 _ = Nothing

check ((Forall (E_Var var) phi) :-> r) = getTheta phi var r Data.Set.empty

answer :: Expr -> String
answer e = case axiom11 e of
             (Just (phi, x, theta)) -> "Axiom scheme 11, phi = " ++ show phi ++ ", x = " ++ show x ++ ", theta = " ++ show theta
             Nothing -> case axiom12 e of
                         (Just (phi, x, theta)) -> "Axiom scheme 12, phi = " ++ show phi ++ ", x = " ++ show x ++ ", theta = " ++ show theta
                         Nothing -> case similar11 e of
                                     (Just (phi, x, theta)) -> "Similar to axiom scheme 11, phi = " ++ show phi ++ ", x = " ++ show x ++ ", theta = " ++ show theta
                                     Nothing -> case similar12 e of
                                                 (Just (phi, x, theta)) -> "Similar to axiom scheme 12, phi = " ++ show phi ++ ", x = " ++ show x ++ ", theta = " ++ show theta
                                                 Nothing -> "Not an axiom scheme 11 or 12"

main = do
    s <- getLine
    putStrLn $ answer $ fromJust $ parseExpr s