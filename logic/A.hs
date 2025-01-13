-- myparser.hs

{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Data.List
import Data.Char
import Control.Applicative

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
      | <Var>

-}

data Expr
  = E_Var String
  | Expr :| Expr
  | Expr :& Expr
  | Expr :-> Expr
  | E_Inverse Expr
  deriving Eq

instance Show Expr where
    show = \case
      E_Var s -> id s
      lhs :|  rhs -> "(|," ++ show lhs ++ "," ++ show rhs ++ ")"
      lhs :&  rhs -> "(&," ++ show lhs ++ "," ++ show rhs ++ ")"
      lhs :-> rhs -> "(->," ++ show lhs ++ "," ++ show rhs ++ ")"
      E_Inverse e -> "(!" ++ show e ++ ")"

data Token 
    = T_Var String
    | T_Disj
    | T_Conj
    | T_Impl
    | T_Inverse
    | T_LPAR
    | T_RPAR
    | T_HALT_
    deriving (Eq, Show)

isUCAlpha :: Char -> Bool
isUCAlpha c = ord 'A' <= ord c && ord c <= ord 'Z'

isVarSymbol :: Char -> Bool
isVarSymbol c = isUCAlpha c || isDigit c || c == '\0039'

tokenize :: String -> [Token]
tokenize [] = []
tokenize ('|' : rest)       = T_Disj    : tokenize rest
tokenize ('&' : rest)       = T_Conj    : tokenize rest
tokenize ('-' : '>' : rest) = T_Impl    : tokenize rest
tokenize ('!' : rest)       = T_Inverse : tokenize rest
tokenize ('(' : rest)       = T_LPAR    : tokenize rest
tokenize (')' : rest)       = T_RPAR    : tokenize rest
tokenize s@(h : _)
    | isSpace h   = let(spaces, rest)     = span isSpace     s
                    in tokenize rest     
    | isUCAlpha h = let(varSymbols, rest) = span isVarSymbol s
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
    fail _ = empty

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

--parseE :: Parser Token Expr
--parseE = parseD >>= parseE'

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
         (do T_Var s <- satisfies (\case { T_Var _ -> True; _ -> False })
             pure (E_Var s))

parseExpr :: String -> Maybe Expr
parseExpr s = fst <$> runParser (parseE <* eof) (tokenize s)

maybeExprToStr :: Maybe Expr -> String
maybeExprToStr Nothing = ""
maybeExprToStr (Just val) = show val

main = do
    s <- getLine
    putStrLn $ maybeExprToStr $ parseExpr s