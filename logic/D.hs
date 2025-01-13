-- myparser.hs

{-# LANGUAGE LambdaCase #-}

module Main where

import Data.Maybe
import Data.Set
import Data.Map
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

I ::= _|_
      | ( E )
      | <Var>

-}

data Expr
  = E_Var String
  | Expr :| Expr
  | Expr :& Expr
  | Expr :-> Expr
  | E_Bottom
  deriving (Eq, Ord)

instance Show Expr where
    show = \case
      E_Var s -> id s
      lhs :|  rhs -> "(" ++ show lhs ++ "|" ++ show rhs ++ ")"
      lhs :&  rhs -> "(" ++ show lhs ++ "&" ++ show rhs ++ ")"
      lhs :-> rhs -> "(" ++ show lhs ++ "->" ++ show rhs ++ ")"
      E_Bottom -> "_|_"

data Token 
    = T_Var String
    | T_Disj
    | T_Conj
    | T_Impl
    | T_Bottom
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
tokenize ('_' : '|' : '_' : rest) = T_Bottom : tokenize rest
tokenize ('|' : rest)       = T_Disj    : tokenize rest
tokenize ('&' : rest)       = T_Conj    : tokenize rest
tokenize ('-' : '>' : rest) = T_Impl    : tokenize rest
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
parseI = (do element T_Bottom
             pure E_Bottom) <|>
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

-- Nature tree --

type Context = [Expr]  

(<+>) :: Context -> Expr -> Context
(<+>) c e = c ++ [e]
            {-if Data.Map.member e c 
            then adjust ((+) 1) e c
            else Data.Map.insert e 1 c-}

data Message = Message Context Expr

getContext :: Message -> Context
getContext (Message c e) = c

getMainExpr :: Message -> Expr
getMainExpr (Message c e) = e

showListOf :: [Expr] -> String
showListOf [] = ""
showListOf [h] = show h
showListOf (h:t) = show h ++ "," ++ showListOf t 

--TODO: fix show

instance Show Message where
    show (Message le e) = (showListOf le) ++ "|-" ++ show e

data Node
  = E_N_N   Message Node -- TO FROM
  | E_Or    Message Node Node Node --TO L R L|R 
  | I_R_Or  Message Node 
  | I_L_Or  Message Node 
  | E_R_And Message Node 
  | E_L_And Message Node 
  | I_And   Message Node Node
  | I_Impl  Message Node 
  | E_Impl  Message Node Node
  | Ax      Message

showWithNum :: Int -> Node -> String
showWithNum num (Ax msg) = "[" ++ show num ++ "] " ++ show msg ++ " [Ax]\n"
showWithNum num (E_N_N   msg node1) = showWithNum (num+1) node1 ++
                                      "[" ++ show num ++ "] " ++ show msg ++ " [E!!]\n"
showWithNum num (E_Or    msg node1 node2 node3) = showWithNum (num+1) node1 ++
                                                  showWithNum (num+1) node2 ++
                                                  showWithNum (num+1) node3 ++
                                      "[" ++ show num ++ "] " ++ show msg ++ " [E|]\n"
showWithNum num (I_R_Or  msg node1) = showWithNum (num+1) node1 ++
                                      "[" ++ show num ++ "] " ++ show msg ++ " [Ir|]\n"
showWithNum num (I_L_Or  msg node1) = showWithNum (num+1) node1 ++
                                      "[" ++ show num ++ "] " ++ show msg ++ " [Il|]\n"
showWithNum num (E_R_And msg node1) = showWithNum (num+1) node1 ++
                                      "[" ++ show num ++ "] " ++ show msg ++ " [Er&]\n"
showWithNum num (E_L_And msg node1) = showWithNum (num+1) node1 ++
                                      "[" ++ show num ++ "] " ++ show msg ++ " [El&]\n"
showWithNum num (I_And   msg node1 node2) = showWithNum (num+1) node1 ++
                                            showWithNum (num+1) node2 ++
                                      "[" ++ show num ++ "] " ++ show msg ++ " [I&]\n"
showWithNum num (I_Impl  msg node1) = showWithNum (num+1) node1 ++
                                      "[" ++ show num ++ "] " ++ show msg ++ " [I->]\n"
showWithNum num (E_Impl  msg node1 node2) = showWithNum (num+1) node1 ++
                                            showWithNum (num+1) node2 ++
                                      "[" ++ show num ++ "] " ++ show msg ++ " [E->]\n"

instance Show Node where
    show n = showWithNum 0 n

--rating--

type Rate = Map String Bool

showRateVar :: (String, Bool) -> String
showRateVar (s, b) = s ++ ":=" ++ (if b then "T" else "F")

showRateList :: [(String, Bool)] -> String
showRateList [] = ""
showRateList [a] = showRateVar a
showRateList l = (showRateVar $ head l) ++ "," ++ (showRateList $ tail l)

showRate :: Rate -> String
showRate rate = showRateList $ Data.Map.assocs rate

getSetOfVars :: Expr -> Set String
getSetOfVars (E_Var s) = Data.Set.fromList [s]
getSetOfVars E_Bottom  = Data.Set.empty
getSetOfVars (l :& r)  = Data.Set.union (getSetOfVars l) (getSetOfVars r)
getSetOfVars (l :| r)  = Data.Set.union (getSetOfVars l) (getSetOfVars r)
getSetOfVars (l :-> r) = Data.Set.union (getSetOfVars l) (getSetOfVars r)

calcExpr :: Expr -> Rate -> Bool
calcExpr E_Bottom  _    = False
calcExpr (E_Var s) rate = fromJust $ Data.Map.lookup s rate
calcExpr (l :& r)  rate = (calcExpr l rate) && (calcExpr r rate)
calcExpr (l :| r)  rate = (calcExpr l rate) || (calcExpr r rate)
calcExpr (l :-> r) rate = (not $ calcExpr l rate) || (calcExpr r rate)

mergeToRate :: Rate -> [String] -> [Bool] -> Rate
mergeToRate acc [] [] = acc
mergeToRate acc l r =  mergeToRate (Data.Map.insert (head l) (head r) acc) (tail l) (tail r)

rateByVectors :: [String] -> [Bool] -> Rate
rateByVectors ls lb = mergeToRate Data.Map.empty ls lb

boolFrom01 :: Int -> Bool
boolFrom01 b = if b == 0 then False else True

pow :: Int -> Int -> Int -> Int -- for start: acc <- 1
pow acc a 0 = acc
pow acc a x = pow (acc * a) a (x - 1)

genVector :: Int -> Int -> [Bool]
genVector 0 _ = []
genVector len num = [boolFrom01 $ div num (pow 1 2 (len - 1))] ++ 
                    (genVector (len - 1) (mod num (pow 1 2 (len - 1))))

checkByNum :: Int -> [String] -> Expr -> Maybe [Bool]
checkByNum num varList e = if num == (pow 1 2 (length varList)) then Nothing
                           else if calcExpr e (rateByVectors varList (genVector (length varList) num)) 
                                then checkByNum (num + 1) varList e
                                else Just (genVector (length varList) num)

refutation :: Expr -> Maybe Rate
refutation e = (\s -> \b -> rateByVectors s b) (Data.Set.elems $ getSetOfVars e) <$> (checkByNum 0 (Data.Set.elems $ getSetOfVars e) e)

--proofing--
notThird :: Expr -> Expr
notThird phi = phi :| (phi :-> E_Bottom)

-- test: exclusionOfAnAssumption Data.Set.empty (E_Var "A") (E_Var "B") (Ax $ Message (Data.Set.singleton $ E_Var "A") (E_Var "B")) (Ax $ Message (Data.Set.singleton $ (E_Var "A") :-> E_Bottom) (E_Var "B"))
exclusionOfAnAssumption :: Context -> Expr -> Expr -> Node -> Node -> Node
exclusionOfAnAssumption gamma phi psi proofFromPhi proofFromNotPhi = -- let phi == A
  E_Or (Message gamma psi) -- Г|-psi
       proofFromPhi        -- Г,A|-psi
       proofFromNotPhi     -- Г,~A|-psi
       (E_N_N (Message gamma (notThird phi)) -- Г|- A|~A
              (E_Impl (Message (gamma <+> ((notThird phi) :-> E_Bottom)) E_Bottom) -- Г, ~(A|~A)|- _|_
                      (Ax (Message (gamma <+> ((notThird phi) :-> E_Bottom)) ((notThird phi) :-> E_Bottom))) -- Г,~(A|~A)|- ~(A|~A)
                      (I_R_Or (Message (gamma <+> ((notThird phi) :-> E_Bottom)) (notThird phi))  -- Г,~(A|~A)|- A|~A
                              (I_Impl (Message (gamma <+> ((notThird phi) :-> E_Bottom)) (phi :-> E_Bottom)) -- Г, ~(A|~A)|-~A
                                      (E_Impl (Message (gamma <+> ((notThird phi) :-> E_Bottom) <+> phi) E_Bottom) -- Г, ~(A|~A), A |- _|_
                                              (Ax (Message (gamma <+> ((notThird phi) :-> E_Bottom) <+> phi) ((notThird phi) :-> E_Bottom))) -- Г,~(A|~A), A|- ~(A|~A)
                                              (I_L_Or (Message (gamma <+> ((notThird phi) :-> E_Bottom) <+> phi) (notThird phi)) -- Г,~(A|~A), A|- A|~A
                                                      (Ax (Message (gamma <+> ((notThird phi) :-> E_Bottom) <+> phi) phi))       -- Г,~(A|~A), A|- A
                                              )
                                      )
                              )
                      )
              )
        )

emmy :: Node
emmy = Ax $ Message [] (E_Var "EMMY")

genProof :: Message -> Rate -> Node
genProof msg rate = case getMainExpr msg of
                      (E_Var s)                       -> (Ax msg)
                      ((E_Var s) :-> E_Bottom)        -> (Ax msg)
                      (E_Bottom :-> E_Bottom)         -> (I_Impl msg
                                                                 (Ax (Message (getContext msg <+> E_Bottom) E_Bottom))
                                                         )
                      (E_Bottom :-> a)                -> (I_Impl msg
                                                                 (E_N_N (Message (getContext msg <+> E_Bottom) a)
                                                                        (Ax (Message (getContext msg <+> E_Bottom <+> (a :-> E_Bottom)) E_Bottom))
                                                                 )
                                                         )
                      ((a :-> E_Bottom) :-> E_Bottom) -> (I_Impl msg
                                                                 (E_Impl (Message (getContext msg <+> (a :-> E_Bottom)) E_Bottom)
                                                                         (Ax (Message (getContext msg <+> (a :-> E_Bottom)) (a :-> E_Bottom)))
                                                                         (genProof (Message (getContext msg <+> (a :-> E_Bottom)) a) rate)
                                                                 )
                                                         )

                      ((a :& b) :-> E_Bottom)         -> if (calcExpr a rate)
                                                         then (I_Impl msg
                                                                      (E_Impl (Message (getContext msg <+> (a :& b)) E_Bottom)
                                                                              (genProof (Message (getContext msg <+> (a :& b)) (b :-> E_Bottom)) rate)
                                                                              (E_R_And (Message (getContext msg <+> (a :& b)) b)
                                                                                       (Ax (Message (getContext msg <+> (a :& b)) (a :& b)))
                                                                              )
                                                                      )
                                                              )
                                                         else (I_Impl msg
                                                                      (E_Impl (Message (getContext msg <+> (a :& b)) E_Bottom)
                                                                              (genProof (Message (getContext msg <+> (a :& b)) (a :-> E_Bottom)) rate)
                                                                              (E_L_And (Message (getContext msg <+> (a :& b)) a)
                                                                                       (Ax (Message (getContext msg <+> (a :& b)) (a :& b)))
                                                                              )
                                                                      )
                                                              )
                      (a :& b)                        -> (I_And msg
                                                                (genProof (Message (getContext msg) a) rate)
                                                                (genProof (Message (getContext msg) b) rate)
                                                         )

                      ((a :| b) :-> E_Bottom)         -> (I_Impl msg
                                                                 (E_Or (Message (getContext msg <+> (a :| b)) E_Bottom)
                                                                       (E_Impl (Message (getContext msg <+> (a :| b) <+> a) E_Bottom)
                                                                               (genProof (Message (getContext msg <+> (a :| b) <+> a) (a :-> E_Bottom)) rate)
                                                                               (Ax (Message (getContext msg <+> (a :| b) <+> a) a))
                                                                       )
                                                                       (E_Impl (Message (getContext msg <+> (a :| b) <+> b) E_Bottom)
                                                                               (genProof (Message (getContext msg <+> (a :| b) <+> b) (b :-> E_Bottom)) rate)
                                                                               (Ax (Message (getContext msg <+> (a :| b) <+> b) b))
                                                                       )
                                                                       (Ax (Message (getContext msg <+> (a :| b)) (a :| b)))
                                                                 )
                                                         )
                      (a :| b)                        -> if (calcExpr a rate)
                                                         then (I_L_Or msg
                                                                      (genProof (Message (getContext msg) a) rate)
                                                              )
                                                         else (I_R_Or msg
                                                                      (genProof (Message (getContext msg) b) rate)
                                                              )

                      ((a :-> b) :-> E_Bottom)        -> (I_Impl msg
                                                                 (E_Impl (Message (getContext msg <+> (a :-> b)) E_Bottom)
                                                                         (genProof (Message (getContext msg <+> (a :-> b)) (b :-> E_Bottom)) rate)
                                                                         (E_Impl (Message (getContext msg <+> (a :-> b)) b)
                                                                                 (Ax (Message (getContext msg <+> (a :-> b)) (a :-> b)))
                                                                                 (genProof (Message (getContext msg <+> (a :-> b)) a) rate)
                                                                         )
                                                                 )
                                                         )
                      (a :-> b)                       -> if (calcExpr b rate)
                                                         then (I_Impl msg
                                                                      (genProof (Message (getContext msg <+> a) b) rate)
                                                              )
                                                         else (I_Impl msg
                                                                      (E_Impl (Message (getContext msg <+> a) b)
                                                                              (I_Impl (Message (getContext msg <+> a) (E_Bottom :-> b))
                                                                                      (E_N_N (Message (getContext msg <+> a <+> E_Bottom) b)
                                                                                             (Ax (Message (getContext msg <+> a <+> E_Bottom <+> (b :-> E_Bottom)) E_Bottom))
                                                                                      )
                                                                              )
                                                                              (E_Impl (Message (getContext msg <+> a) E_Bottom)
                                                                                      (genProof (Message (getContext msg <+> a) (a :-> E_Bottom)) rate)
                                                                                      (Ax (Message (getContext msg <+> a) a))
                                                                              )
                                                                      )
                                                              )

type PreRate = ([String], [Bool])

preRateToContext :: PreRate -> Context  
preRateToContext (s, []) = []
preRateToContext (s, b) = [if head b 
                           then E_Var $ head s
                           else (E_Var $ head s) :-> E_Bottom] ++ preRateToContext (tail s, tail b)

genTree :: PreRate -> Expr -> Node  
genTree (s, b) e = if length s == length b
                   then genProof (Message (preRateToContext (s, b)) e) (rateByVectors s b)
                   else exclusionOfAnAssumption (preRateToContext (s, b)) 
                                                (E_Var $ s !! (length b)) e 
                                                (genTree (s, b ++ [True]) e)
                                                (genTree (s, b ++ [False]) e)

buildProof :: Expr -> String
buildProof e = case refutation e of
                (Just rate) -> "Formula is refutable [" ++ showRate rate ++ "]"
                Nothing -> show $ genTree ((Data.Set.elems $ getSetOfVars e), []) e

main = do
    s <- getLine
    putStrLn $ buildProof $ fromJust $ parseExpr s