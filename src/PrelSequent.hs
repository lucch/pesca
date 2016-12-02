{-# LANGUAGE ScopedTypeVariables #-}

module PrelSequent where

import Control.Exception (catch, toException, SomeException(..))

infixr 5 +++
infixr 5 ++++
infixr 2 |||
infixr 2 +||
infixr 5 .>.
infixr 5 ...
infixr 5 ....
infixr 5 +..
infixr 5 ..+
infixr 3 ***
infixr 6 |>
infixr 3 <<<

-- some auxiliary operations for sequent calculus. AR 19/6/1998 -- 22/4/1999
-- Copyright (c) Aarne Ranta 1998-99, under GNU General Public License (see GPL)

-- list operations

nub :: Eq a => [a] -> [a]
nub l = case l of 
          []  -> []
          a:k -> if elem a k then nub k else a : nub k

combinations :: [[a]] -> [[a]]
combinations t = case t of []    -> [[]]
                           aa:uu -> [a:u | a <- aa, u <- combinations uu]

-- useful Error type

data Err a = Ok a | Bad String            -- like Maybe type with error msgs

mberr s (Just c)  = Ok c                   -- add msg s to Maybe failures
mberr s (Nothing) = Bad s

okError :: Err a -> a
okError c = case c of Ok a -> a
                      _    -> error "no result Ok"

-- printing

indent :: Int -> [String] -> [String]
indent n ss = map (replicate n ' ' ++) ss

a +++ b  = a ++ " "  ++ b
a ++++ b = a ++ "\n" ++ b

readFileIf :: String -> IO String
readFileIf f = catch (readFile f) (\(_ :: SomeException) -> reportOn f) where
 reportOn f =
   do
   putStr ("File " ++ f ++ " does not exist. Returned empty string")
   return ""

-- parser combinators a` la Wadler and Hutton

type Parser a b = [a] -> [(b,[a])]

succeed :: b -> Parser a b
succeed v s = [(v,s)]

fails :: Parser a b
fails s = []

(|||) :: Parser a b -> Parser a b -> Parser a b
(p1 ||| p2) s = p1 s ++ p2 s

(.>.) :: Parser a b -> (b -> Parser a c) -> Parser a c
(p1 .>. p2) s = [(b,z) | (a,y) <- p1 s, (b,z) <- p2 a y]

(...) :: Parser a b -> Parser a c -> Parser a (b,c)
p1 ... p2 = p1 .>. (\x -> p2 .>. (\y -> succeed (x,y)))

(+..) :: Parser a b -> Parser a c -> Parser a c
p1 +.. p2 = p1 .>. (\x -> p2 .>. (\y -> succeed y))

(..+) :: Parser a b -> Parser a c -> Parser a b
p1 ..+ p2 = p1 .>. (\x -> p2 .>. (\y -> succeed x))

(***) :: Parser a b -> (b -> c) -> Parser a c
p *** f = p .>. (\x -> succeed (f x))

(<<<) :: Parser a b -> c -> Parser a c  -- return
p <<< v = p *** (\x -> v)

item :: Parser a a
item [] = []
item (a:x) = [(a,x)]

(|>) :: Parser a b -> (b -> Bool) -> Parser a b
p |> b = p .>. (\x -> if b x then succeed x else fails)

satisfy :: (a -> Bool) -> Parser a a
satisfy b = item |> b

literal :: (Eq a) => a -> Parser a a
literal x = satisfy (==x)

guarantee :: Parser a b -> Parser a b
guarantee p s = let u = p s in (fst (head u),snd (head u)) : tail u

first :: Parser a b -> Parser a b
first p s = case p s of []    -> []
                        (x:l) -> [x]

(+||) :: Parser a b -> Parser a b -> Parser a b
p1 +|| p2 = first (p1 ||| p2)

many :: Parser a b -> Parser a [b]
many p = p .>. (\x -> many p .>. (\y -> succeed (x:y))) ||| succeed []

some :: Parser a b -> Parser a [b]
some p = (p ... many p) *** (\ (x,y) -> x:y)

longestOfMany :: Parser a b -> Parser a [b]
longestOfMany p = 
  guarantee 
   (p .>. (\x -> longestOfMany p .>. (\y -> succeed (x:y))) +|| succeed [])

pJunk   :: Parser Char String
pJunk = longestOfMany (satisfy (\x -> elem x "\n\t "))

pJ :: Parser Char a -> Parser Char a
pJ p = pJunk +.. p ..+ pJunk

pTList  :: String -> Parser Char a -> Parser Char [a]
pTList t p = p .... many (jL t +.. p) *** (\ (x,y) -> x:y) ---- mod. AR 5/1/1999

(....) :: Parser Char b -> Parser Char c -> Parser Char (b,c)
p1 .... p2 = p1 ... pJunk +.. p2

literals :: (Eq a) => [a] -> Parser a [a]
literals l = case l of []  -> succeed [] 
                       a:l -> literal a ... literals l *** (\ (x,y) -> x:y)

pOpt :: (Eq a) => [a] -> Parser a [a]
pOpt l = succeed [] ||| literals l

lits :: (Eq a) => [a] -> Parser a [a]
lits  = literals

jL :: String -> Parser Char String
jL = pJ . lits

pParenth p = literal '(' +.. pJunk +.. p ..+ pJunk ..+ literal ')'
pArgList p = pParenth (pTList "," p) +|| succeed [] -- (p,...,p), poss. empty

longestOfSome p = (p ... longestOfMany p) *** (\ (x,y) -> x:y)

pFileName =
  longestOfSome (satisfy (`elem` nameChar))
   where nameChar = ['0'..'9'] ++ ['A'..'Z'] ++ ['a'..'z'] ++ "/._-"

pIntc :: Parser Char Int
pIntc = some (satisfy numb) *** read
         where numb x = elem x ['0'..'9']

fullParses p = map fst (filter ((==[]) . snd) p)


