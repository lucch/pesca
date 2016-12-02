module PSequent where

import PrelSequent
import Sequent

-- parsers for formulae and sequents. AR 4/4/1999 -- 13/4

pSequent :: Parser Char Sequent
pSequent = pContext ... jL "=>" +.. (pContext *** reverse)

pContext = pTList "," (pFormula 1) ||| succeed []

pFormula :: Int -> Parser Char Formula  -- Int is precedence number
pFormula 3 =
     pPred .... pArgList pTerm        *** (\ (p,x) -> Predic p x)
 ||| pTerm .... pPrInfix .... pTerm   *** (\ (x,(p,y)) -> Predic p [x,y])
 ||| pScheme ... pArgList pTerm       *** (\ (p,x) -> Scheme p x)
 ||| lits "_|_"                       <<< Falsum
 ||| lits "~" +.. pJ (pFormula 3)     *** Neg
 ||| lits "(" +.. jL "/A" +..
     pJ pVar ... lits ")" +.. pFormula 3 *** (\ (x,a) -> Univ x a)
 ||| lits "(" +.. jL "/E" +..
     pJ pVar ... lits ")" +.. pFormula 3 *** (\ (x,a) -> Exist x a)
 ||| pParenth (pFormula 1)
pFormula 2 =
  pFormula 3 ... 
   (jL "&" +.. pTList "&" (pFormula 3)   *** (\b -> \x -> Conj x (foldr1 Conj b))
     |||
    jL "v" +.. pTList "v" (pFormula 3)   *** (\b -> \x -> Disj x (foldr1 Disj b))
     |||
    succeed id)
      ***
       (\ (a,b) -> b a)
pFormula 1 =
  pFormula 2 ... 
   (jL "->" +.. pFormula 1 *** (\b -> \a -> Impl a b)
    ||| succeed id)
      ***
       (\ (a,b) -> b a)

pTerm = 
  pTerm2 .... 
  (pInfix .... pTerm2 *** (\ (f,y) -> \x -> Apply f [x,y]) ||| succeed (\x -> x))
   *** (\ (x,y) -> y x)

pTerm2 =
  pConst .... pArgList pTerm  *** (\ (f,x) -> Apply f x)  
 +||
  pVar                        *** Var
 |||
  pMeta                       *** Meta
 |||
  pParenth pTerm

pScheme = longestOfSome pCapital                       -- 1+ capital letters
pPred   = pCapital ... longestOfSome pSmall *** junct  -- capit. with 1+ small 
pConst  = pSmall   ... longestOfSome pSmall *** junct  -- 2+ small letters
           |||
          longestOfSome pDigit                         -- or 1+ digits
pVar    = pSmall   ... longestOfMany (literal '\'') *** junct
                                                       -- small with 0+ primes
pMeta   = literal '?' +.. pVar ---

pPrInfix = 
  foldl1 (|||) (map lits (words "= < > #")) 
 ||| 
  literal '\\' ... longestOfSome pLetter *** junct

pInfix = 
  foldl1 (|||) (map lits (words "+ - *")) 
 ||| 
  literal '\\' ... longestOfSome pLetter *** junct

junct (a,b) = a:b

pSmall   = satisfy (`elem` ['a'..'z'])
pCapital = satisfy (`elem` ['A'..'Z'])
pLetter  = pCapital ||| pSmall
pDigit   =  satisfy (`elem` ['0'..'9'])

pRuleIdent = longestOfSome (satisfy (not . (`elem` " \n\t")))

pGoalId :: Parser Char [Int]
pGoalId = longestOfSome (satisfy (`elem` ['1' .. '9']) *** read . (:[])) ---

