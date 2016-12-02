module Sequent where

-- sequent calculi. AR 4/4/1999 -- 14/4
-- The abstract syntax of formulae, sequents, and proofs

type Ident = String

data Formula = Scheme Ident [Term]      -- A           (schematic letter)
             | Predic Ident [Term]      -- Pred(x,y)   (predication formula) 
             | Falsum                   -- _|_
             | Neg  Formula             -- ~A
             | Conj Formula Formula     -- A & B
             | Disj Formula Formula     -- A v B
             | Impl Formula Formula     -- A -> B
             | Univ Ident Formula       -- (/Ax)C
             | Exist Ident Formula      -- (/Ex)C

             | Other ()                 -- 7/11/2000 for Alfa plugin
                 deriving (Eq,Show)

data Term = Var Ident
          | Meta Ident
          | NewMeta Ident ---
          | Apply Ident [Term]
               deriving (Eq,Show)

type Context = [Formula]
type Sequent = (Context,Context)

------------------------

-- identifiers treated as infixes

infixPredicate p = case p of
                     c:_ | c `elem` "=#<>\\" -> True
                     _                       -> False
infixFunction f  = case f of
                     c:_ | c `elem` "+-*\\"  -> True
                     _                       -> False

------------------------

data Proof = 
   Goal Sequent
 | Param Ident
 | Proof Ident Sequent [Proof]   deriving (Eq,Show)

isAtomic :: Formula -> Bool
isAtomic f =
 case f of
   Falsum -> False
   _      -> isNotComplex f

isNotComplex :: Formula -> Bool
isNotComplex f =
 case f of
   Scheme _ _ -> True
   Predic _ _ -> True
   Falsum     -> True
   Other _    -> True
   _          -> False

type Obligation = Either Sequent Ident  -- proof obligation: premises and parametres
type Obligations = [Obligation]

--------------------

-- the type of shared-context rules

type AbsRule     = Sequent -> Maybe Obligations   -- Nothing = rule does not apply
type AbsCalculus = [(Ident,AbsRule)]

--------------------

-- to identify leaves and nodes in proof trees

type GoalId = Either [Int] Ident  -- either premise or individual parametre

goalsOfProof :: Proof -> [Either ([Int],Sequent) Ident]
goalsOfProof tree = [Left x  | (x,True) <- nodesOfProof  tree] ++ 
                    [Right y | y        <- paramsOfProof tree] 

nodesOfProof :: Proof -> [(([Int],Sequent), Bool)]
nodesOfProof tree = giveNums [] 1 tree where
 giveNums n k tr =
  case tr of 
    Goal s        -> [((n ++ [k], s),True)]
    Proof _ s trs -> ((n ++ [k], s),False) :
                         foldl (++) [] 
                            [giveNums (n ++ [k]) i t | (i,t) <- zip [1..] trs]
    _             -> []

paramsOfProof :: Proof -> [Ident]
paramsOfProof tree = 
  case tree of 
    Goal s        -> []
    Param x       -> [x]
    Proof _ s trs -> foldl (++) [] (map paramsOfProof trs) 

conclusionOfProof :: Proof -> Sequent
conclusionOfProof tree = 
  case tree of 
    Goal s        -> s
    Param x       -> ([],[])
    Proof _ s trs -> s

---------------

refreshIdent :: [Ident] -> Ident -> Ident
refreshIdent ids i = if i `elem` ids then refreshIdent ids (nxt i) else i where
 nxt s = s ++ "'"

---------------

substFormula :: [Ident] -> ([(Ident,Term)] -> Term -> Term) -> 
                                          [(Ident,Term)] -> Formula -> Formula
substFormula symbs oper subst formula = 
  case formula of
     Scheme p terms  -> Scheme p (map (oper subst) terms)
     Predic p terms  -> Predic p (map (oper subst) terms)
     Neg  a          -> Neg (ss a)
     Conj a b        -> Conj (ss a) (ss b)
     Disj a b        -> Disj (ss a) (ss b)
     Impl a b        -> Impl (ss a) (ss b)
     Univ x a        -> let y = mkVar x in Univ  y (sss x y a)
     Exist x a       -> let y = mkVar x in Exist y (sss x y a)
     _               -> formula
   where
    ss       = substFormula symbs     oper subst
    sss x y  = substFormula (y:symbs) oper ((x,Var y):subst)
    mkVar x  = refreshIdent symbs x

substVar :: [(Ident,Term)] -> Term -> Term
substVar subst term =
 case term of
    Apply f terms -> Apply f (map (substVar subst) terms)
    Var x         -> case lookup x subst of
                       Just t -> t
                       _      -> term
    _             -> term

substTerm :: [(Ident,Term)] -> Term -> Term
substTerm subst term =
 case term of
    Apply f terms -> Apply f (map (substTerm subst) terms)
    Meta  m       -> case lookup m subst of
                       Just t -> t
                       _      -> term
    NewMeta  m    -> case lookup m subst of
                       Just t -> t
                       _      -> term
    _             -> term

makeParams :: [(Ident,Term)] -> Term -> Term
makeParams subst term =
 case term of
    Apply f terms -> Apply f (map (substTerm subst) terms)
    NewMeta  m    -> case lookup m subst of
                       Just t -> t
                       _      -> term
    _             -> term

notOccur :: Ident -> [Formula] -> Bool
notOccur x cont = not (x `elem` foldl (++) [] (map freeVariables cont))
 
freeVariables :: Formula -> [Ident]
freeVariables formula =
 case formula of
    Scheme p terms  -> foldl (++) [] (map freeVariablesOfTerm terms)
    Predic p terms  -> foldl (++) [] (map freeVariablesOfTerm terms)
    Neg  a          -> freeVariables a
    Conj a b        -> freeVariables a ++ freeVariables b
    Disj a b        -> freeVariables a ++ freeVariables b
    Impl a b        -> freeVariables a ++ freeVariables b
    Univ x a        -> filter (/=x) (freeVariables a)
    Exist x a       -> filter (/=x) (freeVariables a) 
    _               -> []

freeVariablesOfTerm t =
    case t of
      Apply f terms -> foldl (++) [] (map freeVariablesOfTerm terms)
      Var x         -> [x]
      _             -> []

htProof :: Proof -> Int     -- the maximum height of a path in a proof
htProof (Goal _)       = 1
htProof (Param _)      = 0
htProof (Proof _ _ []) = 1
htProof (Proof _ _ pp) = 1 + maximum (map htProof pp)

eqMultis :: (Eq a) => [a] -> [a] -> Bool              -- multiset equality
eqMultis m1 m2 = length m1 == length m2 && m1 `subset` m2 where
 subset k1 k2 = all (\x -> occs x k2 >= occs x k1) k1
 occs x k = length (filter (==x) k)

ordsOfSequent :: Sequent -> [(Sequent,(Int,Int))]
ordsOfSequent (ant,suc) = 
 [((ant',suc'),(i,j)) | (ant',i) <- ordsOf ant, (suc',j) <- ordsOf suc]
  where
    ordsOf []   = [([],0)]
    ordsOf list = [(x : take (n-1) list ++ drop n list, n) | 
                                            (x,n) <- zip list [1..]]

