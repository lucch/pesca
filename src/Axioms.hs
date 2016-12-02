module Axioms where

import PrelSequent
import Sequent
import PrSequent
import PSequent

-- non-logical rules formed from axioms. AR 15/4/1999 -- 24/3/2000

type Axiom = ([Atom],[Atom])
data Atom  = Atom Ident [ATerm] deriving (Eq,Read,Show)
data ATerm = Par Ident | Appl Ident [ATerm] deriving (Eq,Read,Show)

axioms2calculus :: [(Ident,Axiom)] -> AbsCalculus
axioms2calculus axx = [(i,axiom2rule a) | (i,a) <- axx]

axiom2rule :: Axiom -> AbsRule
axiom2rule (prems,concl) =
  \ (ant,suc) ->
    case findInstanceOfAtoms concl ant of
      Just insts -> Just (map (Left . (mkPrem insts)) prems ++ map Right params)
       where
        mkPrem i p = (substFormula s substTerm i (atom2formula params p) : ant, suc)
                      where s = foldl (++) [] (map (freeVariablesOfTerm . snd) i)
        params = nub [c | Atom _ args <- prems, 
                          c <- foldl (++) [] (map parOf args), 
                          not (c `elem` [d | Atom _ xx <- concl, 
                                             d <- foldl (++) [] (map parOf xx)])]
        parOf t =
         case t of
           Par x    -> [x]
           Appl _ y -> foldl (++) [] (map parOf y)
      _          -> Nothing

findInstanceOfAtoms :: [Atom] -> [Formula] -> Maybe [(Ident,Term)]
findInstanceOfAtoms atoms formulae = 
 case (atoms,formulae) of
   ([],_)   -> Just []
   (_, [])   -> Nothing
   (_, f:fs) -> findOne [f:fs' | fs' <- subsets (length atoms - 1) fs]
  where
   findOne []     = Nothing
   findOne (s:ss) = case instanceOfAtoms atoms s of
                      Just i -> Just i
                      _      -> findOne ss

instanceOfAtoms :: [Atom] -> [Formula] -> Maybe [(Ident,Term)]
instanceOfAtoms atoms formulae = 
  if   length atoms == length formulae    && 
       all matchForm (zip atoms formulae) &&
       complete insts                     &&
       consistent insts
  then Just [(a,f) | (a,Just f) <- insts]
  else Nothing
   where
    matchForm ((Atom pred args),formula) = 
      case formula of
        Predic f xx | f == pred && length xx == length args -> True
        _ -> False
    insts = foldl (++) [] (map tryInst (zip args1 args2))
    tryInst (a1,a2) =
     case (a1,a2) of
       (Par a,f)                       -> [(a,Just f)]
       (Appl c a, Apply c' a') | c==c' -> foldl (++) [] (map tryInst (zip a a'))
       _                               -> [("x",Nothing)]
    args1 = (foldl (++) [] [xx | Atom   _ xx <- atoms])
    args2 = (foldl (++) [] [xx | Predic _ xx <- formulae])
    consistent t = all (`lookupIsUnique` t) (map fst t)
    complete t = 
     case t of
       (_,Nothing):_ -> False
       (_,Just _):t' -> complete t'
       []            -> True


atom2formula params (Atom f xx) = Predic f (map aterm2term xx) where
 aterm2term t =
  case t of
    Par x     -> if x `elem` params then NewMeta x else Meta x
    Appl f yy -> Apply f (map aterm2term yy)

-----------------

prAxiom :: Axiom -> String
prAxiom (prems,concl) = 
 case prems of
   [] -> prOneInAxiom concl
   _  -> prems' ++++ replicate (max (length prems') (length concl')) '-' ++++ concl'
          where
           concl' = prOneInAxiom concl
           prems' = foldr1 (+++) [prOneInAxiom (p:concl) | p <- prems]

prOneInAxiom atoms =
 case atoms of
   [] -> "Gamma => Delta"
   _  -> prTList ", " (map prAtom atoms) ++ "," +++ "Gamma => Delta"
  where
   prAtom  (Atom p [x,y]) | infixPredicate p = prATerm x +++ p +++ prATerm y
   prAtom  (Atom p xx) = p ++ prArgList (map prATerm xx)
   prATerm (Par c)     = c
   prATerm (Appl f [x,y]) | infixFunction f = prATerm x +++ f +++ prATerm y
   prATerm (Appl f xx) = f ++ prArgList (map prATerm xx)

prLatexAxioms (ns,axx) =
 "\\documentstyle[proof]{article}" ++++
 "\\begin{document}" ++++
 ns ++++ -- new commands 
 foldr (++++) "" ["\\[" ++++ prLatexAxiom ax ++++ "\\]" | ax <- axx] ++++
 "\\end{document}"

prLatexAxiom (name,([],concl)) = 
 makeLatex (prOneInAxiom concl) ++ "^{" ++ makeLatex name ++"}"
prLatexAxiom (name,(prems,concl)) =
 "\\infer[{\\scriptsize" +++ makeLatex name  ++ "}]{" ++++
     makeLatex (prOneInAxiom concl) ++++ "}{" ++++
     prTList "\n & \n" [makeLatex (prOneInAxiom (p:concl)) | p <- prems] ++++ "}"

-----------------

pAxiom :: Parser Char Axiom
pAxiom      = ((pConclusion ..+ jL "->" ||| succeed []) ... pPremises 
                 *** (\ (x,y) -> (y,x)) 
              |||
               jL "~" +.. (pConclusion ||| pParenth pConclusion) *** (\x -> ([],x)))
pPremises   = pTList "v" pAtom ||| lits "_|_" <<< []
pConclusion = pTList "&" pAtom

pAtom  = 
  pATerm .... pPrInfix .... pATerm   *** (\ (x,(p,y)) -> Atom p [x,y])
 |||
  pPred  ... pArgList pATerm *** (\ (p,x) -> Atom p x)

pATerm  =
 pATerm2 .... 
  (pInfix .... pATerm2 *** (\ (f,y) -> \x -> Appl f [x,y]) ||| succeed (\x -> x))
   *** (\ (x,y) -> y x)

pATerm2 = 
  pConst ... pArgList pATerm *** (\ (p,x) -> Appl p x) 
 ||| 
  pVar *** Par
 |||
  pParenth pATerm

pAxioms :: Parser Char [(Ident,Axiom)]
pAxioms = longestOfMany (pJ pRuleIdent ... pJ pAxiom)

-----------------

-- get LaTeX newcommand prelude and the axioms, separated by a comment line
-- starting with --.
readAxioms :: String -> ((String,[(Ident,Axiom)]),String)
readAxioms s =
 case pAxioms (remComm s') of
    (a,""):_ -> ((news,a),  "all axioms accepted\n")
    (a, _):_ -> ((news,a),  show (length a) +++ "axioms accepted\n")
    _        -> ((news,[]), "no axioms accepted\n")
  where
   (news,s') = let ss = lines s ; (ss1,ss2) = span (\l -> take 2 l /= "--") ss
                in (unlines ss1, unlines ss2)
   remComm s =
    case s of 
      []        -> []
      '-':'-':t -> remComm t2 where t2 = dropWhile  (/='\n') t
      c      :t -> c : remComm t

-----------------

subsets int list =
 case int of
   0 -> [[]]
   n -> [h:t | h <- list, t <- subsets (n-1) (del h list)]
  where 
   del x []     = []
   del x (y:ys) = if x==y then ys else y : del x ys

lookupIsUnique x t = length (nub [y | (z,y) <- t, z==x]) < 2

