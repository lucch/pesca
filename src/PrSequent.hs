module PrSequent where

import PrelSequent
import Sequent

-- printing sequent calculus. AR 4/4/1999 -- 14/4

-- printing in ASCII

prSequent :: Sequent -> String
prSequent (ant,suc) = 
  prTList ", " (map (prFormula 1) ant) +++ "=>" +++
  prTList ", " (map (prFormula 1) (reverse suc))

prFormula n f =
  case f of
    Scheme i terms  -> i ++ prArgList (map prTerm terms)
    Predic p [x,y]  | infixPredicate p -> prTerm x +++ p +++ prTerm y
    Predic p terms  -> p ++ prArgList (map prTerm terms)
    Falsum          -> "_|_"
    Neg  a          -> "~" +++ prf 3 a
    Conj a b        -> parIf 2 (prf 3 a +++ "&"  +++ prf 3 b)
    Disj a b        -> parIf 2 (prf 3 a +++ "v"  +++ prf 3 b)
    Impl a b        -> parIf 1 (prf 2 a +++ "->" +++ prf 2 b)
    Univ x a        -> "(" ++ "/A" ++ x ++ ")" ++ prf 3 a
    Exist x a       -> "(" ++ "/E" ++ x ++ ")" ++ prf 3 a
   where
    parIf k s = if n > k then "(" ++ s ++ ")" else s
    prf = prFormula

prTerm t =
 case t of
   Var x      -> x
   Meta c     -> c
   NewMeta c  -> c
   Apply f [x,y]  | infixFunction f -> prTerm x +++ f +++ prTerm y
   Apply f tt -> f ++ prArgList (map prTerm tt)

prProof = prProofNodes False
prProofNodes sh tree = foldr1 lined (map prLine layers) ++ prParams where ---
 layers    = [[prSeqn sh n s | ((n,s),_) <- nodesOfProof tree, length n == ht-k] 
                                                                | k <- [0 .. ht-1]]
 prSeqn sh n s = (if sh then ((concat (map show n))+++) else id) (prSequent s) 
 ht        = htProof tree
 prLine ss = foldr1 (\x y -> x ++ "   " ++ y) ss
 lined x y = x ++++ replicate (length x) '-' ++++ y
 prParams  = let pp = paramsOfProof tree in 
              case pp of
               [] -> ""
               _  -> "\n\nParameters" +++ foldr1 (+++) pp 

---------

prGoals goals = foldr (++++) "" (map prGoal goals) where
 prGoal (Left (ints,sequent)) = prGoalId ints +++ "=" +++ prSequent sequent
 prGoal (Right par)           = par +++ "=" +++ "?"

prGoalId n = foldl1 (++) (map show n) -- works for 1..9 only

---------------------------------------------------
-- printing in LaTeX

-- printing proof trees as LaTeX files

prLatexProof proof = prLatexFile ("\\[" ++++ prProof proof ++++ "\\]") where
   prProof (Goal seq)             = makeLatex (prSequent seq ++ "^{??}")
   prProof (Param c)              = makeLatex (c +++ "= ?")
   prProof (Proof ident seq [])   = 
     "\\infer{" ++++
     makeLatex (prSequent seq) ++++ "}{" ++ makeLatex ident ++ "}"
--     makeLatex (prSequent seq ++ "^{" ++ ident ++"}") -- axiom without line
   prProof (Proof ident seq proofs) =
     "\\infer[{\\scriptstyle" +++ makeLatex ident  ++ "}]{" ++++
     makeLatex (prSequent seq) ++++ "}{" ++++
     prTList "\n & \n" (map prProof proofs) ++++ "}"

prLatexFormula n f = makeLatex (prFormula n f)

prLatexFile string =
 "\\documentstyle[proof]{article}" ++++
 "\\setlength{\\parskip}{2mm}" ++++
 "\\setlength{\\parindent}{0mm}" ++++
--- "\\newcommand{\\discharge}[2]{\\stackrel {#1. \\ }{[ #2 ]}}" ++++ -- JvP's
 "\\newcommand{\\discharge}[2]{\\begin{array}[b]{c} #1 \\\\ #2 \\end{array}}" ++++
 "\\begin{document}" ++++ 
 string ++++ 
 "\\end{document}"

makeLatex s =
 case s of
   '_':'|':'_':t -> "\\bot"     +++ makeLatex t
   '~'        :t -> "\\sim"     +++ makeLatex t
   '&'        :t -> "\\&"       +++ makeLatex t
   ' ':'v':' ':t -> " \\vee"    +++ makeLatex t
   '-':'>'    :t -> "\\supset"  +++ makeLatex t
   '=':'>'    :t -> "\\Rightarrow" +++ makeLatex t
   '/':'A'    :t -> "\\forall"  +++ makeLatex t
   '/':'E'    :t -> "\\exists"  +++ makeLatex t
   'G':'a':'m':'m':'a':t -> "\\Gamma" +++ makeLatex t
   'D':'e':'l':'t':'a':t -> "\\Delta" +++ makeLatex t
   '#'        :t -> "\\#" +++ makeLatex t
   c          :t -> c : makeLatex t
   []            -> []

-- auxiliary operations

prTList t ss =
 case ss of
   []   -> ""
   [s]  -> s
   s:ss -> s ++ t ++ prTList t ss

prArgList tt =
 case tt of
   []  -> ""
   _   -> "(" ++ prTList "," tt ++ ")"

