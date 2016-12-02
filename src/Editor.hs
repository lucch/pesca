{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import PrelSequent
import Sequent
import Interaction
import PSequent
import PrSequent
import Calculi
import Axioms
import Natural
import System.Cmd (system)
import System.IO.Error (isEOFError)
import Control.Exception (catch, toException, SomeException(..))

-- sequent calculus proof editor. Aarne Ranta 8/4/1999 -- 26/4 -- 14/11/2000

main :: IO ()
main = do putStr welcomeMsg
          editProofs ((rulesOfCalculus (Calculus ["G3i"]), Goal ([],[])),[])
          return ()

welcomeMsg =
 "\nWelcome to a proof editor for sequent calculus, version November 24, 2000." ++++
 "Written by Aarne Ranta, e-mail aarne@cs.chalmers.se" ++++
 "Starting with the calculus G3i (intuitionistic predicate calculus)." ++++
 "Type ? for help on available commands.\n\n"

editProofs :: (Env,[String]) -> IO (Proof,String)
editProofs envh@(env@(calculus,tree),history) =
 do
 putStr "|- "
 s <- catch getLine (\e -> if isEOFError e then return "q" else ioError e)
 let (comm,m0)  = case pCommand calculus s of
                    (x,""):_ -> (x,     "")
                    _        -> (CVoid, "No parse of command\n")
     (tree',m1) = exec comm env
     (env',msg) = ((calculus,tree'), m0 ++ m1)
     history'   = history ++ [s]
     envh'      = (env', history')
  in
   do
   putStr "\n"
   putStr msg
   putStr "\n"
   (case comm of
      CAxioms file  -> do s <- readFileIf file
                          let (na@(_,a),m) = readAxioms s
                              a'    = axioms2calculus a in
                            do putStr m
                               writeAndLatexFile (file ++".rules") (prLatexAxioms na)
                               editProofs ((calculus ++ a', tree'),history')
      CLatex file   -> do writeAndLatexFile file (prLatexProof tree')
                          editProofs envh'
      CNatural file -> do let nat = proof2nat tree'
                          writeAndLatexFile file (prLatexFile (prNatProof nat))
                          editProofs envh'
      CHistory file -> do writeFile file (foldr (++++) "" (history ++ ["q"]))
                          editProofs envh'
      CChange calc' -> let (c,m) = changeCalculus calculus calc' in
                        do putStr m
                           editProofs ((c,tree'),history')
      CQuit         -> do writeFile "myhistory.txt"
                                    (foldr (++++) "" (history ++ ["q"]))
                          putStr "history written in myhistory.txt\n"
                          return (tree',"")
      CManual       -> do system "latex manual.tex >& /dev/null ; xdvi manual.dvi &"
                          editProofs envh'
      _             -> editProofs envh')

-----------------------

writeAndLatexFile file content = do
  writeFile (file ++ ".tex") content
  system ("latex" +++ file ++ ".tex >& /dev/null ; xdvi" +++ file ++ ".dvi &")
  return ()

type Env = (AbsCalculus, Proof)

data Command =
   CRefine [Int] (Int,Int) Ident
 | CInstance Ident Term
 | CTry    [Int] Int
 | CNew    Sequent
 | CRemove [Int]
 | CShowGoals
 | CShowTree
 | CShowApplicable [Int]
 | CChange Calculus
 | CAxioms String
 | CQuit
 | CLatex String
 | CNatural String
 | CHistory String
 | CHelp
 | CManual
 | CVoid

exec :: Command -> Env -> (Proof,String)
exec c env@(calculus,tree) =
 case c of
   CRefine g (i,j) r  -> (t, m ++++ prProof t)
                            where (t,m) = refine (calculus,tree) g (i,j) r
   CInstance par term -> (t, prProof t)
                            where t = instantiate calculus par term tree
   CTry g limit       -> (t, m ++++ prProof t)
                            where (t,m) = tryRefine (calculus,tree) g limit
   CNew sequent       -> (t, prProof t)
                            where t = Goal sequent
   CRemove ints       -> (t, m ++++ prProof t)
                            where (t,m) = remove tree ints
   CShowGoals         -> (tree, prGoals (goalsOfProof tree))
   CShowTree          -> (tree, prProofNodes True tree)
   CShowApplicable g  -> (tree, showAllApplicableRules (calculus,tree) g)
   CChange _          -> (tree, "")
   CAxioms file       -> (tree, "axioms written in" +++ file ++ ".rules.tex")
   CLatex file        -> (tree, "proof written in" +++ file ++ ".tex")
   CNatural file      -> (tree, "natural deduction tree written in" +++ file ++ ".tex")
   CHistory file      -> (tree, "history written in" +++ file)
   CHelp              -> (tree, helpMessage)
   CManual            -> (tree, "")
   CQuit              -> (tree, "Goodbye")
   _                  -> (tree, "no command processed")

helpMessage =
 "Commands:\n" ++++
 "  r goal [A int] [S int] rule  -  refine goal with rule (A changes active" ++++
 "                                  formula in antecedent, S in succedent)" ++++
 "  i parametre term             -  instantiate parametre with term" ++++
 "  t goal int                   -  try to refine goal to depth int" ++++
 "  n sequent                    -  new sequent to prove"  ++++
 "  u node                       -  remove subtree node"   ++++
 "  s                            -  show subgoals"         ++++
 "  w                            -  show current proof tree" ++++
 "  a goal                       -  show rules applicable to goal" ++++
 "  c calculus                   -  change calculus into one of" ++++
 "                                  " ++ prCalculi                 ++++
 "  x file                       -  read axioms from file and write rules into" ++++
 "                                  file.rules.tex" ++++
 "  l [file]                     -  print current proof in LaTeX to file,"  ++++
 "                                  which is by default myproof.tex" ++++
 "  d [file]                     -  print current proof in natural deduction to"++++
 "                                  LaTeX file, which is by default" ++++
 "                                  mydeduction.tex (works only for G3i, G3ip)" ++++
 "  h [file]                     -  print history to file," ++++
 "                                  which is by default myhistory.txt" ++++
 "  ?                            -  print this help message" ++++
 "  m                            -  show the PESCA manual" ++++
 "  q                            -  write history in myhistory.txt and quit\n"

----------------------

pCommand calculus =
  jL "r" +.. pGoalId ... pJ (jL "A" +.. pIntc ||| succeed 1) ...
             pJ (jL "S" +.. pIntc ||| succeed 1) ... pJ pRuleIdent
                         *** (\ (g,(i,(j,r))) -> CRefine g (i,j) r)
 |||
  jL "i" +.. pRuleIdent ... pJ pTerm
                         *** (\ (m,t) -> CInstance m t)
 |||
  jL "x" +.. pRuleIdent  *** CAxioms
 |||
  jL "t" +.. pGoalId ... pJ pIntc
                         *** (\ (g,m) -> CTry g m)
 |||
  jL "n" +.. pSequent    *** CNew
 |||
  jL "u" +.. pGoalId     *** CRemove
 |||
  jL "s"                 <<< CShowGoals
 |||
  jL "w"                 <<< CShowTree
 |||
  jL "a" +.. pGoalId     *** CShowApplicable
 |||
  jL "c" +.. pTList "+" pRuleIdent  *** CChange . Calculus
 |||
  jL "l" +.. (pRuleIdent ||| succeed "myproof")     *** CLatex
 |||
  jL "d" +.. (pRuleIdent ||| succeed "mydeduction") *** CNatural
 |||
  jL "h" +.. (pRuleIdent ||| succeed "myhistory.txt") *** CHistory
 |||
  jL "?"                 <<< CHelp
 |||
  jL "m"                 <<< CManual
 |||
  jL "q"                 <<< CQuit

---------------------

showAllApplicableRules :: (AbsCalculus,Proof) -> [Int] -> String
showAllApplicableRules (calculus,proof) ints =
 case lookup ints [x | Left x <- goalsOfProof proof] of
   Just sequent -> foldr (++++) [] (map prAr (allApplicableRules calculus sequent))
   _            -> prGoalId ints +++ "does not exist"
  where
    prAr ((sq,(i,j)),((r,_),_)) =
      "r" +++ prGoalId ints +++ "A" ++ show i +++ "S" ++ show j +++ r +++
      "--" +++ prSequent sq

-----------------------

changeCalculus calc calc' =
 case rcalc' of
   [] -> (calc,   "new calculus not recognized\n")
   _  -> (rcalc', "new calculus has" +++ show (length rcalc') +++ "rules\n")
  where rcalc' = rulesOfCalculus calc'

