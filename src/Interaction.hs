module Interaction where

import PrelSequent
import Sequent
import PrSequent

-- operations for interactive theorem proving. AR 8/4/1999 -- 13/4

refine :: (AbsCalculus,Proof) -> [Int] -> (Int,Int) -> Ident -> (Proof,String)
refine (calculus,tree) ints (i,j) ident =
 case lookup ints [z | Left z <- goalsOfProof tree] of
   Just (ant,suc) ->
     case refineLocal calculus ident goal of
       Ok obs -> (replace tree ints (Proof ident goal (map (newGoal obs) obs)),"")
       Bad s  -> (tree,s)
      where  
       goal                   = (activate i ant, activate j suc)
       newParams obls         = [(p, Meta (refreshP p)) | Right p <- obls] 
       newGoal obls g         = case g of
                                  (Left sequent) -> Goal  (refreshS obls sequent)
                                  (Right param)  -> Param (refreshP param)
       refreshS obls (an,su)  = (map sp an, map sp su) 
                                  where  ---
                                   sp = substFormula [] makeParams (newParams obls)
       refreshP p             = refreshIdent (paramsOfProof tree) p
       activate int []        = []
       activate int cont      = let  n=int-1 in
                                 if   length cont < n then cont
                                 else cont!!n : take n cont ++ drop (n+1) cont
   _ -> (tree, "no such goal")

instantiate :: AbsCalculus -> Ident -> Term -> Proof -> Proof
instantiate calc param term proof =
 case proof of
   Goal (ant,suc)          -> Goal (substIn ant, substIn suc)
   Param x                 -> proof
   Proof rule (a,s) proofs -> Proof rule (substIn a, substIn s) (instProofs proofs)
  where 
   substIn       = map (substFormula symbs substTerm [(param,term)])
                    where symbs = [] --- freeVariablesOfTerm term
   instProofs pp = map (instantiate calc param term) (filter (/=(Param param)) pp)

remove :: Proof -> [Int] -> (Proof,String)
remove tree ints = 
 case lookup ints (map fst (nodesOfProof tree)) of
   Just sequent -> (replace tree ints (Goal sequent),"")
   _            -> (tree, prGoalId ints +++ "does not exist")

refineLocal :: AbsCalculus -> Ident -> Sequent -> Err Obligations
refineLocal calculus ident sequent =
 case lookup ident calculus of
   Just rule ->
     case rule sequent of
       Just obls -> Ok  obls
       _         -> Bad ("rule" +++ ident +++ "does not apply")
   _  -> Bad ("rule" +++ ident +++ "does not exist")

applicableRules :: AbsCalculus -> Sequent -> [((Ident,AbsRule),Obligations)]
applicableRules calc sequent = [ ((i,r),seqs r) | (i,r) <- calc, ok r] where
 ok r   = case r sequent of
            Just _ -> True
            _      -> False
 seqs r = case r sequent of
            Just ss -> ss
            _       -> []

allApplicableRules :: AbsCalculus -> Sequent -> 
  [((Sequent,(Int,Int)),((Ident,AbsRule),Obligations))]
allApplicableRules calc sequent = 
    [((sq',i),app) | (sq',i) <- ordsOfSequent sequent,
                     app     <- applicableRules calc sq']

replace :: Proof -> [Int] -> Proof -> Proof
replace tree ints tree' =
  case (tree,tail ints) of
    (_, []) -> tree'
    (Proof c s trs, k:n) | k <= length trs  -> 
                            Proof c s (t1 ++ [tr'] ++ tail t2) 
                                 where (t1,t2) = splitAt (k-1) trs
                                       tr' = replace (head t2) (k:n) tree'
    _       -> tree

tryRefine :: (AbsCalculus,Proof) -> [Int] -> Int -> (Proof,String)
tryRefine (calculus,tree) goal limit  =
 case lookup goal [x |  Left x <- goalsOfProof tree] of
   Just sequent ->
     case tryMethod calculus limit sequent of
       proof:_  -> (replace tree goal proof,"")
       []       -> (tree, "no proof found")
   _ -> (tree, prGoalId goal +++ "does not exist")

tryMethod :: AbsCalculus -> Int -> Sequent -> [Proof]
tryMethod calculus limit sequent =
 case limit of
   0 -> [Proof i sequent' [] | (sequent',_) <- ordsOfSequent sequent,
                               ((i,r),obls) <- applicableRules calculus sequent',
                               null [x | Left x  <- obls]]
   _ -> [Proof i sequent' pp | (sequent',_) <- ordsOfSequent sequent,
                               ((i,r),ss)   <- applicableRules calculus sequent',
                               pp           <- tryToEach (limit - 1) ss]
  where
   tryToEach n ss = combinations (map (tryMethod calculus n) [x | Left x  <- ss])

