module Calculi where

import Sequent

-- sequent calculi from Negri & von Plato (1999). AR 13/4/1999 -- 19/3

data Calculus = Calculus [Ident]

rulesOfCalculus :: Calculus -> AbsCalculus
rulesOfCalculus (Calculus calcs) = foldl (++) [] (map rOf calcs) where
 rOf calc =
  case calc of
   "G3ip"  -> justPremises $ gxpL ++ gipR ++ g3iLImpl
   "G4ip"  -> justPremises $ gxpL ++ gipR ++ g4iLImpl
   "G3cp"  -> justPremises $ gxpL ++ gcpRL
   "G3i"   -> justPremises  (gxpL ++ gipR ++ g3iLImpl) ++ g3xqL ++ g3iqR 
   "G3c"   -> justPremises  (gxpL ++ gcpRL           ) ++ g3xqL ++ g3cqR
   "G4i"   -> justPremises  (gxpL ++ gipR ++ g4iLImpl) ++ g3xqL ++ g3iqR
   "Geq"   -> gxeq
   -------------------------------- ADD YOUR OWN CALCULUS HERE
   _      -> []

prCalculi = "G3i G4i G3c G3ip G4ip G3cp Geq"

justPremises :: [(Ident, Sequent -> Maybe [Sequent])] -> 
                [(Ident, Sequent -> Maybe [Either Sequent Ident])]
justPremises = map jP where
 jP (i,f)    = (i, (\x -> mb (f x)))
 mb (Just s) = Just (map Left s)
 mb Nothing  = Nothing

gxpL =
 [("L&", \ (ant,suc) -> 
              case ant of
                Conj a b : rest -> Just [(a:b:rest, suc)]
                _               -> Nothing),
  ("Lv", \ (ant,suc) -> 
              case ant of
                Disj a b : rest -> Just [(a:rest, suc), (b:rest, suc)]
                _               -> Nothing),
  ("L_|_",\ (ant,suc) -> 
              case ant of
                Falsum : rest   -> Just []
                _               -> Nothing)]

gipR =
  [("R&", \ (ant,suc) -> 
              case suc of
                [Conj a b] -> Just [(ant,[a]),(ant,[b])]
                _          -> Nothing),
  ("Rv1", \ (ant,suc) -> 
              case suc of
                [Disj a b] -> Just [(ant,[a])]
                _          -> Nothing),
  ("Rv2", \ (ant,suc) -> 
              case suc of
                [Disj a b] -> Just [(ant,[b])]
                _          -> Nothing),
  ("R->", \ (ant,suc) -> 
              case suc of
                [Impl a b] -> Just [(a:ant,[b])]
                [Neg  a]   -> Just [(a:ant,[Falsum])]
                _          -> Nothing),
  ("ax", \ (ant,suc) ->
                 case suc of
                   [p] | isAtomic p && p `elem` ant -> Just []
                   _                                -> Nothing)
 ]

gcpRL =
  [("R&", \ (ant,suc) -> 
              case suc of
                Conj a b:suc' -> Just [(ant, a:suc'),(ant, b:suc')]
                _             -> Nothing),
  ("Rv",  \ (ant,suc) -> 
              case suc of
                Disj a b:suc' -> Just [(ant, b:a:suc')]
                _             -> Nothing),
  ("R->", \ (ant,suc) -> 
              case suc of
                Impl a b:suc' -> Just [(a:ant, b:suc')]
                Neg  a  :suc' -> Just [(a:ant, Falsum:suc')]
                _             -> Nothing),
  ("L->", \ (ant,suc) -> 
                 case ant of
                   Impl a b : rest -> Just [(rest, a:suc), (b:rest,suc)]
                   Neg a    : rest -> Just [(rest, a:suc), (Falsum:rest,suc)]
                   _               -> Nothing),
  ("ax", \ (ant,suc) ->
                 case suc of
                   p : suc' | isAtomic p && p `elem` ant -> Just []
                   _                                     -> Nothing)
 ]

g3iLImpl =
    [("L->", \ (ant,suc) -> 
                 case ant of
                   Impl a b : rest -> Just [(Impl a b :rest, [a]), (b:rest,suc)]
                   Neg a    : rest -> Just [(Impl a b :rest, [a]), (b:rest,suc)]
                                                         where b = Falsum
                   _               -> Nothing)]

g4iLImpl =
    [("L0->", \ (ant,suc) -> 
                 case ant of
                   Impl p b : rest | isNotComplex p && p `elem` rest -> 
                               Just [(p : b : rest, suc)]
                   Neg  p   : rest | isNotComplex p && p `elem` rest -> 
                               Just [(p : Falsum : rest, suc)]
                   _     -> Nothing),
     ("L&->", \ (ant,suc) -> 
                 case ant of
                   Impl (Conj c d) b : rest -> 
                               Just [(Impl c (Impl d b) : rest, suc)]
                   Neg  (Conj c d)   : rest -> 
                               Just [(Impl c (Impl d Falsum) : rest, suc)]
                   _               -> Nothing),
     ("Lv->", \ (ant,suc) -> 
                 case ant of
                   Impl (Disj c d) b : rest -> 
                               Just [(Impl c b : Impl d b : rest, suc)]
                   Neg  (Disj c d)   : rest -> 
                               Just [(Impl c Falsum : Impl d Falsum : rest, suc)]
                   _               -> Nothing),
     ("L->->",\ (ant,suc) -> 
                 case ant of
                   Impl (Impl c d) b : rest ->
                          Just [(c : Impl d b : rest, [d]), (b : rest, suc)]
                   Impl (Neg c) b    : rest ->
                          Just [(c : rest, [Falsum]), (b : rest,  suc)]
                   Neg  (Impl c d)   : rest ->
                          Just [(c : Impl d Falsum : rest, [d])]
                   Neg  (Neg c)      : rest ->
                          Just [(c :  rest, suc)]
                   _               -> Nothing)
 ]

g3xqL = 
 [
  ("L/A", \ (ant,suc) -> 
              case ant of
                Univ x a : ant' -> 
                  Just [Left (a' : Univ x a : ant', suc), Right "t"]
                    where a' = substFormula ["t"] substVar [(x,NewMeta "t")] a
                _          -> Nothing),
  ("L/E", \ (ant,suc) -> 
              case ant of
                Exist x a : ant' | notOccur x (ant' ++ suc) -> 
                  Just [Left (a:ant', suc)]   --- A(y/x) pro A ?? 
                _          -> Nothing)
 ]

g3iqR = 
 [("R/A", \ (ant,suc) -> 
              case suc of
                [Univ x a] | notOccur x ant -> 
                  Just [Left (ant, [a])]   --- A(y/x) pro A ??
                _          -> Nothing),
  ("R/E", \ (ant,suc) -> 
              case suc of
                [Exist x a] -> 
                  Just [Left (ant, [a']), Right "t"]
                    where a' = substFormula ["t"] substVar [(x,NewMeta "t")] a
                _          -> Nothing)
 ]

g3cqR = 
 [("R/A", \ (ant,suc) -> 
              case suc of
                Univ x a : suc' | notOccur x (ant ++ suc') -> 
                  Just [Left (ant, a:suc')]   --- A(y/x) pro A ??
                _          -> Nothing),
  ("R/E", \ (ant,suc) -> 
              case suc of
                Exist x a : suc' -> 
                  Just [Left (ant, a' : Exist x a : suc'), Right "t"]
                    where a' = substFormula ["t"] substVar [(x,NewMeta "t")] a
                _          -> Nothing)
 ]

gxeq =
 [
  ("Ref", \ (ant,suc) -> 
             Just [Left (equ (NewMeta "a") (NewMeta "a") : ant, suc), Right "a"]),
  ("Repl", \ (ant,suc) -> 
              case ant of
                Predic "=" [a,b] : p : rest | atomicOn a p -> 
                  Just [Left (atomSubst p a b : ant, suc), Right "a", Right "b"]
                _ -> Nothing)
 ]
  where
   equ a b = Predic "=" [a, b]
   atomicOn a p    = False ---
   atomSubst p a b = p ---