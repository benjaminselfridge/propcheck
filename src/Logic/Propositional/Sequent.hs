-- | Logic.Propositional.Sequent

module Logic.Propositional.Sequent
  ( Sequent(..)
  , printTheorem
  , printTheoremAndProof
  , ppTheoremAndProof
  , ppTheoremAndProofReverse
  ) where

import Logic.Propositional

import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Set as S

data Sequent = S.Set Formula :- S.Set Formula

lefts  (ls: _) = ls
rights ( _:rs) = rs

showFormulas :: S.Set Formula -> String
showFormulas = intercalate ", " . map show . S.toList

instance Show Sequent where
  show (ls :- rs)
    | S.null ls && S.null rs = ":-"
    | S.null ls = ":- " ++ showFormulas rs
    | S.null rs = showFormulas ls ++ " :-"
    | otherwise = showFormulas ls ++ " :- " ++ showFormulas rs

infix 0 :-

data Proof = Axiom Sequent
           | RAnd Sequent Proof Proof
           | ROr Sequent Proof
           | RImplies Sequent Proof
           | RBottom Sequent Proof
           | LAnd Sequent Proof
           | LOr Sequent Proof Proof
           | LImplies Sequent Proof Proof
           | LBottom Sequent Proof

conclusion :: Proof -> Sequent
conclusion (Axiom    s    ) = s
conclusion (RAnd     s _ _) = s
conclusion (ROr      s   _) = s
conclusion (RImplies s   _) = s
conclusion (LAnd     s   _) = s
conclusion (LOr      s _ _) = s
conclusion (LImplies s _ _) = s
conclusion (LBottom  s   _) = s

prove :: Sequent -> Either Assignment Proof
prove (ls :- rs)
  | (f@(And g h):_) <- filter isAnd (S.toList rs) =
      do g_proof <- prove (ls :- S.insert g (S.delete f rs))
         h_proof <- prove (ls :- S.insert h (S.delete f rs))
         return $ RAnd (ls :- rs) g_proof h_proof
  | (f@(Or g h):_) <- filter isOr (S.toList rs) =
      do gh_proof <- prove (ls :- S.union (S.fromList [g,h]) (S.delete f rs))
         return $ ROr (ls :- rs) gh_proof
  | (f@(Implies g h):_) <- filter isImplies (S.toList rs) =
      do gh_proof <- prove (S.insert g ls :- S.insert h (S.delete f rs))
         return $ RImplies (ls :- rs) gh_proof
  | (f@Bottom:_) <- filter isBottom (S.toList rs) =
      do nof_proof <- prove (ls :- S.delete f rs)
         return $ RBottom (ls :- rs) nof_proof
  | (f@(And g h):_) <- filter isAnd (S.toList ls) =
      do gh_proof <- prove (S.union (S.fromList [g,h]) (S.delete f ls) :- rs)
         return $ LAnd (ls :- rs) gh_proof
  | (f@(Or g h):_) <- filter isOr (S.toList ls) =
      do g_proof <- prove (S.insert g (S.delete f ls) :- rs)
         h_proof <- prove (S.insert h (S.delete f ls) :- rs)
         return $ LOr (ls :- rs) g_proof h_proof
  | (f@(Implies g h):_) <- filter isImplies (S.toList ls) =
      do g_proof <- prove (S.delete f ls :- S.insert g rs)
         h_proof <- prove (S.insert h (S.delete f ls) :- rs)
         return $ LImplies (ls :- rs) g_proof h_proof
  | (Bottom:_) <- filter isBottom (S.toList ls) = return $ Axiom (ls :- rs)
  | otherwise = if S.null (S.intersection ls rs)
                then Left $ counterExample (S.toList ls) (S.toList rs)
                else return $ Axiom (ls :- rs)
  where isAnd     f = case f of (And     _ _) -> True; _ -> False
        isOr      f = case f of (Or      _ _) -> True; _ -> False
        isImplies f = case f of (Implies _ _) -> True; _ -> False
        isBottom  f = case f of  Bottom       -> True; _ -> False

counterExample :: [Formula] -> [Formula] -> Assignment
counterExample (Var x:fs) gs = (x, True)  : counterExample fs gs
counterExample [] (Var y:gs) = (y, False) : counterExample [] gs
counterExample []         [] = []
counterExample _ _ = error "called counterExample on sequent with non-variable"

showProof :: String -> Proof -> String
showProof pad (Axiom s) = pad ++ show s ++ " [Axiom]"
showProof pad (RAnd s p1 p2) =
  pad ++ show s ++ " [RAnd]\n" ++
  showProof (pad++"  ") p1 ++ "\n" ++ 
  showProof (pad++"  ") p2
showProof pad (ROr s p) =
  pad ++ show s ++ " [ROr]\n" ++
  showProof (pad++"  ") p
showProof pad (RImplies s p) =
  pad ++ show s ++ " [RImplies]\n" ++
  showProof (pad++"  ") p
showProof pad (RBottom s p) =
  pad ++ show s ++ " [RBottom]\n" ++
  showProof (pad++"  ") p
showProof pad (LAnd s p) =
  pad ++ show s ++ " [LAnd]\n" ++
  showProof (pad++"  ") p
showProof pad (LOr s p1 p2) =
  pad ++ show s ++ " [LOr]\n" ++
  showProof (pad++"  ") p1 ++ "\n" ++
  showProof (pad++"  ") p2
showProof pad (LImplies s p1 p2) =
  pad ++ show s ++ " [LImplies]\n" ++
  showProof (pad++"  ") p1 ++ "\n" ++
  showProof (pad++"  ") p2
showProof pad (LBottom s p) =
  pad ++ show s ++ " [LBottom]\n" ++
  showProof (pad++"  ") p

instance Show Proof where
  show = showProof ""

printTheorem :: Formula -> String
printTheorem f = case prove (S.fromList [] :- S.fromList [f]) of
  Left  _ -> show f ++ " is not a theorem."
  Right _ -> show f ++ " is a theorem."

printTheoremAndProof :: Formula -> String
printTheoremAndProof f = case prove (S.fromList [] :- S.fromList [f]) of
  Left  a -> show f ++ " is not a theorem.\n" ++
             "Counterexample:\n" ++ pad 2 0 (showAssignment a)
  Right p -> show f ++ " is a theorem.\n" ++
             "Proof:\n" ++ (show p)

-- | Pretty printing

stringWidth :: String -> Int
stringWidth = maximum . map length . lines

coLines :: [String] -> [String] -> ([String], [String])
coLines (x1:x2:xs) (y1:y2:ys) =
  let (xs',ys') = coLines (x2:xs) (y2:ys) in (x1:xs',y1:ys')
coLines (x1:[])    (y1:y2:ys) =
  let (xs',ys') = coLines [replicate (length x1) ' '] (y2:ys)
  in (x1:xs',y1:ys')
coLines (x1:x2:xs)    (y1:[]) =
  let (xs',ys') = coLines (x2:xs) [replicate (length y1) ' ']
  in (x1:xs',y1:ys')
coLines (x:[]) (y:[]) = ([x],[y])
coLines _ _ = error "coLines called with two empty arguments"

spliceLines :: String -> String -> String
spliceLines s1 s2 = unlines $ zipWith spliceLine lines1 lines2
  where spliceLine s1 s2 = s1 ++ " | " ++ s2
        (lines1, lines2) = coLines (lines s1) (lines s2)

padLine :: Int -> Int -> String -> String
padLine i j s = replicate i ' ' ++ s ++ replicate j ' '

pad :: Int -> Int -> String -> String
pad i j = unlines . map (padLine i j) . lines

ppProofStep :: String -> String -> String
ppProofStep ppSeq ppPf =
  let seqWidth = stringWidth ppSeq
      ppPfWidth = stringWidth ppPf
      totalWidth = max seqWidth ppPfWidth
      seqPadL = (totalWidth - seqWidth) `div` 2
      seqPadR = totalWidth - (seqPadL + seqWidth)
      pfPadL = (totalWidth - ppPfWidth) `div` 2
      pfPadR = totalWidth - (pfPadL + ppPfWidth)
  in pad seqPadL seqPadR ppSeq ++
--     replicate totalWidth '-' ++ "\n" ++
     pad seqPadL seqPadR (replicate seqWidth '-') ++
     pad pfPadL pfPadR ppPf  

ppProof :: Proof -> String
ppProof (Axiom seq) =
  let ppSeq = show seq
      seqWidth = stringWidth ppSeq
  in ppSeq ++ "\n" ++ replicate seqWidth '-' ++ "\n"
ppProof (RAnd seq pf1 pf2) =
  ppProofStep (show seq) (spliceLines (ppProof pf1) (ppProof pf2))
ppProof (ROr seq pf) = ppProofStep (show seq) (ppProof pf)
ppProof (RImplies seq pf) = ppProofStep (show seq) (ppProof pf)
ppProof (RBottom seq pf) = ppProofStep (show seq) (ppProof pf)
ppProof (LAnd seq pf) = ppProofStep (show seq) (ppProof pf)
ppProof (LOr seq pf1 pf2) =
  ppProofStep (show seq) (spliceLines (ppProof pf1) (ppProof pf2))
ppProof (LImplies seq pf1 pf2) =
  ppProofStep (show seq) (spliceLines (ppProof pf1) (ppProof pf2))
ppProof (LBottom seq pf) = ppProofStep (show seq) (ppProof pf)

reverseLines :: String -> String
reverseLines = unlines . reverse . lines

ppProofReverse :: Proof -> String
ppProofReverse = reverseLines . ppProof

ppTheoremAndProof :: Formula -> String
ppTheoremAndProof f = case prove (S.fromList [] :- S.fromList [f]) of
  Left a -> show f ++ " is not a theorem.\n" ++
            "Counterexample:\n" ++ pad 2 0 (showAssignment a)
  Right p -> "Theorem: " ++ show f ++ "\n" ++
             "Proof:\n" ++ ppProof p

ppTheoremAndProofReverse :: Formula -> String
ppTheoremAndProofReverse f = case prove (S.fromList [] :- S.fromList [f]) of
  Left a -> show f ++ " is not a theorem.\n" ++
            "Counterexample:\n" ++ pad 2 0 (showAssignment a)
  Right p -> "Theorem: " ++ show f ++ "\n" ++
             "Proof:\n" ++ ppProofReverse p
