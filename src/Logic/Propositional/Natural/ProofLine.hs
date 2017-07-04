-- | ProofLine.hs

module Logic.Propositional.Natural.ProofLine
  (ProofRef(..),
   ProofLine,
   genProof)
  where

import Logic.Propositional
import Logic.Propositional.Natural

import Data.Maybe
import qualified Data.Set as S

data ProofRef = AssumptionRef
              | AndIntroRef Int Int
              | AndElimLRef Int
              | AndElimRRef Int
              | ImpliesIntroRef Int
              | ImpliesElimRef Int Int
              | OrIntroLRef Int
              | OrIntroRRef Int
              | OrElimRef Int Int Int
              | BottomElimRef Int
              | ExcludedMiddleRef
  deriving (Show)

type ProofLine = (Int, (Formula, ProofRef))

duplicates :: Eq a => [a] -> Maybe a
duplicates [] = Nothing
duplicates (x:xs) | x `elem` xs = Just x
                  | otherwise   = duplicates xs

duplicateKeys :: Eq a => [(a, b)] -> Maybe a
duplicateKeys = duplicates . map fst

type SimpleGraph = [(Int, [Int])]

findCycle :: [Int] -> Int -> SimpleGraph -> Maybe [Int]
findCycle _ _ [] = Nothing
findCycle visitedNodes start graph
  | Just children <- children,
    any (`elem` children) visitedNodes =
      Just visitedNodes
  | Just children <- children,
    (cyc:_) <- (catMaybes . map findCycleChild) children = Just cyc
  | otherwise = Nothing
  where children = lookup start graph
        findCycleChild child = findCycle (child:visitedNodes) child graph

lineToNode :: ProofLine -> (Int, [Int])
lineToNode (l,(_,AssumptionRef)) = (l,[])
lineToNode (l,(_,AndIntroRef x y)) = (l,[x,y])
lineToNode (l,(_,AndElimLRef x)) = (l,[x])
lineToNode (l,(_,AndElimRRef x)) = (l,[x])
lineToNode (l,(_,ImpliesIntroRef x)) = (l,[x])
lineToNode (l,(_,ImpliesElimRef x y)) = (l,[x,y])
lineToNode (l,(_,OrIntroLRef x)) = (l,[x])
lineToNode (l,(_,OrIntroRRef x)) = (l,[x])
lineToNode (l,(_,OrElimRef x y z)) = (l,[x,y,z])
lineToNode (l,(_,BottomElimRef x)) = (l,[x])
lineToNode (l,(_,ExcludedMiddleRef)) = (l,[])

linesToGraph :: [ProofLine] -> SimpleGraph
linesToGraph = map lineToNode

-- We assume there are no cycles.
genProofFromLine :: Int -> Formula -> ProofRef  -> [ProofLine] -> Either String Proof
genProofFromLine lineNum f ref proofLines
  | AssumptionRef <- ref = return $ Assumption f
  | AndIntroRef j k <- ref,
    Just (g, g_ref) <- lookup j proofLines,
    Just (h, h_ref) <- lookup k proofLines =
      do g_proof <- genProofFromLine j g g_ref proofLines
         h_proof <- genProofFromLine k h h_ref proofLines
         return $ AndIntro f g_proof h_proof
  | AndElimLRef j <- ref,
    Just (g, g_ref) <- lookup j proofLines =
      do g_proof <- genProofFromLine j g g_ref proofLines
         return $ AndElimL f g_proof
  | AndElimRRef j <- ref,
    Just (g, g_ref) <- lookup j proofLines =
      do g_proof <- genProofFromLine j g g_ref proofLines
         return $ AndElimR f g_proof
  | ImpliesIntroRef j <- ref,
    Just (g, g_ref) <- lookup j proofLines =
      do g_proof <- genProofFromLine j g g_ref proofLines
         return $ ImpliesIntro f g_proof
  | ImpliesElimRef j k <- ref,
    Just (g, g_ref) <- lookup j proofLines,
    Just (h, h_ref) <- lookup k proofLines =
      do g_proof <- genProofFromLine j g g_ref proofLines
         h_proof <- genProofFromLine k h h_ref proofLines
         return $ ImpliesElim f g_proof h_proof
  | OrIntroLRef j <- ref,
    Just (g, g_ref) <- lookup j proofLines =
      do g_proof <- genProofFromLine j g g_ref proofLines
         return $ OrIntroL f g_proof
  | OrIntroRRef j <- ref,
    Just (g, g_ref) <- lookup j proofLines =
      do g_proof <- genProofFromLine j g g_ref proofLines
         return $ OrIntroR f g_proof
  | OrElimRef j k l <- ref,
    Just (g, g_ref) <- lookup j proofLines,
    Just (h, h_ref) <- lookup k proofLines,
    Just (i, i_ref) <- lookup l proofLines =
      do g_proof <- genProofFromLine j g g_ref proofLines
         h_proof <- genProofFromLine k h h_ref proofLines
         i_proof <- genProofFromLine l i i_ref proofLines
         return $ OrElim f g_proof h_proof i_proof
  | BottomElimRef j <- ref,
    Just (g, g_ref) <- lookup j proofLines =
      do g_proof <- genProofFromLine j g g_ref proofLines
         return $ BottomElim f g_proof
  | ExcludedMiddleRef <- ref = return $ ExcludedMiddle f
  | otherwise = Left ("Line " ++ show lineNum ++
                      ": reference to non-existent line ")

genProof :: [ProofLine] -> Either String Proof
genProof [] = Left "empty proof"
genProof proofLines = do
  case duplicateKeys proofLines of
    Just dup  -> Left $ "duplicate keys: " ++ show dup
    Nothing ->
      case findCycle [] i (linesToGraph proofLines) of
        Just cycle -> Left $ "cyclic dependencies: " ++ show cycle
        Nothing -> genProofFromLine i f f_ref proofLines
      where (i, (f, f_ref)) = last proofLines
