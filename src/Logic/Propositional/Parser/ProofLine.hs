-- | ProofLine.hs

module Logic.Propositional.Parser.ProofLine
  (ProofRef(..),
   ProofLine,
   genProof)
  where

import Logic.Propositional

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
  deriving (Show)

type ProofLine = (Int, (Formula, ProofRef))

duplicates :: Eq a => [a] -> Maybe a
duplicates [] = Nothing
duplicates (x:xs) | x `elem` xs = Just x
                  | otherwise   = duplicates xs

duplicateKeys :: Eq a => [(a, b)] -> Maybe a
duplicateKeys = duplicates . map fst

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
  | otherwise = Left ("Line " ++ show lineNum ++
                      ": reference to non-existent line ")

genProof :: [ProofLine] -> Either String Proof
genProof [] = Left "empty proof"
genProof proofLines =
  case duplicateKeys proofLines of
    Just dup  -> Left $ "duplicate keys: " ++ show dup
    Nothing ->
      genProofFromLine i f f_ref proofLines
      where (i, (f, f_ref)) = last proofLines
