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

genProofFromLine :: Formula -> ProofRef  -> [ProofLine] -> Either String Proof
genProofFromLine f AssumptionRef _
  = Right $ Assumption f
genProofFromLine f (AndIntroRef j k) proofLines =
  case lookup j proofLines of
    Nothing -> Left $ "reference to nonexistent line " ++ show j
    Just (g, g_ref) ->
      case lookup k proofLines of
        Nothing -> Left $ "reference to nonexistent line " ++ show k
        Just (h, h_ref) ->
          do g_proof <- genProofFromLine g g_ref proofLines
             h_proof <- genProofFromLine h h_ref proofLines
             return $ AndIntro f g_proof h_proof
genProofFromLine f (AndElimLRef j) proofLines =
  case lookup j proofLines of
    Nothing -> Left $ "reference to nonexistent line " ++ show j
    Just (g, g_ref) ->
      do g_proof <- genProofFromLine g g_ref proofLines
         return $ AndElimL f g_proof
genProofFromLine f (AndElimRRef j) proofLines =
  case lookup j proofLines of
    Nothing -> Left $ "reference to nonexistent line " ++ show j
    Just (g, g_ref) ->
      do g_proof <- genProofFromLine g g_ref proofLines
         return $ AndElimR f g_proof
genProofFromLine f (ImpliesIntroRef j) proofLines =
  case lookup j proofLines of
    Nothing -> Left $ "reference to nonexistent line " ++ show j
    Just (g, g_ref) ->
      do g_proof <- genProofFromLine g g_ref proofLines
         return $ ImpliesIntro f g_proof
genProofFromLine f (ImpliesElimRef j k) proofLines =
  case lookup j proofLines of
    Nothing -> Left $ "reference to nonexistent line " ++ show j
    Just (g, g_ref) ->
      case lookup k proofLines of
        Nothing -> Left $ "reference to nonexistent line " ++ show k
        Just (h, h_ref) ->
          do g_proof <- genProofFromLine g g_ref proofLines
             h_proof <- genProofFromLine h h_ref proofLines
             return $ ImpliesElim f g_proof h_proof
genProofFromLine f (OrIntroLRef j) proofLines =
  case lookup j proofLines of
    Nothing -> Left $ "reference to nonexistent line " ++ show j
    Just (g, g_ref) ->
      do g_proof <- genProofFromLine g g_ref proofLines
         return $ OrIntroL f g_proof
genProofFromLine f (OrIntroRRef j) proofLines =
  case lookup j proofLines of
    Nothing -> Left $ "reference to nonexistent line " ++ show j
    Just (g, g_ref) ->
      do g_proof <- genProofFromLine g g_ref proofLines
         return $ OrIntroR f g_proof
genProofFromLine f (OrElimRef j k l) proofLines =
  case lookup j proofLines of
    Nothing -> Left $ "reference to nonexistent line " ++ show j
    Just (g, g_ref) ->
      case lookup k proofLines of
        Nothing -> Left $ "reference to nonexistent line " ++ show k
        Just (h, h_ref) ->
          case lookup l proofLines of
            Nothing -> Left $ "reference to nonexistent line " ++ show l
            Just (i, i_ref) ->
              do g_proof <- genProofFromLine g g_ref proofLines
                 h_proof <- genProofFromLine h h_ref proofLines
                 i_proof <- genProofFromLine i i_ref proofLines
                 return $ OrElim f g_proof h_proof i_proof
genProofFromLine f (BottomElimRef j) proofLines =
  case lookup j proofLines of
    Nothing -> Left $ "reference to nonexistent line " ++ show j
    Just (g, g_ref) ->
      do g_proof <- genProofFromLine g g_ref proofLines
         return $ BottomElim f g_proof

genProof :: [ProofLine] -> Either String Proof
genProof [] = Left "empty proof"
genProof proofLines =
  case duplicateKeys proofLines of
    Just i  -> Left $ "duplicate keys: " ++ show i
    Nothing ->
      genProofFromLine f f_ref proofLines
      where (f, f_ref) = (snd . last) proofLines
