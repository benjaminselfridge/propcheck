module Main where

import Logic.Propositional
import Logic.Propositional.Parser

import Control.Lens
import Control.Monad
import System.Console.CmdArgs.Explicit
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO

-- | Action to perform when running
data Action
  = Check
  | CheckWithProof
  | PrintRules
  | SampleProof
  | ShowHelp
  | ShowVersion

-- | Command line arguments.
data Args = Args { _checkAction :: !Action
                 , _proofPath   :: !FilePath
                 }

-- | Action to perform when running
checkAction :: Simple Lens Args Action
checkAction = lens _checkAction (\s v -> s { _checkAction = v })

proofPath :: Simple Lens Args FilePath
proofPath = lens _proofPath (\s v -> s { _proofPath = v })

-- | Initial arguments if nothing is specified.
defaultArgs :: Args
defaultArgs = Args { _checkAction = Check
--                     _checkWithProofAction = Check
                   , _proofPath = ""
                   }

-- | Flags.

checkWithProofFlag :: Flag Args
checkWithProofFlag = flagNone [ "proof", "p" ] upd help
  where upd = checkAction .~ CheckWithProof
        help = "Show the parsed proof along with the theorem."

printRulesFlag :: Flag Args
printRulesFlag = flagNone [ "rules" ] upd help
  where upd = checkAction .~ PrintRules
        help = "Print the complete list of derivation rules \
               \that can be used in a proof. Use this flag \
               \in conjunction with --sample to figure out \
               \the correct format for writing proof files."

sampleProofFlag :: Flag Args
sampleProofFlag = flagNone [ "sample", "s" ] upd help
  where upd = checkAction .~ SampleProof
        help = "Print a sample proof to stdout. To test this, \
               \redirect the file to a file with > sample.pf \
               \and run `check sample.pf`."

arguments :: Mode Args
arguments = mode "check" defaultArgs help filenameArg flags
  where help = checkVersion ++ "\n" ++ copyrightNotice
        flags = [ checkWithProofFlag
                , printRulesFlag
                , sampleProofFlag
                , flagHelpSimple (checkAction .~ ShowHelp)
                , flagVersion (checkAction .~ ShowVersion)
                ]

-- printProofFlag :: Flag Args
-- printProofFlag = flagNone [ "proof", "p" ] upd help
--   where upd  = checkAction 

checkVersion :: String
checkVersion = "PropCheck propositional logic checker (check) " ++
               versionString ++ ", June 2017."
  where versionString = "0.0.1"

copyrightNotice :: String
copyrightNotice = "Copyright 2017 Ben Selfridge. All rights reserved."

filenameArg :: Arg Args
filenameArg = Arg { argValue = setFilename
                  , argType = "[FILE]"
                  , argRequire = False
                  }
  where setFilename :: String -> Args -> Either String Args
        setFilename nm a = Right (a & proofPath .~ nm)


getCommandLineArgs :: IO Args
getCommandLineArgs = do
  argStrings <- getArgs
  case process arguments argStrings of
    Left msg -> do
      hPutStrLn stderr msg
      exitFailure
    Right v -> return v

-- | Execution.

check :: FilePath -> IO ()
check path = do
  when (null path) $ do
    hPutStrLn stderr "Please specify a path."
    hPutStrLn stderr "For help on using check, run \"check --help\"."
    exitFailure
  proofString <- readFile path
  case parseProof proofString of
    Left e -> putStrLn e
    Right proof -> putStrLn $ ppTheorem proof


checkWithProof :: FilePath -> IO ()
checkWithProof path = do
  when (null path) $ do
    hPutStrLn stderr "Please specify a path."
    hPutStrLn stderr "For help on using check, run \"check --help\"."
    exitFailure
  proofString <- readFile path
  case parseProof proofString of
    Left e -> putStrLn e
    Right proof -> putStrLn $ ppTheoremAndProof proof

sampleProofFile :: String
sampleProofFile =
  "-- Here is a simple proof of transitivity. Also, this is a comment!\n\
  \\n\
  \-- Every proof starts with the keyword \"Proof.\"\n\
  \Proof.\n\
  \\n\
  \-- Next, we list the steps of our proof. You can use any order of\n\
  \-- numbers that you want, but make sure there are no duplicates.\n\
  \\n\
  \1. a => b [Assumption]\n\
  \2. b => c [Assumption]\n\
  \3. a [Assumption]\n\
  \4. b [ImpliesElim 3 1]\n\
  \5. c [ImpliesElim 4 2]\n\
  \\n\
  \-- The last statement in a proof is taken as the conclusion by default.\n\
  \6. a => c [ImpliesIntro 5]\n\
  \\n\
  \-- Our proof is complete!\n\
  \QED\n"

sampleProof :: IO ()
sampleProof = putStr sampleProofFile

assumptionSummary :: String
assumptionSummary =
  "-- Rule of assumption --\n\
  \\n\
  \Format: <formula> [Assumption]\n\
  \\n\
  \The rule of assumption allows the introduction of any hypothesis, with\n\
  \the implicit cost that unless it is discharged at a later point in the\n\
  \proof, it will appear as a top-level hypothesis. This rule requires no\n\
  \references to any other lines in a proof."

andIntroSummary :: String
andIntroSummary =
  "-- Rule of and introduction --\n\
  \\n\
  \Format: f & g [AndIntro i j]\n\
  \\n\
  \        (where line i has conclusion f,\n\
  \line j has conclusion g)\n\
  \\n\
  \The rule of and introduction allows the introduction of a new formula,\n\
  \f & g, given two references, i and j, to lines in the proof concluding\n\
  \f and g respectively."

andElimSummary :: String
andElimSummary =
  "-- Rule of and elimination --\n\
  \\n\
  \Formats: f [AndElimL i]\n\
  \         g [AndElimR i]\n\
  \\n\
  \         (where line i has conclusion f & g for some formula g)\n\
  \\n\
  \The rules of and elimination allow us to conclude formulas f and g,\n\
  \given a reference i to a line in the proof concluding f & g."

impliesIntroSummary :: String
impliesIntroSummary =
  "-- Rule of implies introduction --\n\
  \\n\
  \Format: f => g [ImpliesIntro i]\n\
  \\n\
  \        (where line i has conclusion g)\n\
  \\n\
  \The rule of implies introduction allows us conclude f => g, given a\n\
  \reference i to a line in the proof concluding g. This rule has the\n\
  \benefit of discharging the assumption f, wherever it may occur in the\n\
  \proof tree of the formula f => g. Note that if thep assumption f is\n\
  \used elsewhere in the proof, outside the scope of this formula, then\n\
  \it may still appear as a top-level assumption."

impliesElimSummary :: String
impliesElimSummary =
  "-- Rule of implies elimination --\n\
  \\n\
  \Format: f [ImpliesElim i j]\n\
  \\n\
  \        (where line i has conclusion g for some formula g,\n\
  \               line j has conclusion g => f)\n\
  \\n\
  \The rule of implies elimination (or modus ponens) allows us to\n\
  \conclude a formula f, given two references, i and j, to lines in the\n\
  \proof concluding g and g => f, respectively, where g can be any\n\
  \formula."

orIntroSummary :: String
orIntroSummary =
  "-- Rule of or introduction --\n\
  \\n\
  \Formats: f | g [OrIntroL i]\n\
  \         f | g [OrIntroR j]\n\
  \\n\
  \         (where line i has conclusion f,\n\
  \             or line j has conclusion g)\n\
  \\n\
  \The rule of or introduction allows the introduction of a new formula,\n\
  \f | g, given a reference i (j) to a line in the proof concluding f\n\
  \(g)."

orElimSummary :: String
orElimSummary =
  "-- Rule of or elimination --\n\
  \\n\
  \Format: f [OrElim i j k]\n\
  \\n\
  \        (where line i has conclusion g | h for some formulas g and h,\n\
  \               line j has conclusion f,\n\
  \               line k has conclusion f)\n\
  \\n\
  \The rule of or elimination allows us to conclude a formula f, given\n\
  \three references, i, j, and k, to lines in the proof concluding g | h,\n\
  \f, and f, respectively. This rule has the benefit of discharging the\n\
  \assumption g in the proof of line j, along with the assumption h in\n\
  \the proof of line k. Note that if these assumptions are used elsewhere\n\
  \in the proof, outside the scope of those respective formulas, then\n\
  \they may still appear as top-level assumptions."

bottomElimSummary :: String
bottomElimSummary =
  "-- Rule of bottom elimination --\n\
  \\n\
  \Formats: f [BottomElim i]\n\
  \\n\
  \         (where line i has conclusion _|_)\n\
  \\n\
  \THe rule of bottom elimination (or absurdity) allows us to conclude\n\
  \any formula f, given a reference to a proof i concluding _|_\n\
  \(bottom)."

excludedMiddleSummary :: String
excludedMiddleSummary =
  "-- Rule of excluded middle --\
  \\n\
  \Formats: f | !f [ExcludedMiddle]\n\
  \\n\
  \The rule of excluded middle takes constructive logic and turns it into\n\
  \classical logic, where every statement is either true or false. It\n\
  \says that for any formula f, it is either true or it is false. This is\n\
  \a very powerful law, because it always permits us to case split on the\n\
  \truth or falsehood of any particular statement. This enables us to do\n\
  \proofs by contradiction; without this law, we couldn't prove\n\
  \DeMorgan's laws, Peirce's laws, and a number of other intuitively\n\
  \clear formulas.\n"

allRuleSummaries :: String
allRuleSummaries =
  assumptionSummary   ++ "\n\n" ++
  andIntroSummary     ++ "\n\n" ++
  andElimSummary      ++ "\n\n" ++
  impliesIntroSummary ++ "\n\n" ++
  impliesElimSummary  ++ "\n\n" ++
  orIntroSummary      ++ "\n\n" ++
  orElimSummary       ++ "\n\n" ++
  bottomElimSummary   ++ "\n\n" ++
  excludedMiddleSummary

printAllRuleSummaries :: IO ()
printAllRuleSummaries = putStr allRuleSummaries

ruleList :: String
ruleList =
  "Complete list of rules:\n\
  \\n\
  \  Assumption\n\
  \  AndIntro\n\
  \  AndElimL\n\
  \  AndElimR\n\
  \  ImpliesIntro\n\
  \  ImpliesElim\n\
  \  OrIntro\n\
  \  OrElim\n\
  \  BottomElim\n"

main :: IO ()
main = do
  args <- getCommandLineArgs
  case args^.checkAction of
    Check -> do
      check (args^.proofPath)
    CheckWithProof -> do
      checkWithProof (args^.proofPath)
    PrintRules -> printAllRuleSummaries
    SampleProof -> sampleProof
    ShowHelp ->
      print $ helpText [] HelpFormatDefault arguments
    ShowVersion ->
      putStrLn (modeHelp arguments)
