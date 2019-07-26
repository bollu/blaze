{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where
import GHC.Stack
import Data.Maybe (catMaybes)
import Data.List (nub, sortOn, sortBy)
import Data.Bits
import Data.SBV
import Data.SBV.Internals (CV)
import Data.Word
import Control.Monad
import System.Random
import Control.Applicative
import Control.Monad.State
import Control.Monad.Fail
import Debug.Trace

-- | provide a random integer in [lo, hi]
randint :: (Int, Int) -> IO Int
randint (lo, hi) = liftIO $ getStdRandom $ randomR (lo, hi)

randint8 :: IO Int8
randint8 = liftIO $ getStdRandom $ randomR (-128, 127)

-- | random uniform float
randfloat :: (Float, Float) -> IO Float
randfloat (lo, hi) = liftIO $ getStdRandom $ randomR (lo, hi)

randbool :: IO Bool
randbool = getStdRandom $ random

data Inst = IPush Int8 | IAdd | IMul | IDup | IAnd | ISwap deriving(Eq, Show, Ord)
data Program = Program { progNParams :: Int, progInsts :: [Inst] }
  deriving (Eq, Ord)

instance Show Program where
  show (Program nparams insts) =
     "(" <> "nparams: " <> show nparams <> " | " <> show insts <> ")"

randInst :: IO Inst
randInst = do
  r <- randint (1, 6)
  case r of
    1 -> IPush <$> randint8
    2 -> pure $ IAdd
    3 -> pure $ IMul
    4 -> pure $ IDup
    5 -> pure $ IAnd
    6 -> pure $ ISwap


-- | drop a list element at the specified indeces (inclusive)
dropListElems :: [a] -> Int -> Int -> [a]
dropListElems as ixbegin ixend = take ixbegin as ++ drop (ixend + 1) as

-- | replace a list element at the specified index
replaceListElem :: [a] -> Int -> a -> [a]
replaceListElem as ix a = take ix as ++ [a] ++ drop (ix+1) as

-- | add to a list *after* the specified index
addListElem :: [a] -> Int -> a -> [a]
addListElem as ix a = take ix as ++ [a] ++ drop ix as


-- | Edit the program by a single instruction. Add, modify, or delete
-- an instruction.
perturbProgram :: Program -> IO Program
perturbProgram Program{..} = do
  r <- randint (1, 3)
  ix <- randint (0, length progInsts - 1)
  ix' <- randint (ix, length progInsts - 1)
  progInsts <- case r of
                 1 -> pure $ dropListElems progInsts ix ix'
                 2 -> replaceListElem progInsts ix <$> randInst
                 3 -> addListElem progInsts ix <$> randInst

  return $ Program{..}

interpInst :: Num a => Bits a =>  [a] -> Inst -> Maybe [a]
interpInst as (IPush x) = Just $ (fromIntegral x):as
interpInst (a:a':as) (IAdd) = Just $ (a+a':as)
interpInst (a:a':as) (IMul) = Just $ (a*a':as)
interpInst (a:as) (IDup) = Just $ (a:a:as)
interpInst (a:a':as)(IAnd) = Just $ (a .&. a':as)
interpInst (a:a':as) (ISwap) = Just $ (a':a:as)
interpInst _ _ = Nothing

costInst :: Inst -> Float
costInst (IPush _) = 1
costInst IAdd = 1
costInst IMul = 4
costInst IDup = 1
costInst IAnd = 1
costInst ISwap = 1

costProgram :: Program -> Float
costProgram p = sum $ map costInst $  progInsts p

interpInsts :: Num a => Bits a => [Inst] -> [a] -> Maybe a
interpInsts insts as =
  case foldM interpInst as insts of
    Just [a] -> Just a
    _ -> Nothing

-- | Create a boolean that can be SAT checked
smtQueryEquivProgram :: Program -> Program -> Symbolic SBool
smtQueryEquivProgram p1 p2 = do
  if progNParams p1 /= progNParams p2
  then return $ 1 .== (0 :: SInt8)
  else do
    params <- sequence $ [forall $ "p-" <> show i | i <- [1..progNParams p1]]
    let ms1 = interpInsts (progInsts p1) params :: Maybe SInt8
    let ms2 = interpInsts (progInsts p1) params :: Maybe SInt8
    case liftA2 (,) ms1 ms2 of
      Nothing -> return $ 1 .== (0 :: SInt8)
      Just (s1, s2) -> return $ s1 .== s2

proportionAgreeingRunsPrograms :: Program -> Program -> IO Float
proportionAgreeingRunsPrograms p1 p2 = do
  if progNParams p1 /= progNParams p2
  then return 0
  else do
    let nruns = 10
    scores <- replicateM nruns $ do
      ps <- replicateM (progNParams p1) randint8
      let l = interpInsts (progInsts p1) ps
      let r = interpInsts (progInsts p2) ps
      return $ if l == r then 1 else 0
    return $ fromIntegral (sum scores) / fromIntegral nruns

type Score = Float

-- | Higher score is better.
scoreProgram :: Program -> Program -> IO Score
scoreProgram pc ps = do
  nagree <- proportionAgreeingRunsPrograms pc ps
  if nagree /= 1.0
  then return $ 0.1 + nagree
  else do
    res <- sat $ setTimeOut 100 >> smtQueryEquivProgram pc ps
    if not $ modelExists res
    then return $ 0.1 + nagree
    else return $ 2.0 + 2.0 ** (-1.0 * costProgram ps)

-- | Take a step of metropolois hastings
mhStepProgram :: Program -- ^ ground truth (concrete)
              -> (Score, Program) -- ^ current position
              -> IO (Score, Program) -- ^ next position
mhStepProgram pc (score, ps) = do
  ps' <- perturbProgram ps
  score' <- scoreProgram pc ps'
  let accept = score' / score
  r <- randfloat (0, 1)
  pure $ if r < accept then (score', ps') else (score, ps)


mRepeat :: Monad m => Int -> (a -> m a) -> (a -> m a)
mRepeat 0 _ = pure
mRepeat n f = f >=> mRepeat (n - 1) f

-- | Return the trace of programs seen and their scores
mhTrace :: Int -- ^ number of samples
        -> Program -- ^ programs
        -> IO [(Score, Program)] -- ^ scores
mhTrace n pc =
  let nsteps = 10
      -- go :: Int -> (Score, Program) -> M (Score, Program)
      go 0 (s, p) = pure [(s, p)]
      go n (s, p) = do
                      (s', p') <- mRepeat nsteps (mhStepProgram pc) $ (s, p)
                      rest <- go (n - 1) (s', p')
                      return $ (s', p'):rest
  in do
    let beginp = pc
    s <- scoreProgram pc beginp
    go n (s, beginp)

optimiseProgram :: Program -> IO ()
optimiseProgram pc = do
  liftIO $ putStrLn $ "*** original: " <> show pc <> "***"
  steps <- mhTrace 1000 pc
  let descendingScore (s, _) (s', _) = compare s' s
  let opts = take 4 $ nub $
        sortBy descendingScore [(s, p) | (s, p) <- steps, s >= 2.0]
  forM_ opts $ \(s, p) -> do
    liftIO $ putStrLn $ show (progInsts p) <> " | " <> "score: " <> show s


mainInsts :: IO ()
mainInsts = do
  optimiseProgram $ Program 0 [IPush 2, IPush 3, IAdd]
  optimiseProgram $ Program 1 [IPush 2, IMul]
  optimiseProgram $ Program 1 [IDup, IAnd]

-- main = mainExpr
main :: IO ()
main = mainInsts
