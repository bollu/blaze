{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where
import GHC.Stack
import Data.Maybe (catMaybes)
import Data.List (nub, sortOn)
-- | Here, we consider a small implementation of the
-- STOKE paper, where we stochastically optimise over a
-- large space of programs.
import Data.SBV
import Data.SBV.Internals (CV)
import Data.Word
import Control.Monad
import System.Random
-- | for MCMC
import Control.Applicative
import Control.Monad.State
import Control.Monad.Fail

import Control.Monad.Writer
import Control.Monad.Except
import Control.Monad.Identity
import qualified Data.Map as M
import Debug.Trace

-- | unique labels
type Uniq = Int
--
-- | Global state
data G = G { guniq :: Uniq }

-- | Top level monad all our computations run in
type M a =  StateT G IO a

-- | execute a computation inside our `M`
evalM :: M a -> IO a
evalM ma = evalStateT ma (G 0)

debug :: String -> M ()
debug s = liftIO $ putStrLn $ " >" <> s


-- | Parameter
type Param = String


-- | Expressions
data Expr = EVal Int8
          | ESym String
          | EParam Param
          | EAdd Expr Expr
          | EMul Expr Expr
          | ELt Expr Expr
          | EIte Expr Expr Expr deriving(Eq, Ord)

instance Show Expr where
  show (EVal a)=  show a
  show (ESym a)= "s-" <> a
  show (EParam a) = "p-" <> a
  show (EAdd e e') = "(+ " <> show e <> " " <> show e' <> ")"
  show (EMul e e') = "(* " <> show e <> " " <> show e' <> ")"
  show (ELt e e') = "(< " <> show e <> " " <> show e' <> ")"
  show (EIte i t e) = "(ite " <> " " <> show i <> " " <> show t <> " " <> show e <> ")"


type Env = M.Map String SInt8
compileToSBV :: HasCallStack => Env -> Expr -> Symbolic (SInt8, Env)
compileToSBV m (EVal v) = return $ (fromIntegral v, m)
compileToSBV m (ESym name) =
  case m M.!? name of
    Just sym -> return (sym, m)
    Nothing -> do
      sym <- exists name
      return $ (sym, M.insert name sym m)

compileToSBV m (EParam name) = do
  case m M.!? name of
    Just sym -> return (sym, m)
    Nothing -> do
      sym <- forall name
      return $ (sym, M.insert name sym m)

compileToSBV m (EAdd e e') = do
  (e, m) <- (compileToSBV m e)
  (e', m) <- (compileToSBV m e')
  return $ (e + e', m)

compileToSBV m (EMul e e') = do
  (e, m) <- (compileToSBV m e)
  (e', m) <- (compileToSBV m e')
  return $ ( e * e', m)

compileToSBV m (ELt e e') = do
  (e, m) <- (compileToSBV m e)
  (e', m) <- (compileToSBV m e')
  return $ (ite (e .< e') 1 0, m)

compileToSBV m (EIte i t e) = do
  (i, m) <- (compileToSBV m i)
  (t, m) <- (compileToSBV m t)
  (e, m) <- (compileToSBV m e)
  return $ (ite  (i .== 1) t e, m)

-- | Return the computational cost of the expr
costExpr :: HasCallStack => Expr -> Float
costExpr (EAdd e e') = 1 + costExpr e + costExpr e'
costExpr (EMul e e') = 4 + costExpr e + costExpr e'
costExpr (EVal _) = 0
costExpr (ESym _) = 0
costExpr (EParam _) = 0
costExpr (ELt e e') = 1 + costExpr e + costExpr e'

-- | generate a unique label
genuniq :: M Uniq
genuniq = state $ \G{..} -> (guniq, G{ guniq=guniq+1, ..})

-- | provide a random integer in [lo, hi]
randint :: (Int, Int) -> M Int
randint (lo, hi) = liftIO $ getStdRandom $ randomR (lo, hi)

randint8 :: (Int8, Int8) -> M Int8
randint8 (lo, hi) = liftIO $ getStdRandom $ randomR (lo, hi)

-- | random uniform float
randfloat :: (Float, Float) -> M Float
randfloat (lo, hi) = liftIO $ getStdRandom $ randomR (lo, hi)

randbool :: M Bool
randbool = liftIO $ getStdRandom $ random

-- | Generate a random _concrete_ expression
randExpr :: Int -- ^ depth
 -> [Param] -- ^ parameter names
 -> M Expr
randExpr depth ps = do
  k <- randint (1, 7 + length ps)
  if depth <= 1 || k <= 4
  then do
    r <- randbool
    k <- randint8 (-128, 127) -- int8
    return $ EVal k
  else if k <= 7
  then do
    ldepth <- randint (1, (depth - 1))
    l <- randExpr ldepth ps
    rdepth <- randint (1, (depth - 1))
    r <-  randExpr rdepth ps
    case k of
      5 -> return $ EAdd l r
      6 -> return $ EMul l r
      7 -> return $ ELt l r
  else do
      ix <- randint (0, k - 8)
      return $ EParam (ps !! ix)

-- | Check if an expression has a symbolic value
exprHasSym :: Expr -> Bool
exprHasSym (ESym _) = True
exprHasSym (EParam _) = True
exprHasSym (EVal _) = False
exprHasSym (EAdd e e') = exprHasSym e || exprHasSym e'
exprHasSym (EMul e e') = exprHasSym e || exprHasSym e'
exprHasSym (ELt e e') = exprHasSym e || exprHasSym e'


-- | run an expression with values for parameters and symbols
runExpr :: M.Map String Int8 -> Expr -> Int8
runExpr _ (EVal i) = i
runExpr env (ESym s) = env M.! s
runExpr env (EParam s) = env M.! s
runExpr env (EAdd e e') = runExpr env e + runExpr env e'
runExpr env (EMul e e') = runExpr env e * runExpr env e'
runExpr env (ELt e e') =
  if runExpr env e < runExpr env e'
  then 1
  else 0


-- | Return nagree of runs the concrete program
-- and symbolic program agree on their values
proportionAgreeingRuns :: Expr -> Expr -> M Float
proportionAgreeingRuns c s = do
  -- | take parameters from concrete program and
  -- symbols in abstract program. We need to instantiate
  -- these with values
  let names = exprParams c <> exprSymbols s
  let nruns = 10

  outcomes <- replicateM nruns $ do
    vals <- replicateM (length names) $ randint8 (-128, 127)
    let env = M.fromList $ zip names vals
    pure $ if runExpr env c == runExpr env s then 1 else 0
  pure $ fromIntegral (sum outcomes) / fromIntegral nruns


-- | Find a satisfyng assignment to a symbolic program
unifySymExpr :: HasCallStack => Expr -- ^ concrete program
  -> Expr -- ^ symbolic program
  -> M (Maybe (Expr))
unifySymExpr c s = do
  smtResult <- liftIO $ satWith z3 $ do
        setTimeOut 500
        (sbvc, m) <- compileToSBV mempty c
        (sbvs, m) <- compileToSBV m s
        return $ sbvc .== sbvs

  if not (modelExists smtResult)
     then return Nothing
     -- | note that this step may fail, due to the fact that the model
     -- may do something like:
     -- transform push 2; mul
     else do
       return $ materializeExpr smtResult s


-- | Materialize all symbolic nodes with their concrete values if possible
materializeExpr :: HasCallStack => SatResult -> Expr -> Maybe Expr
materializeExpr res (EVal v) = return $ EVal v
materializeExpr res (EAdd e e') =
  liftA2 EAdd (materializeExpr res e) (materializeExpr res e')
materializeExpr res (EMul e e') =
  liftA2 EMul (materializeExpr res e) (materializeExpr res e')
materializeExpr res (ELt e e') =
  liftA2 ELt (materializeExpr res e) (materializeExpr res e')
materializeExpr res (ESym name) =
  (EVal <$> (getModelValue name res)) <|>
  (EParam <$> getModelUninterpretedValue name res)
materializeExpr res (EParam name) = pure (EParam name)

-- | Gather the parameters used by this expression.
exprParams :: HasCallStack => Expr -> [Param]
exprParams (EAdd e e') = exprParams e <> exprParams e'
exprParams (EMul e e') = exprParams e <> exprParams e'
exprParams (ELt e e') = exprParams e <> exprParams e'
exprParams (ESym _) = []
exprParams (EVal _) = []
exprParams (EParam name) = [name]


-- | Gather the symbols used by this expression.
exprSymbols :: HasCallStack => Expr -> [Param]
exprSymbols (EAdd e e') = exprSymbols e <> exprSymbols e'
exprSymbols (EMul e e') = exprSymbols e <> exprSymbols e'
exprSymbols (ELt e e') = exprSymbols e <> exprSymbols e'
exprSymbols (ESym s) = [s]
exprSymbols (EVal _) = []
exprSymbols (EParam _) = []


-- | baseline score given to anything that unified
unifyScore :: Float
unifyScore = 2.0

-- | Provide a score to a random symbolic program.
scoreExpr :: HasCallStack => Expr -- ^ taget expr
  -> Expr -- ^ symbolic expr
  -> M Float
scoreExpr c s = do
  nagree <- proportionAgreeingRuns c s
  if nagree == 1.0
  then do
    msol <- unifySymExpr c s
    case msol of
      Nothing -> return $ 0.1 + nagree
      Just sol -> return $ unifyScore + 2.0 ** (-1.0 * (costExpr sol))
  else return $ 0.1 + nagree



mhStep :: HasCallStack => Expr -- ^ concrete expression, score
      -> (Float, Expr) -- ^ current symbolic expression
      -> M (Float, Expr) -- ^ next symbolic program, score
mhStep c (score, s) = do
  -- | get a new random expression
  s' <- randExpr 4 (exprParams c)
  score' <- scoreExpr c s'
  -- | find acceptance ratio
  let accept = score' / score
  -- debug $ "proposal: " <> show s' <> " | score: " <> show score' <> " | accept: " <> show accept
  r <- randfloat (0, 1)
  return $ if r < accept then (score', s') else (score, s)


mhSteps :: Int
        -> Expr
        -> (Float, Expr) -> M (Float, Expr)
mhSteps 0 c s = return s
mhSteps i c s =
  mhStep c s >>= \s' -> mhSteps (i - 1) c s'

-- | Get a list of sampled programs by running metropolis hastings
runMH :: HasCallStack => Int -- ^ number of samples wanted
      -> Expr -- ^ concrete expression
      -> M [(Float, Expr)] -- ^ list of runs with scores
runMH i c =
  let go 0 _ _ = return []
      go i c (score, s) = do
        (score', s') <- mhSteps 5 c (score, s)
        nexts <- go (i - 1) c (score', s')
        return $ (score, s):nexts
  in do score <- scoreExpr c c
        go i c (score, c)


optimise :: HasCallStack => Expr -> M [Expr]
optimise c = do
  samples <- runMH 3000 c
  -- | score >= 1 means that it unified.
  return $  nub $ sortOn costExpr $ [e | (score, e) <- samples, score >= unifyScore]

-- | Given number of params, run the program and find equivalent programs
optimiseAndLog :: HasCallStack => Expr -> M ()
optimiseAndLog c = do
    liftIO $ putStrLn $ "----"
    liftIO $ putStrLn $ "program: " <> show c
    opts <- take 3 <$> optimise c
    forM_ opts $ \s -> do
          liftIO $ print s
          liftIO $ putStrLn $ "  cost: " <> show (costExpr s)

main :: HasCallStack => IO ()
main = evalM $ do
  optimiseAndLog (EMul (EVal 2) (EVal 3))
  optimiseAndLog (EMul (EVal 2) (EParam "x"))
  optimiseAndLog (ELt (EMul (EParam "x") (EVal 1)) (EMul (EParam "y") (EVal 1)))


