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
import Data.Bits
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

-- | Binary operation
data Binop = Add | Mul | And | Lt deriving(Eq, Ord)

instance Show Binop where
  show Add = "+"
  show Mul = "*"
  show And = "and"
  show Lt = "<"

-- | Expressions
data Expr = EVal Int8
          | ESym String
          | EParam Param
          | EBinop Binop Expr Expr
          | ENot Expr
          | EIte Expr Expr Expr deriving(Eq, Ord)

instance Show Expr where
  show (EVal a)=  show a
  show (ESym a)= "s-" <> a
  show (EParam a) = "p-" <> a
  show (EBinop op e e') = "("  <> show op <> " " <> show e <> " " <> show e' <> ")"
  show (ENot e) = "(not" <> show e <> ")"
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

compileToSBV m (EBinop op e e') = do
  (e, m) <- (compileToSBV m e)
  (e', m) <- (compileToSBV m e')
  case op of
    Add -> pure $ (e + e', m)
    Mul -> pure $ (e * e', m)
    Lt -> pure $ (ite (e .< e') 1 0, m)
    And -> pure $ (e .&. e', m)

compileToSBV m (EIte i t e) = do
  (i, m) <- (compileToSBV m i)
  (t, m) <- (compileToSBV m t)
  (e, m) <- (compileToSBV m e)
  return $ (ite  (i .== 1) t e, m)

-- | Return the computational cost of the expr
costExpr :: HasCallStack => Expr -> Float
costExpr (EBinop op e e') =
  let l = costExpr e
      r = costExpr e'
      cur = case op of
              Add -> 1
              Mul -> 4
              And -> 1
              Lt -> 1
  in l + r + cur
costExpr (EVal _) = 0
costExpr (ESym _) = 1
costExpr (EParam _) = 1
costExpr (EIte i t e) = costExpr i + (costExpr t + costExpr e) * 0.5

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
  k <- randint (1, 8 + length ps)
  if depth <= 1 || k <= 4
  then do
    r <- randbool
    k <- randint8 (-128, 127) -- int8
    return $ EVal k
  else if k <= 8
  then do
    ldepth <- randint (1, (depth - 1))
    l <- randExpr ldepth ps
    rdepth <- randint (1, (depth - 1))
    r <-  randExpr rdepth ps
    let op = case k of
                5 -> Add
                6 -> Mul
                7 -> Lt
                8 -> And
    pure $ EBinop op l r
  else do
      ix <- randint (0, k - 9)
      return $ EParam (ps !! ix)


-- | run an expression with values for parameters and symbols
runExpr :: M.Map String Int8 -> Expr -> Int8
runExpr _ (EVal i) = i
runExpr env (ESym s) = env M.! s
runExpr env (EParam s) = env M.! s
runExpr env (EIte i t e) =
  case runExpr env i of
    1 -> runExpr env t
    0 -> runExpr env e
runExpr env (EBinop op e e') =
  let l = runExpr env e
      r = runExpr env e'
      f = case op of
            Add -> (+)
            Mul -> (*)
            Lt -> \x y -> if x < y then 1 else 0
            And -> (.&.)
  in f l r

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
materializeExpr res (EIte i t e) =
  liftA3 EIte (materializeExpr res i)
              (materializeExpr res t)
              (materializeExpr res e)
materializeExpr res (EBinop op e e') =
  liftA2 (EBinop op) (materializeExpr res e) (materializeExpr res e')
materializeExpr res (ESym name) =
  (EVal <$> (getModelValue name res)) <|>
  (EParam <$> getModelUninterpretedValue name res)
materializeExpr res (EParam name) = pure (EParam name)

-- | Gather the parameters used by this expression.
exprParams :: HasCallStack => Expr -> [Param]
exprParams (EBinop _ e e') = exprParams e <> exprParams e'
exprParams (EIte i t e) =  exprParams i <> exprParams t <> exprParams e
exprParams (ENot e) = exprParams e
exprParams (ESym _) = []
exprParams (EVal _) = []
exprParams (EParam name) = [name]


-- | Gather the symbols used by this expression.
exprSymbols :: HasCallStack => Expr -> [Param]
exprSymbols (EBinop _ e e') = exprSymbols e <> exprSymbols e'
exprSymbols (ENot e) = exprSymbols e
exprSymbols (ESym s) = [s]
exprSymbols (EVal _) = []
exprSymbols (EParam _) = []
exprSymbols (EIte i t e) = exprSymbols i <> exprSymbols t <> exprSymbols e


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
  optimiseAndLog (EBinop Mul (EVal 2) (EVal 3))
  optimiseAndLog (EBinop Mul (EVal 2) (EParam "x"))
  optimiseAndLog (EIte (EVal 1) (EParam "x") (EParam "x"))
  optimiseAndLog (EBinop And (EParam "x") (EParam "x"))
  optimiseAndLog (EBinop Lt (EBinop Mul (EParam "x") (EVal 1))
                         (EBinop Mul (EParam "y") (EVal 1)))


