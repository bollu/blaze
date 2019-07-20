{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
module Main where
import Data.Maybe (catMaybes)
import Data.List (nub)
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
data G = G { guniq :: Uniq, gsymbols :: M.Map String (SBV Int32) }

-- | Top level monad all our computations run in
type M a =  StateT G IO a

-- | execute a computation inside our `M`
evalM :: M a -> IO a
evalM ma = evalStateT ma (G 0 mempty)


-- | Number of parameters for the program
type NParams = Int

-- | symbolic expressions
data SymE =
   SymInt Int32
   | SymSym String
   | SymParam String
   | SymAdd SymE SymE
   | SymMul SymE SymE
   | SymLt SymE SymE
   | SymIte SymE SymE SymE
  deriving(Eq, Ord, Show)

-- | regular instructions
data Inst a = Push a | Add | Mul | Lt | If | Dup
  deriving(Eq, Show, Ord)


type Program a = [Inst a]
type Stack a = [a]


-- | Transfer function
data Transfer m a =
    Transfer { tadd :: a -> a -> m a
          , tmul :: a -> a -> m a
          , tlt :: a -> a -> m a
          , ttrue :: a -> Bool
          }

-- | Monadic interpretMer of the code, to run arbitrary effects.
interpretM :: (MonadFail m, Monad m)
           => Transfer m a
           -> Program a
           -> [a]
           -> m a
interpretM Transfer{..} [] [a] = return a
interpretM Transfer{..} ((Push a):is) as =
    interpretM Transfer{..} is (a:as)
interpretM Transfer{..} (Add:is) (a:a':as) = do
    o <- tadd a a'
    interpretM Transfer{..} is (o:as)
interpretM Transfer{..} (Mul:is) (a:a':as) = do
    o <- tmul a a'
    interpretM Transfer{..} is (o:as)
interpretM Transfer{..} (Lt:is) (a:a':as) = do
    o <- tlt a a'
    interpretM Transfer{..} is (o:as)
interpretM Transfer{..} (Dup:is) (a:as) = do
    interpretM Transfer{..} is (a:a:as)
interpretM _ _ _  = Control.Monad.Fail.fail ""


concreteTransfer :: Transfer Maybe Int32
concreteTransfer =
    Transfer { tadd = \a a' -> pure $ a + a'
          , tmul = \a a' -> pure $ a * a'
          , tlt = \a a' -> pure $ if a < a' then 1 else 0
          , ttrue = \a -> a == 1
          }

-- | concreteTransfer evaluator
runConcrete :: Program Int32 -> [Int32] -> Maybe Int32
runConcrete p as = interpretM concreteTransfer p as

-- | costs are additive
type Cost = Sum Int

-- | Extract the underlying Int from cost
getCost :: Cost -> Int
getCost = getSum

costTransferT :: (MonadFail m, Monad m)
              => Transfer m a
              -> Transfer (WriterT Cost m) a
costTransferT Transfer{..} =
    Transfer { tadd = \a a' -> do
                o <- lift $ tadd a a'
                writer $ (o, 1)
          , tmul = \a a' -> do
                o <- lift $ tmul a a'
                writer $ (o, 4)
          , tlt = \a a' -> do
                o <- lift $ tmul a a'
                writer $ (o, 1)
          , ttrue = ttrue
          }

-- | Evaluator that figures out the cost
runCost :: (MonadFail m, Monad m) =>
    Transfer m a
    -> Program a
    -> [a]
    -> m (a, Cost)
runCost t p as = runWriterT $ interpretM (costTransferT t) p as


symbolicTransfer :: Transfer Maybe (SymE)
symbolicTransfer =
    Transfer { tadd = \a a' -> pure $ SymAdd a a'
          , tmul = \a a' -> pure $ SymMul a a'
          , tlt = \a a' -> pure $
              SymIte (SymLt a a') (SymInt 1) (SymInt 0)
          , ttrue = \a -> a == SymInt 1
          }

-- | create a symbolic program
runSymbolic :: Program SymE -> [SymE] -> Maybe SymE
runSymbolic p as = interpretM symbolicTransfer p as

compileSymbolicToSBV :: M.Map String (SInt32) ->
  SymE ->
  Symbolic (SInt32, M.Map String (SInt32))
compileSymbolicToSBV m (SymInt x) = return $ (fromIntegral x, m)
compileSymbolicToSBV m (SymSym name) =
  case m M.!? name of
    Just sym -> return ( sym, m)
    Nothing -> do
       sym <- sInt32 name
       return $ (sym, M.insert name sym m)
compileSymbolicToSBV m (SymParam name) = do
  case m M.!? name of
    Just sym -> return ( sym, m)
    Nothing -> do
       sym <- forall name
       return $ (sym, M.insert name sym m)
compileSymbolicToSBV m (SymAdd s1 s2) = do
  (s1, m) <- (compileSymbolicToSBV m s1)
  (s2, m) <- (compileSymbolicToSBV m s2)
  return $ (s1 + s2, m)

compileSymbolicToSBV m (SymMul s1 s2) = do
  (s1, m) <- (compileSymbolicToSBV m s1)
  (s2, m) <- (compileSymbolicToSBV m s2)
  return $ ( s1 * s2, m)

compileSymbolicToSBV m (SymLt s1 s2) = do
  (s1, m) <- (compileSymbolicToSBV m s1)
  (s2, m) <- (compileSymbolicToSBV m s2)
  return $ (ite (s1 .< s2) 1 0, m)

compileSymbolicToSBV m (SymIte i t e) = do
  (i, m) <- (compileSymbolicToSBV m i)
  (t, m) <- (compileSymbolicToSBV m t)
  (e, m) <- (compileSymbolicToSBV m e)
  return $ (ite  (i .== 1) t e, m)


-- | generate a unique label
genuniq :: M Uniq
genuniq = state $ \G{..} -> (guniq, G{ guniq=guniq+1, ..})

-- | provide a random integer in [lo, hi]
randint :: (Int, Int) -> M Int
randint (lo, hi) = liftIO $ getStdRandom $ randomR (lo, hi)

randint32 :: (Int32, Int32) -> M Int32
randint32 (lo, hi) = liftIO $ getStdRandom $ randomR (lo, hi)

-- | random uniform float
randfloat :: (Float, Float) -> M Float
randfloat (lo, hi) = liftIO $ getStdRandom $ randomR (lo, hi)

-- | Generate a random instruction.
randSymInst ::  M (Inst SymE)
randSymInst = do
    choice <- randint (1, 5)
    case choice of
      1 -> do
          uuid <- genuniq
          let name = "sym-" <> show uuid
          return $ Push (SymSym name)
      2 -> return $ Add
      3 -> return $ Mul
      4 -> return $ Lt
      5 -> return $ Dup

-- | Reify a symbolic instruction into a real instruction
-- by consulting the dictionary.
materializeSymInst :: SatResult -> Inst SymE -> Maybe (Inst Int32)
materializeSymInst res (Push (SymParam s)) = error $ "param in push"
materializeSymInst res (Push (SymSym s)) = do
  v <- getModelValue s res
  return $ Push v
materializeSymInst _ Add = return Add
materializeSymInst _ Mul = return Mul
materializeSymInst _ Lt = return Lt
materializeSymInst _ Dup = return Dup

-- | Given a symbolic program and an SBV model dictionary,
-- reify it into an actual program
materializeSymProgram :: SatResult -> Program SymE -> Maybe (Program Int32)
materializeSymProgram res s = trace ("reifyp: " <> show s) $ traverse (materializeSymInst  res) s

-- | Convert a concrete program into a symbolic program
concrete2symInst :: Inst Int32 -> Inst SymE
concrete2symInst (Push i) = Push (SymInt i)
concrete2symInst Add = Add
concrete2symInst Mul = Mul
concrete2symInst Lt = Lt
concrete2symInst Dup = Dup

-- | Convert a concrete program into a symbolic program
concrete2symProgram :: Program Int32 -> Program SymE
concrete2symProgram = map concrete2symInst


-- | Generate a random program
randSymProgram :: Int -- ^ max length
            -> M (Program SymE) -- ^ symbolic program
randSymProgram maxl = do
    l <- liftIO $ getStdRandom $ randomR (1, maxl)
    replicateM l randSymInst

-- | insert an element at the middle of a list
splice :: [a] -> Int -> a -> [a]
splice xs i x = take (i - 1) xs ++ [x] ++ drop i xs

-- | modify the original program to get a new program
perturbSymProgram ::
  Program SymE
  -> M (Program SymE)
perturbSymProgram [] = return []
perturbSymProgram p = do
  ninstsToModify <- randint (1, length p)
  ixs <- replicateM ninstsToModify $ randint (0, length p - 1)
  foldM (\p ix -> do
    inst' <- randSymInst
    return $ splice p ix inst') p ixs


-- | Find a satisfyng assignment to a symbolic program
unifySymProgram ::
  NParams  -- ^ number of parameters
  -> Program Int32 -- ^ concrete program
  -> Program SymE -- ^ symbolic program
  -> M (Maybe (Program Int32))
unifySymProgram nparams c s = do
  ids <- replicateM nparams genuniq
  let params = [SymParam ("param-" <> show i) | i <- ids]
  -- | Run the program as a symbolic effect on the stack
  let mvc = runSymbolic (concrete2symProgram c) params
  -- | Run the symbolic program as the same
  let mvs = runSymbolic s params
  smtResult <- liftIO $ sat $ do
    case liftA2 (,) mvc mvs of
      Nothing -> return $ 1 .== (0 :: SInt32)
      Just (vc, vs) -> do
        -- | We need to be careful here to not double allocate te
        -- same symbol
        (sbvc, m) <- compileSymbolicToSBV mempty vc
        (sbvs, m) <- compileSymbolicToSBV m vs
        return $ sbvc .== sbvs

  if not (modelExists smtResult)
     then return Nothing
     -- | note that this step may fail, due to the fact that the model
     -- may do something like:
     -- transform push 2; mul
     -- into: push p; push p; add; where "p" is the symbol of the parameter.
     else return $ materializeSymProgram smtResult s

-- | Provide a score to a random symbolic program.
scoreSymProgram :: NParams
  -> Program Int32 -- ^ target program
  -> Program SymE -- ^ current symbolic program
  -> M Float
scoreSymProgram nparams c s = do
  msol <- unifySymProgram nparams c s
  case msol of
    Nothing -> return 0.0
    Just sol -> do
      inputs <- replicateM nparams (randint32 (1, 4))
      let Just (_, cost) = runCost concreteTransfer sol inputs
      return $ 2.0 ** (-1.0 * fromIntegral (getCost cost))



mhStep :: NParams ->
      Program Int32 -- ^ concrete program
      -> Program SymE -- ^ current symbolic program
      -> M (Program SymE) -- ^ next symbolic program
mhStep nparams c s = do
  a <- scoreSymProgram nparams c s
  -- | perturb the current program to get the next program
  s' <- randSymProgram (length c * 2) -- perturbSymProgram s
  a' <- scoreSymProgram nparams c s'
  -- | find acceptance ratio
  let accept = a' / a
  r <- randfloat (0, 1)
  return $ if r < accept then s' else s


mhSteps :: Int
        -> NParams
        -> Program Int32
        -> Program SymE -> M (Program SymE)
mhSteps 0 nparams c s = return s
mhSteps i nparams c s =
  mhStep nparams c s >>= \s' -> mhSteps (i - 1) nparams c s'

-- | get a lazy of sampled programs
runMH :: Int
      -> NParams
      -> Program Int32 -> Program SymE -> M [Program SymE]
runMH 0 nparams _ _ = return []
runMH i nparams c s = do
     s' <- mhSteps 10 nparams c s
     nexts <- runMH (i - 1) nparams c s'
     return $ s:nexts


optimise :: NParams -- ^ number of parameters
            -> Program Int32  -- ^ original program
            -> M [Program Int32]
optimise nparams p = do
  s <- randSymProgram (length p  * 2)
  samples <- runMH 10 nparams p s
  nub <$> catMaybes <$> traverse (unifySymProgram nparams p) samples


-- | Given number of params, run the program and find equivalent programs
mainProgram :: NParams -> Program Int32 -> M ()
mainProgram nparams p = do
    liftIO $ putStrLn $ "----"
    liftIO $ putStrLn $ "program: " <> show p
    let params = [SymParam $ "p-" <> show i | i <- [1..nparams]]
    liftIO $ print $ runSymbolic (concrete2symProgram p) params
    opts <- optimise nparams p
    forM_ opts $ \p' -> do
          liftIO $ print p'
          liftIO $ print $ runSymbolic (concrete2symProgram p') params
          let Just (_, cost) =  runCost symbolicTransfer (concrete2symProgram p') params
          liftIO $ putStrLn $ "  cost: " <> show cost

main :: IO ()
main = evalM $ do
  mainProgram 0 [Push 2, Push 3, Push 3, Mul, Add]
  mainProgram 1 [Push 2, Mul]

