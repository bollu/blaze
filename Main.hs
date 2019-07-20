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

-- | unique labels
type Uniq = Int

-- | Top level monad all our computations run in
type M a =  StateT Uniq IO a

-- | execute a computation inside our `M`
evalM :: M a -> IO a
evalM ma = evalStateT ma 0


-- | Number of parameters for the program
type NParams = Int

-- | symbolic expressions
data SymE =
   SymInt Int32
   | SymSym String
   | SymAdd SymE SymE
   | SymMul SymE SymE
   | SymLt SymE SymE
   | SymIte SymE SymE SymE
  deriving(Eq, Ord, Show)

-- | regular instructions
data Inst a = Push a | Add | Mul | Lt | If
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

compileSymbolicToSBV :: SymE -> (Symbolic (SBV Int32)
compileSymbolicToSBV (SymInt x) = return $ fromIntegral x
compileSymbolicToSBV (SymSym x) = symbolic x
compileSymbolicToSBV (SymAdd s1 s2) =
  liftA2 (+) (compileSymbolicToSBV s1)  (compileSymbolicToSBV s2)
compileSymbolicToSBV (SymMul s1 s2) =
  liftA2 (*) (compileSymbolicToSBV s1)  (compileSymbolicToSBV s2)
compileSymbolicToSBV (SymLt s1 s2) = do
  sbv1 <- compileSymbolicToSBV s1
  sbv2 <- compileSymbolicToSBV s2
  return $ ite  (sbv1 .< sbv2) 1 0
compileSymbolicToSBV (SymIte i t e) = do
  sbvi <- compileSymbolicToSBV i
  sbvt <- compileSymbolicToSBV t
  sbve <- compileSymbolicToSBV e
  return $ ite  (sbvi .== 1) sbvt sbve


-- | generate a unique label
genuniq :: M Uniq
genuniq = state $ \u -> (u, u+1)

-- | provide a random integer in [lo, hi]
randint :: (Int, Int) -> M Int
randint (lo, hi) = liftIO $ getStdRandom $ randomR (lo, hi)

-- | random uniform float
randfloat :: (Float, Float) -> M Float
randfloat (lo, hi) = liftIO $ getStdRandom $ randomR (lo, hi)

-- | Generate a random instruction.
randSymInst ::  StateT Uniq IO (Inst SymE)
randSymInst = do
    choice <- randint (1, 4)
    case choice of
      1 -> do
          uuid <- genuniq
          let name = "sym-" <> show uuid
          return $ Push (SymSym name)
      2 -> return $ Add
      3 -> return $ Mul
      4 -> return $ Lt

-- | Reify a symbolic instruction into a real instruction
-- by consulting the dictionary.
reifySymInst :: SatResult -> Inst SymE -> Inst Int32
reifySymInst res (Push (SymSym s)) =
  let Just (v :: Int32) = getModelValue s res in Push v
reifySymInst _ Add = Add
reifySymInst _ Mul = Mul
reifySymInst _ Lt = Lt

-- | Convert a concrete program into a symbolic program
concrete2symInst :: Inst Int32 -> Inst SymE
concrete2symInst (Push i) = Push (SymInt i)
concrete2symInst Add = Add
concrete2symInst Mul = Mul
concrete2symInst Lt = Lt

-- | Convert a concrete program into a symbolic program
concrete2symProgram :: Program Int32 -> Program SymE
concrete2symProgram = map concrete2symInst

-- | Given a symbolic program and an SBV model dictionary,
-- reify it into an actual program
reifySymProgram :: SatResult -> Program SymE -> Program Int32
reifySymProgram res = map (reifySymInst  res)

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
  let params = [SymSym ("param-" <> show i) | i <- ids]
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
        sbvc <- compileSymbolicToSBV vc
        sbvs <- compileSymbolicToSBV vs
        return $ sbvc .== sbvs

  if not (modelExists smtResult)
     then return Nothing
     else return $ Just $ reifySymProgram smtResult s

-- | Provide a score to a random symbolic program.
scoreSymProgram :: NParams
  -> Program Int32 -- ^ target program
  -> Program SymE -- ^ current symbolic program
  -> M Float
scoreSymProgram nparams c s = do
  msol <- unifySymProgram nparams c s
  case msol of
    Nothing -> return 0.0 -- ^ let there be some chance of accepting
                          --   invalid programs
    Just sol ->
      let Just (_, cost) = runCost concreteTransfer sol []
       in return $ 2.0 ** (-1.0 * fromIntegral (getCost cost))



mhStep :: NParams ->
      Program Int32 -- ^ concrete program
      -> Program SymE -- ^ current symbolic program
      -> M (Program SymE) -- ^ next symbolic program
mhStep nparams c s = do
  a <- scoreSymProgram nparams c s
  -- | perturb the current program to get the next program
  s' <- randSymProgram (length c * 2)-- perturbSymProgram s
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
    liftIO $ print $ runConcrete p []
    opts <- optimise nparams p
    forM_ opts $ \p -> do
          liftIO $ print p
          let Just (_, cost) =  runCost concreteTransfer p []
          liftIO $ putStrLn $ "  cost: " <> show cost

main :: IO ()
main = evalM $ do
  mainProgram 0 [Push 2, Push 3, Push 3, Mul, Add]
  mainProgram 1 [Push 2, Mul]

