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



-- | symbolic expressions
data SymE =
   SymInt Int
   | SymSym String
   | SymAdd SymE SymE
   | SymMul SymE SymE
   | SymLt SymE SymE
   | SymIte SymE SymE SymE
  deriving(Eq, Ord, Show)

-- | regular instructions
data Inst a = Push a | Add | Mul | Lt | If deriving(Eq, Show, Ord)


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

-- | Compile the symbolic expression to an SBV expresion
compileSymbolicToSBV :: SymE -> Symbolic (SBV Int32)
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


-- reifySymExpr :: SatResult -> SymE -> Int
-- reifySumExpr res (SymInt x) = x
-- reifySumExpr res (SymAdd x x') = x + x'
-- reifySumExpr res (SymMul x x') = x * x'

-- | Reify a symbolic instruction into a real instruction
-- by consulting the dictionary.
reifySymInst :: SatResult -> Inst SymE -> Inst Int32
reifySymInst res (Push (SymSym s)) =
  let Just (v :: Int32) = getModelValue s res in Push v
reifySymInst _ Add = Add
reifySymInst _ Mul = Mul
reifySymInst _ Lt = Lt

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
unifySymProgram :: Program Int32
  -> Program SymE
  -> M (Maybe (Program Int32))
unifySymProgram p sp =
  case liftA2 (,) (runConcrete p []) (runSymbolic sp []) of
    Nothing -> return Nothing -- ^ program failed to run, return Nothing
    Just (vprog, vsym) -> do
      -- | create an SBV expression that we want
      -- | Try to get a satisfying model
      smtResult <- liftIO $ sat $ do
         vsbv <- compileSymbolicToSBV vsym
         return $ vsbv .== fromIntegral vprog
      if not (modelExists smtResult)
         then return Nothing
         else return $ Just $ reifySymProgram smtResult sp

-- | Provide a score to a random symbolic program.
scoreSymProgram :: Program Int32 -- ^ target program
  -> Program SymE -- ^ current symbolic program
  -> M Float
scoreSymProgram p sp = do
  sol <- unifySymProgram p sp
  case sol of
    Nothing -> return 0.0 -- ^ let there be some chance of accepting
                          --   invalid programs
    Just reifysp ->
      let Just (_, cost) = runCost concreteTransfer reifysp []
       in return $ 2.0 ** (-1.0 * fromIntegral (getCost cost))



mhStep :: Program Int32 -- ^ concrete program
      -> Program SymE -- ^ current symbolic program
      -> M (Program SymE) -- ^ next symbolic program
mhStep c s = do
  a <- scoreSymProgram c s
  -- | perturb the current program to get the next program
  s' <- randSymProgram (length c * 2)-- perturbSymProgram s
  a' <- scoreSymProgram c s'
  -- | find acceptance ratio
  let accept = a' / a
  r <- randfloat (0, 1)
  return $ if r < accept then s' else s


mhSteps :: Int -> Program Int32 -> Program SymE -> M (Program SymE)
mhSteps 0 c s = return s
mhSteps i c s = mhStep c s >>= \s' -> mhSteps (i - 1) c s'

-- | get a lazy of sampled programs
runMH :: Int -> Program Int32 -> Program SymE -> M [Program SymE]
runMH 0 _ _ = return []
runMH i c s = do
     s' <- mhSteps 10 c s
     nexts <- runMH (i - 1) c s'
     return $ s:nexts

-- | person who runs the program needs to supply a stack value
p1 :: Num a => Program a
p1 = [Push 2
     , Push 2
     , Push 3
     , Mul
     , Add]

main :: IO ()
main = do
    print $ "program: " <> show p1
    print $ runConcrete p1 []
    evalM $ do
      s <- randSymProgram (length p1)
      perturbs <- perturbSymProgram s
      samples <- runMH 100 p1 s
      unifieds <- nub <$> catMaybes <$> traverse (unifySymProgram p1) samples
      forM_ unifieds $ \p -> do
            liftIO $ print p
            let Just (_, cost) =  runCost concreteTransfer p []
            liftIO $ putStrLn $ "  cost: " <> show cost

