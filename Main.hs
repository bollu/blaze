{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
module Main where
-- | Here, we consider a small implementation of the
-- STOKE paper, where we stochastically optimise over a
-- large space of programs.
import Data.SBV
import Data.SBV.Internals (CV)
import Data.Word
import Control.Monad
import System.Random
-- | for MCMC
import Control.Monad.Bayes.Traced.Basic
import Control.Monad.Bayes.Class
import Control.Monad.Fail

import Control.Monad.Writer
import Control.Monad.Except
import Control.Monad.Identity
import qualified Data.Map as M


data Inst a = Push a | Add | Mul | Lt | If deriving(Eq, Show, Ord)


type Program a = [Inst a]
type Stack a = [a]

data ExistsProof where
    ExistsProof :: forall a. Provable a => a -> ExistsProof

-- | Transfer function
data Transfer m a =
    Transfer { tadd :: a -> a -> m a
          , tmul :: a -> a -> m a
          , tlt :: a -> a -> m a
          , ttrue :: a -> Bool
          }

-- | Monadic interpretMer of the code, to run arbitrary effects.
interpretM :: (MonadFail m, Monad m) => Transfer m a  -> Program a -> [a] -> m a
interpretM Transfer{..} [] (a:_) = return a
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


concreteTransfer :: Transfer Maybe Int
concreteTransfer =
    Transfer { tadd = \a a' -> pure $ a + a'
          , tmul = \a a' -> pure $ a * a'
          , tlt = \a a' -> pure $ if a < a' then 1 else 0
          , ttrue = \a -> a == 1
          }

-- | concreteTransfer evaluator
runConcrete :: Program Int -> [Int] -> Maybe Int
runConcrete p as = interpretM concreteTransfer p as

type Cost = Product Int

costTransferT :: (MonadFail m, Monad m) => Transfer m a -> Transfer (WriterT Cost m) a
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


symbolicTransfer :: Transfer Maybe (SBV Int32)
symbolicTransfer =
    Transfer { tadd = \a a' -> pure $ a + a'
          , tmul = \a a' -> pure $ a * a'
          , tlt = \a a' -> pure $ ite (a .< a') 1 0
          , ttrue = \a -> a == 1
          }

-- | concreteTransfer evaluator
runSymbolic :: Program (SBV Int32) -> [(SBV Int32)] -> Maybe (SBV Int32)
runSymbolic p as = interpretM symbolicTransfer p as

-- | person who runs the program needs to supply a stack value
p1 :: Num a => Program a
p1 = [Push 2
     , Push 2
     , Add]

-- | Generate a random instruction.
randSymInst ::  Symbolic (Inst (SBV Int32))
randSymInst = do
    choice <- liftIO $ getStdRandom $ randomR (1, 4) :: Symbolic Int32
    case choice of
      1 -> do
          v <- exists_
          return $ Push v
      2 -> return $ Add
      3 -> return $ Mul
      4 -> return $ Lt


type M = SymbolicT (ExceptT String IO)

-- | Generate a random program
randSymProgram :: Int -- ^ max length
            -> Symbolic (Program (SBV Int32))
randSymProgram maxl = do
    l <- liftIO $ getStdRandom $ randomR (1, maxl)
    replicateM l randSymInst

symProgramUnify ::
    Program Int -- ^ concrete program
    -> Program (SBV (Int32)) -- ^ abstract program
    -> SBool
symProgramUnify p sp =
    case runConcrete p [] of
      Nothing -> (1 :: SBV (Int32)) .== 0
      Just finalv -> do
          case runSymbolic sp [] of
            Nothing -> (1 :: SBV (Int32)) .== 0
            Just symval -> symval .== (fromIntegral finalv)

tryGenerateProgram ::
  Program Int
  -> IO (Maybe (M.Map String CV))
tryGenerateProgram p = do
    smtResult <- sat $ do
            sp <-  randSymProgram 10
            lift $ print $ sp
            pure $ symProgramUnify p1 sp
    if modelExists smtResult
    then pure $ Just $  getModelDictionary smtResult
    else pure $ Nothing

generateProgram :: Program Int
  -> IO (M.Map String CV)
generateProgram p = do
    env <- tryGenerateProgram p
    case env of
      Nothing -> generateProgram p
      Just a -> return a

main :: IO ()
main = do
    generateProgram p1 >>= print

