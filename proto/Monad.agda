module proto.Monad where 

{-# FOREIGN GHC import Control.Monad.Trans.Reader #-}

data ReaderT (E : Set) (M : Set → Set) (A : Set) : Set where
  readerT : (E → M A) → ReaderT E M A

runReaderT : ∀ {E M A} → ReaderT E M A → E → M A
runReaderT (readerT f) = f

{-# COMPILE GHC ReaderT = data Control.Monad.Trans.Reader.ReaderT ( ReaderT ) #-}
-- {-# COMPILE GHC runReaderT = Control.Monad.Trans.Reader.runReaderT #-}
