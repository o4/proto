module proto.IO where 

open import proto.Core
open import proto.Coinduction

infixr 5 _++_
_++_ : String → String → String 
_++_ = primStringAppend 

show : String → String 
show = primShowString 

infixl 1 _>>=_ _>>_

postulate 
    return : ∀ {a : Set ℓ₁}              →    a              → IO a
    _>>=_  : ∀ {a : Set ℓ₁} {b : Set ℓ₂} → IO a → (a → IO b) → IO b
    _>>_   : ∀ {a : Set ℓ₁} {b : Set ℓ₂} → IO a →      IO b  → IO b
    
{-# COMPILE GHC return = \ _ _         -> return :: a    ->                IO a #-}
{-# COMPILE GHC  _>>=_ = \ _ _ _ _     -> (>>=)  :: IO a -> (a -> IO b) -> IO b #-}
{-# COMPILE GHC  _>>_  = \ _ _ _ _     -> (>>)   :: IO a ->       IO b  -> IO b #-}
{-# COMPILE UHC return = \ _ _     x   -> UHC.Agda.Builtins.primReturn x        #-}
{-# COMPILE UHC  _>>=_ = \ _ _ _ _ x y -> UHC.Agda.Builtins.primBind   x y      #-}

{-# FOREIGN GHC import qualified Data.Text              #-}
{-# FOREIGN GHC import qualified Data.Text.IO           #-}
{-# FOREIGN GHC import qualified System.IO              #-}
{-# FOREIGN GHC import qualified Control.Exception      #-}
{-# FOREIGN GHC import qualified Control.Monad.Reader   #-}
{-# FOREIGN GHC import qualified Control.Monad.IO.Class #-}

-- MonadIO : ∀ {a : Set} → Monad {a} IO
-- _>>=_ {{MonadIO}} = _>>=_

{-# FOREIGN GHC
  fromColist :: MAlonzo.Code.Qproto.Coinduction.AgdaColist a -> [a]
  fromColist    MAlonzo.Code.Qproto.Coinduction.Nil        = []
  fromColist   (MAlonzo.Code.Qproto.Coinduction.Cons x xs) = x : fromColist (MAlonzo.RTE.flat xs)
    
  toColist :: [a]  -> MAlonzo.Code.Qproto.Coinduction.AgdaColist a
  toColist []       = MAlonzo.Code.Qproto.Coinduction.Nil
  toColist (x : xs) = MAlonzo.Code.Qproto.Coinduction.Cons x (MAlonzo.RTE.Sharp (toColist xs)) #-}

postulate 
    FileHandle  : Set
    stdout      : FileHandle 
    stdin       : FileHandle 
    stderr      : FileHandle 
    getLine     : IO String 
    putStrLn    : String → IO ⊤
    hPutStrLn   : FileHandle → String → IO ⊤
    getContents : IO Costring
    readFile    : String → IO Costring
    writeFile   : String → Costring → IO ⊤
    appendFile  : String → Costring → IO ⊤

{-# COMPILE GHC  FileHandle = type System.IO.Handle                                  #-}
{-# COMPILE GHC      stdout = System.IO.stdout :: System.IO.Handle                   #-}
{-# COMPILE GHC       stdin = System.IO.stdin  :: System.IO.Handle                   #-}
{-# COMPILE GHC      stderr = System.IO.stderr :: System.IO.Handle                   #-}
{-# COMPILE GHC getContents = fmap toColist getContents                              #-}
{-# COMPILE GHC    readFile = fmap toColist . readFile . Data.Text.unpack            #-}
{-# COMPILE GHC   writeFile = \ s -> writeFile  (Data.Text.unpack s) . fromColist    #-}
{-# COMPILE GHC  appendFile = \ s -> appendFile (Data.Text.unpack s) . fromColist    #-}
{-# COMPILE GHC    putStrLn = \ s -> putStrLn   (Data.Text.unpack s)                 #-}
{-# COMPILE GHC   hPutStrLn = Data.Text.IO.hPutStrLn                                 #-}

{-# COMPILE UHC      stdout = UHC.Agda.Builtins.primStdout                           #-}
{-# COMPILE UHC       stdin = UHC.Agda.Builtins.primStdin                            #-}
{-# COMPILE UHC      stderr = UHC.Agda.Builtins.primStderr                           #-}
{-# COMPILE UHC getContents = UHC.Agda.Builtins.primGetContents                      #-}
{-# COMPILE UHC    readFile = UHC.Agda.Builtins.primReadFile                         #-}
{-# COMPILE UHC   writeFile = UHC.Agda.Builtins.primWriteFile                        #-}
{-# COMPILE UHC  appendFile = UHC.Agda.Builtins.primAppendFile                       #-}
{-# COMPILE UHC    putStrLn = UHC.Agda.Builtins.primPutStrLn                         #-}
{-# COMPILE UHC   hPutStrLn = UHC.Agda.Builtins.primHPutStrLn                        #-}

{-# FOREIGN GHC import GHC.MVar
                import Data.IORef #-}

postulate 
  MVar  : Set → Set 
  IORef : Set → Set
  
{-# COMPILE GHC  MVar = type GHC.MVar.MVar    #-}
{-# COMPILE GHC IORef = type Data.IORef.IORef #-}

  
