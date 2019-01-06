{-# OPTIONS --safe #-}

module proto.Base where 

open import proto.Core public 
open import proto.ByteString
open import proto.Map
open import proto.IO

data Strictness : Set where 
    Lazy   : Strictness 
    Strict : Strictness 
    
ByteString : Strictness → Set 
ByteString Strict = StByteString 
ByteString Lazy   = CoByteString
