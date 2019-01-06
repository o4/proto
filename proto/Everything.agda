{-# OPTIONS --safe #-}

module proto.Everything where

open import proto.Base 
open import proto.ByteString 
open import proto.Coinduction
open import proto.Core
open import proto.IO
open import proto.Map

main : IO ⊤
main = putStrLn "Ok"
