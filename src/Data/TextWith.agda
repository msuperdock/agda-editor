module Data.TextWith where

open import Data.Bool
  using (Bool; true)
open import Data.Char
  using (Char)
open import Data.CharWith
  using (CharWith)
open import Data.Digit
  using (module Digits)
open import Data.Function
  using (_$_; const)
open import Data.List
  using (List)
open import Data.Nat
  using (ℕ)
open import Data.Retraction
  using (Retraction; retraction-compose)
open import Data.Text
  using (Text)

-- ## Definition

TextWith
  : (Char → Bool)
  → Set
TextWith p
  = List (CharWith p)

-- ## Module

module TextWith where

  retraction
    : Retraction (TextWith (const true)) Text
  retraction
    = List.retraction CharWith.retraction

  retraction-digit
    : Retraction (TextWith Char.is-digit) ℕ
  retraction-digit
    = retraction-compose Digits.retraction
    $ List.retraction CharWith.retraction-digit

