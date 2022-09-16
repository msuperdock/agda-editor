module Data.Symbol.Token where

open import Data.Bool
  using (Bool; T; _∨_; false; not)
open import Data.Char
  using (Char)
open import Data.List
  using (List; []; _∷_)

-- ## Definition

is-valid
  : List Char
  → Bool
is-valid []
  = false
is-valid (c ∷ cs)
  = not (Char.is-space c) ∨ is-valid cs

IsValid
  : List Char
  → Set
IsValid cs
  = T (is-valid cs)

record Token
  : Set
  where

  field

    characters
      : List Char

    valid
      : IsValid characters

