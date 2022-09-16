module Data.If where

open import Data.Bool
  using (Bool; false; true)

-- ## Definition

data If
  (A : Set)
  : Bool
  → Set
  where

  nothing
    : If A false

  just
    : A
    → If A true

