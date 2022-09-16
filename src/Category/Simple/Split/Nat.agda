module Category.Simple.Split.Nat where

open import Category.Simple.Split
  using (SimpleSplitFunctor; simple-split-functor-from-retraction)
open import Data.Char
  using (Char)
open import Data.Nat
  using (ℕ)
open import Data.TextWith
  using (TextWith)

-- ## Nondependent

simple-split-functor-nat
  : SimpleSplitFunctor (TextWith Char.is-digit) ℕ
simple-split-functor-nat
  = simple-split-functor-from-retraction TextWith.retraction-digit

