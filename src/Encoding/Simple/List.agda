module Encoding.Simple.List where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.List
  using (dependent-simple-category-list)
open import Data.Function
  using (_$_)
open import Data.List
  using (List)
open import Data.Nat
  using (ℕ)
open import Encoding.List
  using (dependent-encoding-list)
open import Encoding.Simple
  using (DependentSimpleEncoding; dependent-encoding-simple)
open import Encoding.Unit
  using (dependent-encoding-unit)

-- ## Dependent

dependent-simple-encoding-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {A : Set}
  → DependentSimpleEncoding C' A
  → DependentSimpleEncoding
    (dependent-simple-category-list C')
    (List A)
dependent-simple-encoding-list e
  = dependent-encoding-simple
  $ dependent-encoding-list
    (dependent-encoding-unit e)

