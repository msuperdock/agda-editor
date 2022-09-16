module Encoding.Simple.State.List where

open import Category
  using (ChainCategory)
open import Category.Simple.State
  using (DependentSimpleStateCategory)
open import Category.Simple.State.List
  using (dependent-simple-state-category-list)
open import Data.Function
  using (_$_)
open import Data.List
  using (List)
open import Data.Nat
  using (ℕ)
open import Encoding.Simple.State
  using (DependentSimpleStateEncoding; dependent-state-encoding-simple)
open import Encoding.State.List
  using (dependent-state-encoding-list)
open import Encoding.State.Unit
  using (dependent-state-encoding-unit)

-- ## Dependent

dependent-simple-state-encoding-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleStateCategory C}
  → {A : Set}
  → DependentSimpleStateEncoding C' A
  → DependentSimpleStateEncoding
    (dependent-simple-state-category-list C')
    (List A)
dependent-simple-state-encoding-list e
  = dependent-state-encoding-simple
  $ dependent-state-encoding-list
    (dependent-state-encoding-unit e)

