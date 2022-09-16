module Category.Simple.Partial where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSet)
open import Category.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Category.Simple.State
  using (DependentSimpleStateCategory; SimpleStateCategory)
open import Data.Maybe
  using (Maybe)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Dependent

-- ### DependentSimplePartialFunction

-- #### Types

DependentSimplePartialFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleStateCategory C
  → DependentSet C
  → Set

record DependentSimplePartialFunction''
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentSimpleStateCategory C)
  (D' : DependentSet C)
  : Set

-- #### Definitions

DependentSimplePartialFunction {n = zero} C' D'
  = SimpleStateCategory.Object C' → Maybe D'
DependentSimplePartialFunction {n = suc _} C' D'
  = DependentSimplePartialFunction'' C' D'

record DependentSimplePartialFunction'' {_ C} C' D' where

  inductive

  field

    tail
      : (x : ChainCategory.Object C)
      → DependentSimplePartialFunction
        (DependentSimpleStateCategory.tail C' x)
        (DependentSet.tail D' x)

-- #### Module

module DependentSimplePartialFunction where

  open module DependentSimplePartialFunction''' {n C C' D'} F
    = DependentSimplePartialFunction'' {n} {C} {C'} {D'} F public

  bool-function
    : {n : ℕ}
    → {C : ChainCategory n}
    → {C' : DependentSimpleStateCategory C}
    → {D' : DependentSet C}
    → DependentSimplePartialFunction C' D'
    → DependentSimpleBoolFunction C'
  bool-function {n = zero} F x
    = Maybe.is-just (F x)
  bool-function {n = suc _} F
    = record
    { tail
      = λ x → bool-function (tail F x)
    }

-- ### DependentSimplePartialFunction'

-- #### Types

DependentSimplePartialFunction'
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSet C
  → DependentSet C
  → Set

record DependentSimplePartialFunction'''
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' D' : DependentSet C)
  : Set

-- #### Definitions

DependentSimplePartialFunction' {n = zero} C' D'
  = C' → Maybe D'
DependentSimplePartialFunction' {n = suc _} C' D'
  = DependentSimplePartialFunction''' C' D'

record DependentSimplePartialFunction''' {_ C} C' D' where

  inductive

  field

    tail
      : (x : ChainCategory.Object C)
      → DependentSimplePartialFunction'
        (DependentSet.tail C' x)
        (DependentSet.tail D' x)

module DependentSimplePartialFunction'
  = DependentSimplePartialFunction'''

