module Category.Simple.State where

open import Category
  using (Category; ChainCategory; chain-category₀; chain-category₁)
open import Category.Core
  using (DependentObject; Object'; object')
open import Category.Simple.State.Lift
  using (DependentSimpleStateLift; dependent-state-lift-simple)
open import Category.State
  using (DependentStateCategory)
open import Data.Nat
  using (ℕ; suc)

-- ## Dependent

-- ### Definition

record DependentSimpleStateCategory'
  {n : ℕ}
  (C : ChainCategory n)
  : Set₁
  where

  field

    {object}
      : DependentObject
        (ChainCategory.object C)

    lift
      : DependentSimpleStateLift object
        (ChainCategory.identity C)
        (ChainCategory.lift C)

DependentSimpleStateCategory
  = DependentSimpleStateCategory'

-- ### Module

module DependentSimpleStateCategory where

  open module DependentSimpleStateCategory'' {n C} C'
    = DependentSimpleStateCategory' {n} {C} C' public

  tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → DependentSimpleStateCategory C
    → (x : ChainCategory.Object C)
    → DependentSimpleStateCategory
      (ChainCategory.tail C x)
  tail C' x
    = record
    { lift
      = DependentSimpleStateLift.tail (lift C') x
    }

-- ### Conversion

dependent-state-category-simple
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentStateCategory C
  → DependentSimpleStateCategory C
dependent-state-category-simple C'
  = record
  { lift
    = dependent-state-lift-simple
      (DependentStateCategory.lift C')
  }

-- ## Nondependent

-- ### Definition

SimpleStateCategory
  : Set₁
SimpleStateCategory
  = DependentSimpleStateCategory
    chain-category₀

-- ### Module

module SimpleStateCategory
  (C : SimpleStateCategory)
  where

  open DependentSimpleStateCategory' C public

  open Object' object public
    using () renaming
    ( Object
      to Object
    )

-- ### Construction

simple-state-category
  : Set
  → SimpleStateCategory
simple-state-category A
  = record
  { object
    = object' A
  }

-- ## Dependent₁

-- ### Definition

DependentSimpleStateCategory₁
  : Category
  → Set₁
DependentSimpleStateCategory₁ C
  = DependentSimpleStateCategory
    (chain-category₁ C)

-- ### Module

module DependentSimpleStateCategory₁
  (C : Category)
  (C' : DependentSimpleStateCategory₁ C)
  where

  open DependentSimpleStateCategory' C' public
    using (lift)

  open module SimpleStateCategory' x
    = SimpleStateCategory (DependentSimpleStateCategory.tail C' x) public
    using (Object)

