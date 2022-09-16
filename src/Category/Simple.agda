module Category.Simple where

open import Category
  using (ChainCategory; DependentCategory; chain-category₀)
open import Category.Core
  using (DependentObject; Object'; object')
open import Category.Simple.Lift
  using (DependentSimpleLift; DependentSimplePrelift; DependentSimplePrelift';
    dependent-lift-simple)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Dependent

-- ### DependentSet

-- #### Types

DependentSet
  : {n : ℕ}
  → ChainCategory n
  → Set₁

record DependentSet'
  {n : ℕ}
  (C : ChainCategory (suc n))
  : Set₁

-- #### Definitions

DependentSet {n = zero} _
  = Set
DependentSet {n = suc _} C
  = DependentSet' C

record DependentSet' C where

  inductive
  no-eta-equality

  field

    tail
      : (x : ChainCategory.Object C)
      → DependentSet
        (ChainCategory.tail C x)

module DependentSet
  = DependentSet'

-- ### DependentSimplePrecategory

record DependentSimplePrecategory
  {n : ℕ}
  (C : ChainCategory n)
  : Set₁
  where

  no-eta-equality

  field

    {object}
      : DependentObject
        (ChainCategory.object C)

    lift
      : DependentSimplePrelift object
        (ChainCategory.compose C)
        (ChainCategory.lift C)

-- ### DependentSimplePrecategory'

record DependentSimplePrecategory'
  {n : ℕ}
  (C : ChainCategory n)
  : Set₁
  where

  no-eta-equality

  field

    {object}
      : DependentObject
        (ChainCategory.object C)

    lift
      : DependentSimplePrelift' object
        (ChainCategory.lift C)

-- ### DependentSimpleCategory

-- #### Definition

record DependentSimpleCategory'
  {n : ℕ}
  (C : ChainCategory n)
  : Set₁
  where

  no-eta-equality

  field

    {object}
      : DependentObject
        (ChainCategory.object C)

    lift
      : DependentSimpleLift object
        (ChainCategory.identity C)
        (ChainCategory.compose C)
        (ChainCategory.lift C)

DependentSimpleCategory
  = DependentSimpleCategory'

-- #### Module

module DependentSimpleCategory where

  open module DependentSimpleCategory'' {n C} C'
    = DependentSimpleCategory' {n} {C} C' public

  tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → DependentSimpleCategory C
    → (x : ChainCategory.Object C)
    → DependentSimpleCategory
      (ChainCategory.tail C x)
  tail C' x
    = record
    { lift
      = DependentSimpleLift.tail (lift C') x
    }

  set
    : {n : ℕ}
    → {C : ChainCategory n}
    → DependentSimpleCategory C
    → DependentSet C
  set {n = zero} C'
    = Object'.Object (object C')
  set {n = suc _} C'
    = record
    { tail
      = λ x → set (tail C' x)
    }

-- #### Conversion

dependent-category-simple
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → DependentSimpleCategory C
dependent-category-simple C'
  = record
  { lift
    = dependent-lift-simple
      (DependentCategory.lift C')
  }

-- ## Nondependent

-- ### SimpleCategory

-- #### Definition

SimpleCategory
  : Set₁
SimpleCategory
  = DependentSimpleCategory
    chain-category₀

-- #### Module

module SimpleCategory
  (C : SimpleCategory)
  where

  open DependentSimpleCategory' C public

  open Object' object public
    using (Object)

-- #### Construction

simple-category
  : Set
  → SimpleCategory
simple-category A
  = record
  { object
    = object' A
  }

