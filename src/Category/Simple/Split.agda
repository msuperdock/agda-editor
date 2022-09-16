module Category.Simple.Split where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Simple
  using (DependentSimpleCategory; DependentSimplePrecategory;
    DependentSimplePrecategory'; dependent-category-simple; simple-category)
open import Category.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Category.Simple.Partial
  using (DependentSimplePartialFunction)
open import Category.Simple.Split.Lift
  using (DependentSimpleSplitLift; DependentSimpleSplitLift';
    DependentSimpleSplitPrelift; DependentSimpleSplitPrelift';
    dependent-split-lift-simple; dependent-split-lift-simple')
open import Category.Simple.State
  using (DependentSimpleStateCategory; dependent-state-category-simple;
    simple-state-category)
open import Category.Split
  using (DependentSplitFunctor; DependentSplitFunctor')
open import Category.Split.Core
  using (DependentSplitBase; SplitBase; split-base-from-retraction)
open import Category.State
  using (DependentStateCategory)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Retraction
  using (Retraction)

-- ## Dependent

-- ### DependentSimpleSplitPrefunctor

record DependentSimpleSplitPrefunctor
  {n : ℕ}
  {C : ChainCategory n}
  (C' : DependentSimpleStateCategory C)
  (D' : DependentSimplePrecategory C)
  : Set
  where

  field

    {base}
      : DependentSplitBase
        (DependentSimpleStateCategory.object C')
        (DependentSimplePrecategory.object D')

    lift
      : DependentSimpleSplitPrelift
        (DependentSimpleStateCategory.lift C')
        (DependentSimplePrecategory.lift D') base

-- ### DependentSimpleSplitPrefunctor'

record DependentSimpleSplitPrefunctor'
  {n : ℕ}
  {C : ChainCategory n}
  (C' : DependentSimpleCategory C)
  (D' : DependentSimplePrecategory' C)
  : Set
  where

  field

    {base}
      : DependentSplitBase
        (DependentSimpleCategory.object C')
        (DependentSimplePrecategory'.object D')

    lift
      : DependentSimpleSplitPrelift'
        (DependentSimpleCategory.lift C')
        (DependentSimplePrecategory'.lift D') base

-- ### DependentSimpleSplitFunctor

-- #### Definition

record DependentSimpleSplitFunctor''
  {n : ℕ}
  {C : ChainCategory n}
  (C' : DependentSimpleStateCategory C)
  (D' : DependentSimpleCategory C)
  : Set
  where

  field

    {base}
      : DependentSplitBase
        (DependentSimpleStateCategory.object C')
        (DependentSimpleCategory.object D')

    lift
      : DependentSimpleSplitLift
        (DependentSimpleStateCategory.lift C')
        (DependentSimpleCategory.lift D') base

DependentSimpleSplitFunctor
  = DependentSimpleSplitFunctor''

-- #### Module

module DependentSimpleSplitFunctor where

  open module DependentSimpleSplitFunctor'''' {n C C' D'} F
    = DependentSimpleSplitFunctor'' {n} {C} {C'} {D'} F public

  tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentSimpleStateCategory C}
    → {D' : DependentSimpleCategory C}
    → DependentSimpleSplitFunctor C' D'
    → (x : ChainCategory.Object C)
    → DependentSimpleSplitFunctor
      (DependentSimpleStateCategory.tail C' x)
      (DependentSimpleCategory.tail D' x)
  tail F x
    = record
    { lift
      = DependentSimpleSplitLift.tail (lift F) x
    }

  partial-function
    : {n : ℕ}
    → {C : ChainCategory n}
    → {C' : DependentSimpleStateCategory C}
    → {D' : DependentSimpleCategory C}
    → DependentSimpleSplitFunctor C' D'
    → DependentSimplePartialFunction C'
      (DependentSimpleCategory.set D')
  partial-function {n = zero} F
    = SplitBase.base (base F)
  partial-function {n = suc _} F
    = record
    { tail
      = λ x → partial-function (tail F x)
    }

  bool-function
    : {n : ℕ}
    → {C : ChainCategory n}
    → {C' : DependentSimpleStateCategory C}
    → {D' : DependentSimpleCategory C}
    → DependentSimpleSplitFunctor C' D'
    → DependentSimpleBoolFunction C'
  bool-function {n = zero} F
    = SplitBase.bool-function (base F)
  bool-function {n = suc _} F
    = record
    { tail
      = λ x → bool-function (tail F x)
    }

-- #### Conversion

dependent-split-functor-simple
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentStateCategory C}
  → {D' : DependentCategory C}
  → DependentSplitFunctor C' D'
  → DependentSimpleSplitFunctor
    (dependent-state-category-simple C')
    (dependent-category-simple D')
dependent-split-functor-simple F
  = record
  { lift
    = dependent-split-lift-simple
      (DependentSplitFunctor.lift F)
  }

-- ### DependentSimpleSplitFunctor'

-- #### Definition

record DependentSimpleSplitFunctor'''
  {n : ℕ}
  {C : ChainCategory n}
  (C' D' : DependentSimpleCategory C)
  : Set
  where

  field

    {base}
      : DependentSplitBase
        (DependentSimpleCategory.object C')
        (DependentSimpleCategory.object D')

    lift
      : DependentSimpleSplitLift'
        (DependentSimpleCategory.lift C')
        (DependentSimpleCategory.lift D') base

DependentSimpleSplitFunctor'
  = DependentSimpleSplitFunctor'''

-- #### Module

module DependentSimpleSplitFunctor' where

  open module DependentSimpleSplitFunctor'''' {n C C' D'} F
    = DependentSimpleSplitFunctor''' {n} {C} {C'} {D'} F public

  tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' D' : DependentSimpleCategory C}
    → DependentSimpleSplitFunctor' C' D'
    → (x : ChainCategory.Object C)
    → DependentSimpleSplitFunctor'
      (DependentSimpleCategory.tail C' x)
      (DependentSimpleCategory.tail D' x)
  tail F x
    = record
    { lift
      = DependentSimpleSplitLift'.tail (lift F) x
    }

-- #### Conversion

dependent-split-functor-simple'
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' D' : DependentCategory C}
  → DependentSplitFunctor' C' D'
  → DependentSimpleSplitFunctor'
    (dependent-category-simple C')
    (dependent-category-simple D')
dependent-split-functor-simple' F
  = record
  { lift
    = dependent-split-lift-simple'
      (DependentSplitFunctor'.lift F)
  }

-- ## Nondependent

-- ### SimpleSplitFunctor

-- #### Definition

SimpleSplitFunctor
  : Set
  → Set
  → Set
SimpleSplitFunctor A B
  = DependentSimpleSplitFunctor
    (simple-state-category A)
    (simple-category B)

-- #### Module

module SimpleSplitFunctor
  {A B : Set}
  (F : SimpleSplitFunctor A B)
  where

  open DependentSimpleSplitFunctor'' F public

  open SplitBase base public
    using () renaming
    ( base
      to base'
    ; unbase
      to unbase
    ; base-unbase
      to base-unbase
    )

-- #### Conversion

simple-split-functor-from-retraction
  : {A B : Set}
  → Retraction A B
  → SimpleSplitFunctor A B
simple-split-functor-from-retraction F
  = record
  { base
    = split-base-from-retraction F
  }

-- ### SimpleSplitFunctor'

-- #### Definition

SimpleSplitFunctor'
  : Set
  → Set
  → Set
SimpleSplitFunctor' A B
  = DependentSimpleSplitFunctor'
    (simple-category A)
    (simple-category B)

-- #### Module

module SimpleSplitFunctor'
  = DependentSimpleSplitFunctor'

