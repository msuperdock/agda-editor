module Category.Simple.Relation where

open import Category
  using (ChainCategory)
open import Category.Simple
  using (DependentSet; DependentSimpleCategory; simple-category)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Relation
  using (Decidable; Relation)

open import Category.Core.Relation
  using () renaming
  ( DependentDecidable
    to DependentDecidable''
  ; DependentRelation
    to DependentRelation''
  )

-- ## Dependent

-- ### DependentRelation

-- #### Types

DependentRelation
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSet C
  → Set₁

record DependentRelation'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentSet C)
  : Set₁

-- #### Definitions

DependentRelation {n = zero}
  = Relation
DependentRelation {n = suc _}
  = DependentRelation'

record DependentRelation' {_ C} C' where

  inductive
  no-eta-equality

  field

    tail
      : (x : ChainCategory.Object C)
      → DependentRelation
        (DependentSet.tail C' x)

module DependentRelation
  = DependentRelation'

-- ### DependentDecidable

-- #### Types

DependentDecidable
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C' : DependentSet C)
  → DependentRelation C'
  → Set

record DependentDecidable'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentSet C)
  (R : DependentRelation C')
  : Set

-- #### Definitions

DependentDecidable {n = zero} _
  = Decidable
DependentDecidable {n = suc _} C'
  = DependentDecidable' C'

record DependentDecidable' {_ C} C' R where

  inductive

  field

    tail
      : (x : ChainCategory.Object C)
      → DependentDecidable
        (DependentSet.tail C' x)
        (DependentRelation.tail R x)

module DependentDecidable
  = DependentDecidable'

-- ### DependentSimpleRelation

-- #### Definition

record DependentSimpleRelation
  {n : ℕ}
  {C : ChainCategory n}
  (C' : DependentSimpleCategory C)
  : Set₁
  where

  no-eta-equality

  field

    object
      : DependentRelation''
        (DependentSimpleCategory.object C')

-- #### Construction

simple-relation
  : {A : Set}
  → Relation A
  → DependentSimpleRelation (simple-category A)
simple-relation R
  = record
  { object
    = R
  }

-- ### DependentSimpleDecidable

-- #### Definition

record DependentSimpleDecidable
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentSimpleCategory C}
  (R : DependentSimpleRelation C')
  : Set
  where

  field

    object
      : DependentDecidable''
        (DependentSimpleRelation.object R)

-- #### Construction

simple-decidable
  : {A : Set}
  → (R : Relation A)
  → Decidable R
  → DependentSimpleDecidable (simple-relation R)
simple-decidable _ d
  = record
  { object
    = d
  }

