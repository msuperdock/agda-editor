module Category.Core.Relation where

open import Category.Core
  using (ChainObject; DependentObject; Object')
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Relation
  using (Decidable; Relation)

-- ## Dependent

-- ### DependentRelation

-- #### Types

DependentRelation
  : {n : ℕ}
  → {X : ChainObject n}
  → DependentObject X
  → Set₁

record DependentRelation'
  {n : ℕ}
  {X : ChainObject (suc n)}
  (X' : DependentObject X)
  : Set₁

-- #### Definitions

DependentRelation {n = zero} X'
  = Relation (Object'.Object X')
DependentRelation {n = suc _} X'
  = DependentRelation' X'

record DependentRelation' {_ X} X' where

  inductive
  no-eta-equality

  field

    tail
      : (x : ChainObject.Object X)
      → DependentRelation
        (DependentObject.tail X' x)

module DependentRelation
  = DependentRelation'

-- ### DependentDecidable

-- #### Types

DependentDecidable
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → DependentRelation X'
  → Set

record DependentDecidable'
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' : DependentObject X}
  (R : DependentRelation X')
  : Set

-- #### Definitions

DependentDecidable {n = zero}
  = Decidable
DependentDecidable {n = suc _}
  = DependentDecidable'

record DependentDecidable' {_ X} R where

  inductive

  field

    tail
      : (x : ChainObject.Object X)
      → DependentDecidable
        (DependentRelation.tail R x)

module DependentDecidable
  = DependentDecidable'

