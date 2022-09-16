module Category.Relation where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Data.Nat
  using (ℕ)
open import Data.Relation
  using (Decidable; Relation)

open import Category.Core.Relation
  using () renaming
  ( DependentDecidable
    to DependentDecidable'
  ; DependentRelation
    to DependentRelation'
  )

-- ## Dependent

-- ### DependentRelation

-- #### Definition

record DependentRelation
  {n : ℕ}
  {C : ChainCategory n}
  (C' : DependentCategory C)
  : Set₁
  where

  no-eta-equality

  field

    object
      : DependentRelation'
        (DependentCategory.object C')

-- #### Construction

relation
  : (C : Category)
  → Relation (Category.Object C)
  → DependentRelation C
relation _ R
  = record
  { object
    = R
  }

-- ### DependentDecidable

-- #### Definition

record DependentDecidable
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  (R : DependentRelation C')
  : Set₁
  where

  field

    object
      : DependentDecidable'
        (DependentRelation.object R)

-- #### Construction

decidable
  : (C : Category)
  → (R : Relation (Category.Object C))
  → Decidable R
  → DependentDecidable (relation C R)
decidable _ _ d
  = record
  { object
    = d
  }

