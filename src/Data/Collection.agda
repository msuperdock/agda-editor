module Data.Collection where

open import Data.Empty
  using (⊥-elim)
open import Data.Equal
  using (_≡_; refl)
open import Data.Fin
  using (Fin; _≟_fin)
open import Data.Function
  using (_$_)
open import Data.List
  using (List)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Relation
  using (Dec; Decidable; Relation; no; yes)

-- ## Definition

record Collection'
  {A : Set}
  (R : Relation A)
  : Set
  where
  
  constructor

    collection

  field
  
    elements
      : List A
    
    .valid
      : (k₁ k₂ : Fin (List.length elements))
      → R (List.lookup elements k₁) (List.lookup elements k₂)
      → k₁ ≡ k₂

Collection
  = Collection'

-- ## Module

module Collection where

  open Collection' public

  from-list'
    : {A : Set}
    → (R : Relation A)
    → Decidable R
    → (xs : List A)
    → Dec ((k₁ k₂ : Fin (List.length xs))
      → R (List.lookup xs k₁) (List.lookup xs k₂)
      → k₁ ≡ k₂)
  from-list' R d xs
    = Fin.dec (λ (k₁ : Fin (List.length xs))
      → (k₂ : Fin (List.length xs))
      → R (List.lookup xs k₁) (List.lookup xs k₂)
      → k₁ ≡ k₂)
    $ λ k₁
      → Fin.dec (λ (k₂ : Fin (List.length xs))
      → R (List.lookup xs k₁) (List.lookup xs k₂)
      → k₁ ≡ k₂)
    $ λ k₂ → Dec.function
      (d (List.lookup xs k₁) (List.lookup xs k₂))
      (k₁ ≟ k₂ fin)

  from-list
    : {A : Set}
    → (R : Relation A)
    → Decidable R
    → List A
    → Maybe (Collection R)
  from-list R d xs
    with from-list' R d xs
  ... | no _
    = nothing
  ... | yes p
    = just (collection xs p)

  from-list-elements
    : {A : Set}
    → (R : Relation A)
    → (d : Decidable R)
    → (xs : Collection R)
    → from-list R d (elements xs) ≡ just xs
  from-list-elements R d (collection xs p)
    with from-list' R d xs
  ... | no ¬p
    = ⊥-elim (¬p p)
  ... | yes _
    = refl

