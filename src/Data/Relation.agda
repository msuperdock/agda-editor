module Data.Relation where

open import Data.Empty
  using (¬_; ⊥-elim)
open import Data.Equal
  using (_≡_)
open import Data.Function
  using (const)

-- ## Relation

Relation
  : Set
  → Set₁
Relation A
  = A
  → A
  → Set

-- ## Decidable

data Dec'
  (P : Set)
  : Set
  where

  yes
    : P
    → Dec' P
  no
    : ¬ P
    → Dec' P

Dec
  = Dec'

module Dec where

  function
    : {P Q : Set}
    → Dec P
    → Dec Q
    → Dec (P → Q)
  function (no ¬p) _
    = yes (λ p → ⊥-elim (¬p p))
  function (yes p) (no ¬q)
    = no (λ f → ¬q (f p))
  function _ (yes q)
    = yes (const q)

Decidable
  : {A : Set}
  → Relation A
  → Set
Decidable {A = A} R
  = (x₁ x₂ : A)
  → Dec (R x₁ x₂)

-- ## Trichotomous

data Tri
  (P₁ P₂ P₃ : Set)
  : Set
  where

  τ₁
    : P₁
    → ¬ P₂
    → ¬ P₃
    → Tri P₁ P₂ P₃

  τ₂
    : ¬ P₁
    → P₂
    → ¬ P₃
    → Tri P₁ P₂ P₃

  τ₃
    : ¬ P₁
    → ¬ P₂
    → P₃
    → Tri P₁ P₂ P₃

Trichotomous
  : {A : Set}
  → Relation A
  → Set
Trichotomous {A = A} R
  = (x₁ x₂ : A)
  → Tri (R x₁ x₂) (x₁ ≡ x₂) (R x₂ x₁)

