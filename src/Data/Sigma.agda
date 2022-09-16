module Data.Sigma where

open import Agda.Primitive
  using (Level; _⊔_)

open import Data.Equal
  using (_≡_; refl)
open import Data.Pair
  using (Pair; pair)

import Agda.Builtin.Sigma
  as Builtin

-- ## Definition

Σ
  : {ℓ₁ ℓ₂ : Level}
  → (A₁ : Set ℓ₁)
  → (A₁ → Set ℓ₂)
  → Set (ℓ₁ ⊔ ℓ₂)
Σ
  = Builtin.Σ

infix 2 Σ

syntax Σ A₁ (λ x → A₂)
  = x ∈ A₁ × A₂

open Builtin public
  using () renaming
  ( _,_
    to _,_
  ; fst
    to π₁
  ; snd
    to π₂
  )

-- ## Module

module Sigma where

  -- ### Interface

  infixr 2 _×_

  _×_
    : Set
    → Set
    → Set
  A₁ × A₂
    = _ ∈ A₁ × A₂

  -- ### Conversion

  to-pair
    : {A₁ A₂ : Set}
    → A₁ × A₂
    → Pair A₁ A₂
  to-pair (x₁ , x₂)
    = pair x₁ x₂

  -- ### Properties

  comma-injective₁
    : {A₁ : Set}
    → {A₂ : A₁ → Set}
    → {x₁₁ x₂₁ : A₁}
    → {x₁₂ : A₂ x₁₁}
    → {x₂₂ : A₂ x₂₁}
    → (x₁₁ , x₁₂) ≡ (x₂₁ , x₂₂)
    → x₁₁ ≡ x₂₁
  comma-injective₁ refl
    = refl

-- ## Exports

open Sigma public
  using (_×_)

