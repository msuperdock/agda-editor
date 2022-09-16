module Data.Nat where

open import Data.Equal
  using (refl)
open import Data.Relation
  using (Trichotomous; τ₁; τ₂; τ₃)

import Agda.Builtin.Nat as Builtin

-- ## Definition

open Builtin public
  using () renaming
  ( Nat
    to ℕ
  )

open ℕ public

-- ## Module

module Nat where

  -- ### Interface

  open Builtin public
    using (_+_; _*_)

  -- ### Comparison

  data _<_nat
    : ℕ
    → ℕ
    → Set
    where
  
    z<s
      : {n₂ : ℕ}
      → zero < suc n₂ nat
  
    s<s
      : {n₁ n₂ : ℕ}
      → n₁ < n₂ nat
      → suc n₁ < suc n₂ nat
  
  compare
    : Trichotomous _<_nat
  compare zero zero
    = τ₂ (λ ()) refl (λ ())
  compare zero (suc _)
    = τ₁ z<s (λ ()) (λ ())
  compare (suc _) zero
    = τ₃ (λ ()) (λ ()) z<s
  compare (suc m) (suc n)
    with compare m n
  ... | τ₁ l ¬p ¬g
    = τ₁ (s<s l) (λ {refl → ¬p refl}) (λ {(s<s g) → ¬g g})
  ... | τ₂ ¬l refl ¬g
    = τ₂ (λ {(s<s l) → ¬l l}) refl (λ {(s<s g) → ¬g g})
  ... | τ₃ ¬l ¬p g
    = τ₃ (λ {(s<s l) → ¬l l}) (λ {refl → ¬p refl}) (s<s g)

-- ## Exports

open Nat public
  using (_+_; _*_)

