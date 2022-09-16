module Data.Fin where

open import Data.Empty
  using (¬_; ⊥-elim)
open import Data.Equal
  using (Equal; _≡_; refl; sub)
open import Data.Function
  using (_∘_)
open import Data.Inspect
  using (inspect; [_])
open import Data.Maybe
  using (Maybe; just; maybe; nothing)
open import Data.Nat
  using (ℕ; zero; suc)
open import Data.Relation
  using (Dec; Decidable; Trichotomous; τ₁; τ₂; τ₃; no; yes)

-- ## Definition

data Fin'
  : ℕ
  → Set
  where

  zero
    : {n : ℕ}
    → Fin' (suc n)
  suc
    : {n : ℕ}
    → Fin' n
    → Fin' (suc n)

Fin
  = Fin'

-- ## Module

module Fin where

  open Fin' public

  -- ### Interface

  increment
    : {n : ℕ}
    → Fin n
    → Maybe (Fin n)
  increment {n = suc zero} zero
    = nothing
  increment {n = suc (suc _)} zero
    = just (suc zero)
  increment (suc k)
    = Maybe.map suc (increment k)

  decrement
    : {n : ℕ}
    → Fin n
    → Maybe (Fin n)
  decrement zero
    = nothing
  decrement (suc k)
    = just (maybe (decrement k) zero suc)

  maximum
    : (n : ℕ)
    → Fin (suc n)
  maximum zero
    = zero
  maximum (suc n)
    = suc (maximum n)

  lift
    : {n : ℕ}
    → Fin n
    → Fin (suc n)
  lift zero
    = zero
  lift (suc k)
    = suc (lift k)

  drop
    : {n : ℕ}
    → Fin (suc n)
    → Maybe (Fin n)
  drop {n = zero} zero
    = nothing
  drop {n = suc _} zero
    = just zero
  drop {n = suc _} (suc k)
    = Maybe.map suc (drop k)

  -- ### Conversion

  to-nat
    : {n : ℕ}
    → Fin n
    → ℕ
  to-nat zero
    = zero
  to-nat (suc k)
    = suc (to-nat k)

  -- ### Equality

  _≟_fin
    : {n : ℕ}
    → Decidable (Equal (Fin n))
  
  zero ≟ zero fin
    = yes refl
  suc k₁ ≟ suc k₂ fin
    with k₁ ≟ k₂ fin
  ... | no ¬eq
    = no (λ {refl → ¬eq refl})
  ... | yes refl
    = yes refl
  
  zero ≟ suc _ fin
    = no (λ ())
  suc _ ≟ zero fin
    = no (λ ())

  -- ### Comparison

  data _<_fin
    : {n : ℕ}
    → Fin n
    → Fin n
    → Set
    where

    z<s
      : {n : ℕ}
      → {k₂ : Fin n}
      → zero < suc k₂ fin

    s<s
      : {n : ℕ}
      → {k₁ k₂ : Fin n}
      → k₁ < k₂ fin
      → suc k₁ < suc k₂ fin

  compare
    : {n : ℕ}
    → Trichotomous (_<_fin {n = n})
  compare zero zero
    = τ₂ (λ ()) refl (λ ())
  compare zero (suc _)
    = τ₁ z<s (λ ()) (λ ())
  compare (suc _) zero
    = τ₃ (λ ()) (λ ()) z<s
  compare (suc k₁) (suc k₂)
    with compare k₁ k₂
  ... | τ₁ p₁ ¬p₂ ¬p₃
    = τ₁ (s<s p₁) (λ {refl → ¬p₂ refl}) (λ {(s<s p₃) → ¬p₃ p₃})
  ... | τ₂ ¬p₁ p₂ ¬p₃
    = τ₂ (λ {(s<s p₁) → ¬p₁ p₁}) (sub suc p₂) (λ {(s<s p₃) → ¬p₃ p₃})
  ... | τ₃ ¬p₁ ¬p₂ p₃
    = τ₃ (λ {(s<s p₁) → ¬p₁ p₁}) (λ {refl → ¬p₂ refl}) (s<s p₃)

  <-¬refl
    : {n : ℕ}
    → {k : Fin n}
    → ¬ k < k fin
  <-¬refl {k = k}
    with compare k k
  ... | τ₁ _ ¬p₂ _
    = ⊥-elim (¬p₂ refl)
  ... | τ₂ ¬p₁ _ _
    = ¬p₁
  ... | τ₃ ¬p₁ _ _
    = ¬p₁

  <-¬refl'
    : {n : ℕ}
    → {k₁ k₂ : Fin n}
    → k₁ ≡ k₂
    → ¬ k₁ < k₂ fin
  <-¬refl' refl
    = <-¬refl

  <-trans
    : {n : ℕ}
    → {k₁ k₂ k₃ : Fin n}
    → k₁ < k₂ fin
    → k₂ < k₃ fin
    → k₁ < k₃ fin
  <-trans z<s (s<s _)
    = z<s
  <-trans (s<s p₁) (s<s p₂)
    = s<s (<-trans p₁ p₂)

  <-suc
    : {n : ℕ}
    → (k : Fin n)
    → lift k < suc k fin
  <-suc zero
    = z<s
  <-suc (suc p)
    = s<s (<-suc p)

  <-¬suc
    : {n : ℕ}
    → {k : Fin n}
    → {k' : Fin (suc n)}
    → lift k < k' fin
    → ¬ k' < suc k fin
  <-¬suc {k = suc _} (s<s p) (s<s q)
    = <-¬suc p q

  -- ### Decidability

  dec
    : {n : ℕ}
    → (P : Fin n → Set)
    → ((k : Fin n) → Dec (P k))
    → Dec ((k : Fin n) → P k)
  dec {n = zero} _ _
    = yes (λ ())
  dec {n = suc _} P d
    with d zero
    | dec (P ∘ suc) (d ∘ suc)
  ... | no ¬q | _
    = no (λ f → ¬q (f zero))
  ... | _ | no ¬f
    = no (λ f → ¬f (f ∘ suc))
  ... | yes q | yes f
    = yes (λ {zero → q; (suc k) → f k})

  -- ### Properties

  suc-injective
    : {n : ℕ}
    → {k₁ k₂ : Fin n}
    → Equal (Fin (suc n)) (suc k₁) (suc k₂)
    → k₁ ≡ k₂
  suc-injective refl
    = refl

  lift-injective
    : {n : ℕ}
    → (k₁ k₂ : Fin n)
    → lift k₁ ≡ lift k₂
    → k₁ ≡ k₂
  lift-injective zero zero _
    = refl
  lift-injective (suc k₁) (suc k₂) p
    = sub suc (lift-injective k₁ k₂ (suc-injective p))

  increment-nothing
    : {n : ℕ}
    → (k : Fin (suc n))
    → increment k ≡ nothing
    → k ≡ maximum n
  increment-nothing {n = zero} zero _
    = refl
  increment-nothing {n = suc _} (suc k) p
    = sub suc (increment-nothing k (Maybe.map-nothing suc (increment k) p))

  increment-just
    : {n : ℕ}
    → (k : Fin (suc n))
    → {k' : Fin (suc n)}
    → increment k ≡ just k'
    → to-nat k' ≡ suc (to-nat k)
  increment-just {n = suc _} zero refl
    = refl
  increment-just (suc k) _
    with increment k
    | inspect increment k
  increment-just {n = suc _} (suc k) refl | just _ | [ p ]
    = sub suc (increment-just k p)

  increment-maximum
    : (n : ℕ)
    → increment (maximum n) ≡ nothing
  increment-maximum zero
    = refl
  increment-maximum (suc n)
    = sub (Maybe.map suc) (increment-maximum n)

  drop-just
    : {n : ℕ}
    → {k' : Fin n}
    → (k : Fin (suc n))
    → drop k ≡ just k'
    → k ≡ lift k'
  drop-just {n = suc _} zero refl
    = refl
  drop-just {n = suc _} (suc k) _
    with drop k
    | inspect drop k
  drop-just (suc k) refl | just _ | [ p ]
    = sub suc (drop-just k p)

-- ## Exports

open Fin public
  using (_≟_fin; _<_fin; s<s; z<s)

