module Data.Equal where

open import Data.Empty
  using (¬_)

-- ## Definition

infix 4 _≅_
infix 4 _≡_
infix 4 _≢_

data _≅_
  {A : Set}
  (x : A)
  : {B : Set}
  → B
  → Set
  where

  refl
    : x ≅ x

Equal
  : (A : Set)
  → A
  → A
  → Set
Equal _ x₁ x₂
  = x₁ ≅ x₂

_≡_
  : {A : Set}
  → A
  → A
  → Set
x₁ ≡ x₂
  = x₁ ≅ x₂

_≢_
  : {A : Set}
  → A
  → A
  → Set
x₁ ≢ x₂
  = ¬ x₁ ≡ x₂

-- ## Module

module Equal where

  -- ### Interface

  sym
    : {A₁ A₂ : Set}
    → {x₁ : A₁}
    → {x₂ : A₂}
    → x₁ ≅ x₂
    → x₂ ≅ x₁
  sym refl
    = refl

  trans
    : {A₁ A₂ A₃ : Set}
    → {x₁ : A₁}
    → {x₂ : A₂}
    → {x₃ : A₃}
    → x₁ ≅ x₂
    → x₂ ≅ x₃
    → x₁ ≅ x₃
  trans refl p
    = p

  sub
    : {A B : Set}
    → {x₁ x₂ : A}
    → (P : A → B)
    → x₁ ≡ x₂
    → P x₁ ≡ P x₂
  sub _ refl
    = refl

  -- ### Irrelevance

  irrelevant
    : {A₁ A₂ : Set}
    → {x₁ : A₁}
    → {x₂ : A₂}
    → (p₁ p₂ : x₁ ≅ x₂)
    → p₁ ≡ p₂
  irrelevant refl refl
    = refl

  -- ### Rewrite

  rewrite'
    : {A : Set}
    → {x₁ x₂ : A}
    → (P : A → Set)
    → x₁ ≡ x₂
    → P x₂
    → P x₁
  rewrite' _ refl p
    = p

-- ## Exports

open Equal public
  using (rewrite'; sub; sym; trans)

