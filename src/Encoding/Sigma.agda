module Encoding.Sigma where

open import Category
  using (ChainCategory; DependentCategory; DependentCategory₁)
open import Category.Sigma
  using (dependent-category-sigma)
open import Category.Snoc
  using (chain-category-snoc)
open import Data.Equal
  using (_≡_; refl)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ; _×_; _,_)
open import Encoding
  using (DependentEncoding; Encoding)

-- ## Base

module _
  {A₁ B₁ B₂ : Set}
  where

  module EncodingSigma
    (A₂ : A₁ → Set)
    (e₁ : Encoding A₁ B₁)
    (e₂ : ((x₁ : A₁) → Encoding (A₂ x₁) B₂))
    where

    encode
      : Σ A₁ A₂
      → B₁ × B₂
    encode (x₁ , x₂)
      = Encoding.encode e₁ x₁
      , Encoding.encode (e₂ x₁) x₂
    
    decode
      : B₁ × B₂
      → Maybe (Σ A₁ A₂)
    decode (x₁' , x₂')
      with Encoding.decode e₁ x₁'
    ... | nothing
      = nothing
    ... | just x₁
      with Encoding.decode (e₂ x₁) x₂'
    ... | nothing
      = nothing
    ... | just x₂
      = just (x₁ , x₂)

    decode-encode
      : (x : Σ A₁ A₂)
      → decode (encode x) ≡ just x
    decode-encode (x₁ , x₂)
      with Encoding.decode e₁ (Encoding.encode e₁ x₁)
      | Encoding.decode-encode e₁ x₁
    ... | _ | refl
      with Encoding.decode (e₂ x₁) (Encoding.encode (e₂ x₁) x₂)
      | Encoding.decode-encode (e₂ x₁) x₂
    ... | _ | refl
      = refl

  encoding-sigma
    : (A₂ : A₁ → Set)
    → Encoding A₁ B₁
    → ((x₁ : A₁) → Encoding (A₂ x₁) B₂)
    → Encoding (Σ A₁ A₂) (B₁ × B₂)
  encoding-sigma A₂ e₁ e₂
    = record {EncodingSigma A₂ e₁ e₂}

-- ## Dependent

dependent-encoding-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentCategory (chain-category-snoc C₁')}
  → {A₁ A₂ : Set}
  → DependentEncoding C₁' A₁
  → DependentEncoding C₂' A₂
  → DependentEncoding
    (dependent-category-sigma C₁' C₂')
    (A₁ × A₂)
dependent-encoding-sigma {n = zero} {C₁' = C₁'} {C₂' = C₂'} e₁ e₂
  = encoding-sigma
    (DependentCategory₁.Object C₁' C₂') e₁
    (DependentEncoding.tail e₂)
dependent-encoding-sigma {n = suc _} e₁ e₂
  = record
  { tail
    = λ x → dependent-encoding-sigma
      (DependentEncoding.tail e₁ x)
      (DependentEncoding.tail e₂ x)
  }

