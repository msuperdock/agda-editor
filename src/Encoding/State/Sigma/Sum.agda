module Encoding.State.Sigma.Sum where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Snoc
  using (chain-category-snoc)
open import Category.Split
  using (DependentSplitFunctor)
open import Category.State
  using (DependentStateCategory; DependentStateCategory₁)
open import Category.State.Sigma.Sum
  using (dependent-state-category-sigma-sum)
open import Data.Equal
  using (_≡_; refl)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ; _×_; _,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)
open import Encoding
  using (DependentEncoding; Encoding)
open import Encoding.State
  using (DependentStateEncoding)

-- ## Base

module _
  {A₁ B₁ C₁ C₂ D₁ : Set}
  where

  module EncodingSigmaSum
    (A₂ : B₁ → Set)
    (e₁ : Encoding A₁ C₁)
    (f₁ : Encoding B₁ D₁)
    (e₂ : (x₁ : B₁) → Encoding (A₂ x₁) C₂)
    where

    encode
      : A₁ ⊔ Σ B₁ A₂
      → C₁ ⊔ D₁ × C₂
    encode (ι₁ x₁)
      = ι₁ (Encoding.encode e₁ x₁)
    encode (ι₂ (x₁ , x₂))
      = ι₂ (Encoding.encode f₁ x₁ , Encoding.encode (e₂ x₁) x₂)
    
    decode
      : C₁ ⊔ D₁ × C₂
      → Maybe (A₁ ⊔ Σ B₁ A₂)
    decode (ι₁ x₁')
      with Encoding.decode e₁ x₁'
    ... | nothing
      = nothing
    ... | just x₁
      = just (ι₁ x₁)
    decode (ι₂ (x₁' , x₂'))
      with Encoding.decode f₁ x₁'
    ... | nothing
      = nothing
    ... | just x₁
      with Encoding.decode (e₂ x₁) x₂'
    ... | nothing
      = nothing
    ... | just x₂
      = just (ι₂ (x₁ , x₂))

    decode-encode
      : (x : A₁ ⊔ Σ B₁ A₂)
      → decode (encode x) ≡ just x
    decode-encode (ι₁ x₁)
      with Encoding.decode e₁ (Encoding.encode e₁ x₁)
      | Encoding.decode-encode e₁ x₁
    ... | _ | refl
      = refl
    decode-encode (ι₂ (x₁ , x₂))
      with Encoding.decode f₁ (Encoding.encode f₁ x₁)
      | Encoding.decode-encode f₁ x₁
    ... | _ | refl
      with Encoding.decode (e₂ x₁) (Encoding.encode (e₂ x₁) x₂)
      | Encoding.decode-encode (e₂ x₁) x₂
    ... | _ | refl
      = refl

  encoding-sigma-sum
    : (A₂ : B₁ → Set)
    → Encoding A₁ C₁
    → Encoding B₁ D₁
    → ((x₁ : B₁) → Encoding (A₂ x₁) C₂)
    → Encoding (A₁ ⊔ Σ B₁ A₂) (C₁ ⊔ D₁ × C₂)
  encoding-sigma-sum A₂ e₁ f₁ e₂
    = record {EncodingSigmaSum A₂ e₁ f₁ e₂}

-- ## Dependent

dependent-state-encoding-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentStateCategory C}
  → {D₁' : DependentCategory C}
  → {C₂' : DependentStateCategory (chain-category-snoc D₁')}
  → {A₁ A₂ B₁ : Set}
  → (F₁ : DependentSplitFunctor C₁' D₁')
  → DependentStateEncoding C₁' A₁
  → DependentEncoding D₁' B₁
  → DependentStateEncoding C₂' A₂
  → DependentStateEncoding
    (dependent-state-category-sigma-sum C₂' F₁)
    (A₁ ⊔ B₁ × A₂)
dependent-state-encoding-sigma-sum {n = zero} {D₁' = D₁'} {C₂' = C₂'} _ e₁ f₁ e₂
  = encoding-sigma-sum
    (DependentStateCategory₁.Object D₁' C₂') e₁ f₁
    (DependentStateEncoding.tail e₂)
dependent-state-encoding-sigma-sum {n = suc _} F₁ e₁ f₁ e₂
  = record
  { tail
    = λ x → dependent-state-encoding-sigma-sum
      (DependentSplitFunctor.tail F₁ x)
      (DependentStateEncoding.tail e₁ x)
      (DependentEncoding.tail f₁ x)
      (DependentStateEncoding.tail e₂ x)
  }

