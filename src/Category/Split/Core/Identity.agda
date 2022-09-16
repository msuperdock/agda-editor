module Category.Split.Core.Identity where

open import Category.Core
  using (ChainObject; DependentObject; Object')
open import Category.Split.Core
  using (DependentSplitBase; SplitBase)
open import Data.Equal
  using (refl)
open import Data.Function
  using (id)
open import Data.Maybe
  using (just)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### SplitBase

split-base-identity
  : (X : Object')
  → SplitBase X X
split-base-identity _
  = record
  { base
    = just
  ; unbase
    = id
  ; base-unbase
    = λ _ → refl
  }

-- ## Dependent

-- ### DependentSplitBase

dependent-split-base-identity
  : {n : ℕ}
  → {X : ChainObject n}
  → (X' : DependentObject X)
  → DependentSplitBase X' X'
dependent-split-base-identity {n = zero} X'
  = split-base-identity X'
dependent-split-base-identity {n = suc _} X'
  = record
  { tail
    = λ x → dependent-split-base-identity
      (DependentObject.tail X' x)
  }

