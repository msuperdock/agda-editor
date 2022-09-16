module Category.State.Lift.Product where

open import Category.Core
  using (Arrow'; ChainArrow; ChainIdentity; ChainObject; DependentArrow;
    DependentIdentity; DependentObject; Identity; Object')
open import Category.Core.Product
  using (arrow-equal-product; arrow-product; dependent-arrow-product;
    dependent-identity-product; identity-product; object-product)
open import Category.Lift
  using (ChainLift; ChainPath)
open import Category.State.Lift
  using (DependentStateLift; DependentStatePath; DependentStatePathEqual;
    DependentStatePathIdentity; StatePath; StatePathEqual; StatePathIdentity;
    tt)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (_,_)

-- ## Base

-- ### StatePath

module _
  {X₁ X₂ Y₁ Y₂ : Object'}
  {F₁ : Arrow' X₁ Y₁}
  {F₂ : Arrow' X₂ Y₂}
  where

  module StatePathProduct
    (p₁ : StatePath F₁)
    (p₂ : StatePath F₂)
    where

    base
      : Object'.Object (object-product X₁ X₂)
      → Object'.Object (object-product Y₁ Y₂)
    base (x₁ , x₂)
      = StatePath.base p₁ x₁
      , StatePath.base p₂ x₂

    map
      : (x : Object'.Object (object-product X₁ X₂))
      → Arrow'.Arrow (arrow-product F₁ F₂) x (base x)
    map (x₁ , x₂)
      = StatePath.map p₁ x₁
      , StatePath.map p₂ x₂

  state-path-product
    : StatePath F₁
    → StatePath F₂
    → StatePath
      (arrow-product F₁ F₂)
  state-path-product p₁ p₂
    = record {StatePathProduct p₁ p₂}

-- ### StatePathEqual

module _
  {X₁ X₂ Y₁ Y₂ : Object'}
  {F₁ : Arrow' X₁ Y₁}
  {F₂ : Arrow' X₂ Y₂}
  {p₁₁ p₂₁ : StatePath F₁}
  {p₁₂ p₂₂ : StatePath F₂}
  where

  module StatePathEqualProduct
    (q₁ : StatePathEqual p₁₁ p₂₁)
    (q₂ : StatePathEqual p₁₂ p₂₂)
    where

    map
      : (x : Object'.Object (object-product X₁ X₂))
      → Arrow'.ArrowEqual' (arrow-product F₁ F₂)
        (StatePath.map (state-path-product p₁₁ p₁₂) x)
        (StatePath.map (state-path-product p₂₁ p₂₂) x)
    map (x₁ , x₂)
      = arrow-equal-product
        (StatePathEqual.map q₁ x₁)
        (StatePathEqual.map q₂ x₂)

  state-path-equal-product
    : StatePathEqual p₁₁ p₂₁
    → StatePathEqual p₁₂ p₂₂
    → StatePathEqual
      (state-path-product p₁₁ p₁₂)
      (state-path-product p₂₁ p₂₂)
  state-path-equal-product q₁ q₂
    = record {StatePathEqualProduct q₁ q₂}

-- ### StatePathIdentity

module _
  {X₁ X₂ : Object'}
  {F₁ : Arrow' X₁ X₁}
  {F₂ : Arrow' X₂ X₂}
  {i₁ : Identity F₁}
  {i₂ : Identity F₂}
  {p₁ : StatePath F₁}
  {p₂ : StatePath F₂}
  where

  module StatePathIdentityProduct
    (q₁ : StatePathIdentity i₁ p₁)
    (q₂ : StatePathIdentity i₂ p₂)
    where

    map
      : (x : Object'.Object (object-product X₁ X₂))
      → Arrow'.ArrowEqual' (arrow-product F₁ F₂)
        (StatePath.map (state-path-product p₁ p₂) x)
        (Identity.identity (identity-product i₁ i₂) x)
    map (x₁ , x₂)
      = arrow-equal-product
        (StatePathIdentity.map q₁ x₁)
        (StatePathIdentity.map q₂ x₂)

  state-path-identity-product
    : StatePathIdentity i₁ p₁
    → StatePathIdentity i₂ p₂
    → StatePathIdentity
      (identity-product i₁ i₂)
      (state-path-product p₁ p₂)
  state-path-identity-product q₁ q₂
    = record {StatePathIdentityProduct q₁ q₂}

-- ## Dependent

-- ### DependentStatePath

dependent-state-path-product
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {Y₁' Y₂' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F₁' : DependentArrow X₁' Y₁'}
  → {F₂' : DependentArrow X₂' Y₂'}
  → {p : ChainPath F}
  → DependentStatePath F₁' p
  → DependentStatePath F₂' p
  → DependentStatePath
    (dependent-arrow-product F₁' F₂') p
dependent-state-path-product {n = zero} p₁' p₂'
  = state-path-product p₁' p₂'
dependent-state-path-product {n = suc _} p₁' p₂'
  = record
  { tail
    = λ x p' → dependent-state-path-product
      (DependentStatePath.tail p₁' x p')
      (DependentStatePath.tail p₂' x p')
  }

-- ### DependentStatePathEqual

dependent-state-path-equal-product
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {Y₁' Y₂' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F₁' : DependentArrow X₁' Y₁'}
  → {F₂' : DependentArrow X₂' Y₂'}
  → {p₁ p₂ : ChainPath F}
  → {p₁₁' : DependentStatePath F₁' p₁}
  → {p₂₁' : DependentStatePath F₁' p₂}
  → {p₁₂' : DependentStatePath F₂' p₁}
  → {p₂₂' : DependentStatePath F₂' p₂}
  → DependentStatePathEqual p₁₁' p₂₁'
  → DependentStatePathEqual p₁₂' p₂₂'
  → DependentStatePathEqual
    (dependent-state-path-product p₁₁' p₁₂')
    (dependent-state-path-product p₂₁' p₂₂')
dependent-state-path-equal-product {n = zero} q₁ q₂
  = state-path-equal-product q₁ q₂
dependent-state-path-equal-product {n = suc _} q₁ q₂
  = record
  { tail
    = λ x p₁'' p₂'' → dependent-state-path-equal-product
      (DependentStatePathEqual.tail q₁ x p₁'' p₂'')
      (DependentStatePathEqual.tail q₂ x p₁'' p₂'')
  }

-- ### DependentStatePathIdentity

dependent-state-path-identity-product
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {F : ChainArrow X X}
  → {F₁' : DependentArrow X₁' X₁'}
  → {F₂' : DependentArrow X₂' X₂'}
  → {i₁ : DependentIdentity F₁'}
  → {i₂ : DependentIdentity F₂'}
  → {p : ChainPath F}
  → {p₁' : DependentStatePath F₁' p}
  → {p₂' : DependentStatePath F₂' p}
  → DependentStatePathIdentity i₁ p₁'
  → DependentStatePathIdentity i₂ p₂'
  → DependentStatePathIdentity
    (dependent-identity-product i₁ i₂)
    (dependent-state-path-product p₁' p₂')
dependent-state-path-identity-product {n = zero} q₁ q₂
  = state-path-identity-product q₁ q₂
dependent-state-path-identity-product {n = suc _} q₁ q₂
  = record
  { tail
    = λ p' → dependent-state-path-identity-product
      (DependentStatePathIdentity.tail q₁ p')
      (DependentStatePathIdentity.tail q₂ p')
  }

-- ### DependentStateLift

dependent-state-lift-product
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {F : ChainArrow X X}
  → {F₁' : DependentArrow X₁' X₁'}
  → {F₂' : DependentArrow X₂' X₂'}
  → {i : ChainIdentity F}
  → {i₁' : DependentIdentity F₁'}
  → {i₂' : DependentIdentity F₂'}
  → {l : ChainLift F}
  → DependentStateLift i i₁' l
  → DependentStateLift i i₂' l
  → DependentStateLift i
    (dependent-identity-product i₁' i₂') l
dependent-state-lift-product {n = zero} _ _
  = tt
dependent-state-lift-product {n = suc _} l₁' l₂'
  = record
  { path
    = λ f → dependent-state-path-product
      (DependentStateLift.path l₁' f)
      (DependentStateLift.path l₂' f)
  ; path-equal
    = λ p → dependent-state-path-equal-product
      (DependentStateLift.path-equal l₁' p)
      (DependentStateLift.path-equal l₂' p)
  ; path-identity
    = λ x → dependent-state-path-identity-product
      (DependentStateLift.path-identity l₁' x)
      (DependentStateLift.path-identity l₂' x)
  ; tail
    = λ x → dependent-state-lift-product
      (DependentStateLift.tail l₁' x)
      (DependentStateLift.tail l₂' x)
  }

