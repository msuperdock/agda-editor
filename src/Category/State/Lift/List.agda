module Category.State.Lift.List where

open import Category.Core
  using (Arrow'; ChainArrow; ChainIdentity; ChainObject; DependentArrow;
    DependentIdentity; DependentObject; Identity; Object')
open import Category.Core.List
  using (module ArrowList; arrow-equal-list; arrow-list; dependent-arrow-list;
    dependent-identity-list; identity-list; object-list)
open import Category.Lift
  using (ChainLift; ChainPath)
open import Category.State.Lift
  using (DependentStateLift; DependentStatePath; DependentStatePathEqual;
    DependentStatePathIdentity; StatePath; StatePathEqual; StatePathIdentity;
    tt)
open import Data.Any
  using (any)
open import Data.Equal
  using (_≡_; refl)
open import Data.Fin
  using (Fin)
open import Data.Function
  using (_$_)
open import Data.List
  using (List; _!_)
open import Data.Maybe
  using (Maybe; just)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Vec
  using (Vec)

-- ## Base

-- ### StatePath

module _
  {X Y : Object'}
  {F : Arrow' X Y}
  where

  module StatePathList
    (p : StatePath F)
    where

    base
      : Object'.Object (object-list X)
      → Object'.Object (object-list Y)
    base
      = List.map
        (StatePath.base p)

    map-lookup
      : (xs : Object'.Object (object-list X))
      → (k : Fin (List.length xs))
      → Maybe (l ∈ Fin (List.length (base xs))
        × Arrow'.Arrow F (xs ! k) (base xs ! l))
    map-lookup xs k
      = just (k , Arrow'.arrow F refl p' f)
      where
        f = StatePath.map p (xs ! k)
        p' = List.lookup-map (StatePath.base p) xs k

    map-injective
      : (xs : Object'.Object (object-list X))
      → (k₁ k₂ : Fin (List.length xs))
      → {l : Fin (List.length (base xs))}
      → {f₁ : Arrow'.Arrow F (xs ! k₁) (base xs ! l)}
      → {f₂ : Arrow'.Arrow F (xs ! k₂) (base xs ! l)}
      → map-lookup xs k₁ ≡ just (l , f₁)
      → map-lookup xs k₂ ≡ just (l , f₂)
      → k₁ ≡ k₂
    map-injective _ _ _ refl refl
      = refl

    map
      : (xs : Object'.Object (object-list X))
      → Arrow'.Arrow (arrow-list F) xs (base xs)
    map xs
      = record
      { lookup
        = map-lookup xs
      ; injective
        = map-injective xs
      }

  state-path-list
    : StatePath F
    → StatePath
      (arrow-list F)
  state-path-list p
    = record {StatePathList p}

-- ### StatePathEqual

module _
  {X Y : Object'}
  {F : Arrow' X Y}
  {p₁ p₂ : StatePath F}
  where

  module StatePathEqualList
    (q : StatePathEqual p₁ p₂)
    where

    map
      : (xs : Object'.Object (object-list X))
      → Arrow'.ArrowEqual' (arrow-list F)
        (StatePath.map (state-path-list p₁) xs)
        (StatePath.map (state-path-list p₂) xs)
    map (any xs)
      = arrow-equal-list F refl r
      $ λ k
      → ArrowList.just' k
      $ Arrow'.arrow-trans' F (Arrow'.arrow-refl'' F refl
        (Vec.lookup-map (StatePath.base p₁) xs k))
      $ Arrow'.arrow-trans' F (StatePathEqual.map q
        (Vec.lookup xs k))
      $ Arrow'.arrow-sym' F (Arrow'.arrow-refl'' F refl
        (Vec.lookup-map (StatePath.base p₂) xs k))
      where
        r = Vec.map-equal
          (StatePath.base p₁)
          (StatePath.base p₂)
          (StatePathEqual.base q) xs

  state-path-equal-list
    : StatePathEqual p₁ p₂
    → StatePathEqual
      (state-path-list p₁)
      (state-path-list p₂)
  state-path-equal-list q
    = record {StatePathEqualList q}

-- ### StatePathIdentity

module _
  {X : Object'}
  {F : Arrow' X X}
  {i : Identity F}
  {p : StatePath F}
  where

  module StatePathIdentityList
    (q : StatePathIdentity i p)
    where

    map
      : (xs : Object'.Object (object-list X))
      → Arrow'.ArrowEqual' (arrow-list F)
        (StatePath.map (state-path-list p) xs)
        (Identity.identity (identity-list i) xs)
    map xs@(any xs')
      = arrow-equal-list F refl p'
      $ λ k
      → ArrowList.just' k
      $ Arrow'.arrow-trans' F (Arrow'.arrow-refl'' F refl
        (Vec.lookup-map (StatePath.base p) xs' k))
      $ StatePathIdentity.map q (xs ! k)
      where
        p' = Vec.map-identity
          (StatePath.base p)
          (StatePathIdentity.base q) xs'

  state-path-identity-list
    : StatePathIdentity i p
    → StatePathIdentity
      (identity-list i)
      (state-path-list p)
  state-path-identity-list q
    = record {StatePathIdentityList q}

-- ## Dependent

-- ### DependentStatePath

dependent-state-path-list
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {p : ChainPath F}
  → DependentStatePath F' p
  → DependentStatePath
    (dependent-arrow-list F') p
dependent-state-path-list {n = zero} p'
  = state-path-list p'
dependent-state-path-list {n = suc _} p'
  = record
  { tail
    = λ x p'' → dependent-state-path-list
      (DependentStatePath.tail p' x p'')
  }

-- ### DependentStatePathEqual

dependent-state-path-equal-list
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {p₁ p₂ : ChainPath F}
  → {p₁' : DependentStatePath F' p₁}
  → {p₂' : DependentStatePath F' p₂}
  → DependentStatePathEqual p₁' p₂'
  → DependentStatePathEqual
    (dependent-state-path-list p₁')
    (dependent-state-path-list p₂')
dependent-state-path-equal-list {n = zero} q
  = state-path-equal-list q
dependent-state-path-equal-list {n = suc _} q
  = record
  { tail
    = λ x p₁'' p₂'' → dependent-state-path-equal-list
      (DependentStatePathEqual.tail q x p₁'' p₂'')
  }

-- ### DependentStatePathIdentity

dependent-state-path-identity-list
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {i : DependentIdentity F'}
  → {p : ChainPath F}
  → {p' : DependentStatePath F' p}
  → DependentStatePathIdentity i p'
  → DependentStatePathIdentity
    (dependent-identity-list i)
    (dependent-state-path-list p')
dependent-state-path-identity-list {n = zero} q
  = state-path-identity-list q
dependent-state-path-identity-list {n = suc _} q
  = record
  { tail
    = λ p'' → dependent-state-path-identity-list
      (DependentStatePathIdentity.tail q p'')
  }

-- ### DependentStateLift

dependent-state-lift-list
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {i : ChainIdentity F}
  → {i' : DependentIdentity F'}
  → {l : ChainLift F}
  → DependentStateLift i i' l
  → DependentStateLift i
    (dependent-identity-list i') l
dependent-state-lift-list {n = zero} _
  = tt
dependent-state-lift-list {n = suc _} l'
  = record
  { path
    = λ f → dependent-state-path-list
      (DependentStateLift.path l' f)
  ; path-equal
    = λ p → dependent-state-path-equal-list
      (DependentStateLift.path-equal l' p)
  ; path-identity
    = λ x → dependent-state-path-identity-list
      (DependentStateLift.path-identity l' x)
  ; tail
    = λ x → dependent-state-lift-list
      (DependentStateLift.tail l' x)
  }

