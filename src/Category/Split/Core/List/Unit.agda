module Category.Split.Core.List.Unit where

open import Category.Core
  using (Arrow'; ChainObject; Compose; DependentObject; Identity; Object')
open import Category.Core.List
  using (module ArrowList; module ComposeList; arrow-list; compose-list;
    dependent-arrow-list; dependent-compose-list; dependent-identity-list;
    dependent-object-list; identity-list; object-list)
open import Category.Core.List.Unit
  using (module ArrowListUnit; module ComposeListUnit; arrow-list-unit;
    compose-list-unit; dependent-arrow-list-unit; dependent-compose-list-unit;
    dependent-identity-list-unit; identity-list-unit)
open import Category.Core.Unit
  using (module ArrowUnit; arrow-unit; compose-unit; dependent-arrow-unit;
    dependent-compose-unit; dependent-identity-unit; identity-unit)
open import Category.Split.Core
  using (DependentSplitCompose; DependentSplitIdentity; DependentSplitMap;
    SplitBase; SplitCompose; SplitIdentity; SplitMap)
open import Category.Split.Core.Identity
  using (dependent-split-base-identity; split-base-identity)
open import Data.Equal
  using (_≡_; refl)
open import Data.Fin
  using (Fin)
open import Data.Inspect
  using ([_]; inspect)
open import Data.List
  using (List; _!_)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ; _,_)

-- ## Base

-- ### SplitMap

module SplitMapListUnit
  (X Y : Object')
  where

  map-lookup
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → Arrow'.Arrow (arrow-list (arrow-unit X Y)) xs ys
    → Fin (List.length xs)
    → Maybe (Fin (List.length ys))
  map-lookup fs k
    with ArrowList.Arrow.lookup fs k
  ... | nothing
    = nothing
  ... | just (l , _)
    = just l

  map-injective
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → (fs : Arrow'.Arrow (arrow-list (arrow-unit X Y)) xs ys)
    → (k₁ k₂ : Fin (List.length xs))
    → {l : Fin (List.length ys)}
    → map-lookup fs k₁ ≡ just l
    → map-lookup fs k₂ ≡ just l
    → k₁ ≡ k₂
  map-injective fs k₁ k₂ _ _
    with ArrowList.Arrow.lookup fs k₁
    | inspect (ArrowList.Arrow.lookup fs) k₁
    | ArrowList.Arrow.lookup fs k₂
    | inspect (ArrowList.Arrow.lookup fs) k₂
  map-injective fs k₁ k₂ refl refl
    | just _ | [ p₁ ] | just _ | [ p₂ ]
    = ArrowList.Arrow.injective fs k₁ k₂ p₁ p₂

  map
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {xs' : Object'.Object (object-list X)}
    → {ys' : Object'.Object (object-list Y)}
    → SplitBase.base (split-base-identity (object-list X)) xs ≡ just xs'
    → SplitBase.base (split-base-identity (object-list Y)) ys ≡ just ys'
    → Arrow'.Arrow (arrow-list (arrow-unit X Y)) xs ys
    → Arrow'.Arrow (arrow-list-unit X Y) xs' ys'
  map refl refl fs
    = record
    { lookup
      = map-lookup fs
    ; injective
      = map-injective fs
    }

  map-equal-lookup
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {fs₁ fs₂ : Arrow'.Arrow (arrow-list (arrow-unit X Y)) xs ys}
    → Arrow'.ArrowEqual (arrow-list (arrow-unit X Y)) fs₁ fs₂
    → (k : Fin (List.length xs))
    → map-lookup fs₁ k ≡ map-lookup fs₂ k
  map-equal-lookup {fs₁ = fs₁} {fs₂ = fs₂} rs k
    with ArrowList.Arrow.lookup fs₁ k
    | ArrowList.Arrow.lookup fs₂ k
    | ArrowList.ArrowEqual.lookup rs k
  ... | _ | _ | ArrowList.nothing
    = refl
  ... | _ | _ | ArrowList.just _ _
    = refl

  map-equal
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {xs' : Object'.Object (object-list X)}
    → {ys' : Object'.Object (object-list Y)}
    → {fs₁ fs₂ : Arrow'.Arrow (arrow-list (arrow-unit X Y)) xs ys}
    → (p : SplitBase.base (split-base-identity (object-list X)) xs ≡ just xs')
    → (q : SplitBase.base (split-base-identity (object-list Y)) ys ≡ just ys')
    → Arrow'.ArrowEqual (arrow-list (arrow-unit X Y)) fs₁ fs₂
    → Arrow'.ArrowEqual (arrow-list-unit X Y) (map p q fs₁) (map p q fs₂)
  map-equal refl refl rs
    = record
    { lookup
      = map-equal-lookup rs
    }

  unmap-lookup
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → Arrow'.Arrow (arrow-list-unit X Y) xs ys
    → (k : Fin (List.length xs))
    → Maybe (l ∈ Fin (List.length ys)
      × Arrow'.Arrow (arrow-unit X Y) (xs ! k) (ys ! l))
  unmap-lookup fs k
    with ArrowListUnit.Arrow.lookup fs k
  ... | nothing
    = nothing
  ... | just l
    = just (l , ArrowUnit.tt)

  unmap-injective
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → (fs' : Arrow'.Arrow (arrow-list-unit X Y) xs ys)
    → (k₁ k₂ : Fin (List.length xs))
    → {l : Fin (List.length ys)}
    → {f₁ : Arrow'.Arrow (arrow-unit X Y) (xs ! k₁) (ys ! l)}
    → {f₂ : Arrow'.Arrow (arrow-unit X Y) (xs ! k₂) (ys ! l)}
    → unmap-lookup fs' k₁ ≡ just (l , f₁)
    → unmap-lookup fs' k₂ ≡ just (l , f₂)
    → k₁ ≡ k₂
  unmap-injective fs' k₁ k₂ _ _
    with ArrowListUnit.Arrow.lookup fs' k₁
    | inspect (ArrowListUnit.Arrow.lookup fs') k₁
    | ArrowListUnit.Arrow.lookup fs' k₂
    | inspect (ArrowListUnit.Arrow.lookup fs') k₂
  unmap-injective fs' k₁ k₂ refl refl
    | just _ | [ p₁ ] | just _ | [ p₂ ]
    = ArrowListUnit.Arrow.injective fs' k₁ k₂ p₁ p₂

  unmap
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → Arrow'.Arrow (arrow-list-unit X Y) xs ys
    → Arrow'.Arrow (arrow-list (arrow-unit X Y))
      (SplitBase.unbase (split-base-identity (object-list X)) xs)
      (SplitBase.unbase (split-base-identity (object-list Y)) ys)
  unmap fs
    = record
    { lookup
      = unmap-lookup fs
    ; injective
      = unmap-injective fs
    }

  unmap-equal-lookup
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {fs₁ fs₂ : Arrow'.Arrow (arrow-list-unit X Y) xs ys}
    → Arrow'.ArrowEqual (arrow-list-unit X Y) fs₁ fs₂
    → (k : Fin (List.length xs))
    → ArrowList.LookupEqual (arrow-unit X Y) xs ys k
      (unmap-lookup fs₁ k)
      (unmap-lookup fs₂ k)
  unmap-equal-lookup {fs₁ = fs₁} {fs₂ = fs₂} ps k
    with ArrowListUnit.Arrow.lookup fs₁ k
    | ArrowListUnit.Arrow.lookup fs₂ k
    | ArrowListUnit.ArrowEqual.lookup ps k
  ... | nothing | _ | refl
    = ArrowList.nothing
  ... | just l | _ | refl
    = ArrowList.just l ArrowUnit.tt

  unmap-equal
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {fs₁ fs₂ : Arrow'.Arrow (arrow-list-unit X Y) xs ys}
    → Arrow'.ArrowEqual (arrow-list-unit X Y) fs₁ fs₂
    → Arrow'.ArrowEqual (arrow-list (arrow-unit X Y)) (unmap fs₁) (unmap fs₂)
  unmap-equal ps
    = record
    { lookup
      = unmap-equal-lookup ps
    }

  map-unmap-lookup
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → (fs : Arrow'.Arrow (arrow-list-unit X Y) xs ys)
    → (k : Fin (List.length xs))
    → map-lookup (unmap fs) k ≡ ArrowListUnit.Arrow.lookup fs k
  map-unmap-lookup fs k
    with ArrowListUnit.Arrow.lookup fs k
  ... | nothing
    = refl
  ... | just _
    = refl

  map-unmap
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → (p : SplitBase.base (split-base-identity (object-list X))
      (SplitBase.unbase (split-base-identity (object-list X)) xs)
      ≡ just xs)
    → (q : SplitBase.base (split-base-identity (object-list Y))
      (SplitBase.unbase (split-base-identity (object-list Y)) ys)
      ≡ just ys)
    → (fs : Arrow'.Arrow (arrow-list-unit X Y) xs ys)
    → Arrow'.ArrowEqual (arrow-list-unit X Y) (map p q (unmap fs)) fs
  map-unmap refl refl fs
    = record
    { lookup
      = map-unmap-lookup fs
    }

split-map-list-unit
  : (X Y : Object')
  → SplitMap
    (arrow-list
      (arrow-unit X Y))
    (arrow-list-unit X Y)
    (split-base-identity
      (object-list X))
    (split-base-identity
      (object-list Y))
split-map-list-unit X Y
  = record {SplitMapListUnit X Y}

-- ### SplitIdentity

module SplitIdentityListUnit
  (X : Object')
  where

  map
    : (xs : Object'.Object (object-list X))
    → {xs' : Object'.Object (object-list X)}
    → (p : SplitBase.base (split-base-identity (object-list X)) xs ≡ just xs')
    → Arrow'.ArrowEqual (arrow-list-unit X X)
      (SplitMap.map (split-map-list-unit X X) p p
        (Identity.identity (identity-list (identity-unit X)) xs))
      (Identity.identity (identity-list-unit X) xs')
  map _ refl
    = record
    { lookup
      = λ _ → refl
    }

  unmap
    : (xs : Object'.Object (object-list X))
    → Arrow'.ArrowEqual (arrow-list (arrow-unit X X))
      (SplitMap.unmap (split-map-list-unit X X)
        (Identity.identity (identity-list-unit X) xs))
      (Identity.identity (identity-list (identity-unit X))
        (SplitBase.unbase (split-base-identity (object-list X)) xs))
  unmap _
    = record
    { lookup
      = λ k → ArrowList.just k ArrowUnit.tt
    }

  normalize-arrow
    : (xs : Object'.Object (object-list X))
    → {xs' : Object'.Object (object-list X)}
    → SplitBase.base (split-base-identity (object-list X)) xs ≡ just xs'
    → Arrow'.Arrow (arrow-list (arrow-unit X X)) xs
      (SplitBase.unbase (split-base-identity (object-list X)) xs')
  normalize-arrow xs refl
    = Identity.identity (identity-list (identity-unit X)) xs

  normalize-valid
    : (xs : Object'.Object (object-list X))
    → {xs' : Object'.Object (object-list X)}
    → (p : SplitBase.base (split-base-identity (object-list X)) xs ≡ just xs')
    → (q : SplitBase.base (split-base-identity (object-list X))
      (SplitBase.unbase (split-base-identity (object-list X)) xs')
      ≡ just xs')
    → Arrow'.ArrowEqual (arrow-list-unit X X)
      (SplitMap.map (split-map-list-unit X X) p q (normalize-arrow xs p))
      (Identity.identity (identity-list-unit X) xs')
  normalize-valid xs refl refl
    = map xs refl

split-identity-list-unit
  : (X : Object')
  → SplitIdentity
    (identity-list
      (identity-unit X))
    (identity-list-unit X)
    (split-map-list-unit X X)
split-identity-list-unit X
  = record {SplitIdentityListUnit X}

-- ### SplitCompose

module SplitComposeListUnit
  (X Y Z : Object')
  where

  map-lookup
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {zs : Object'.Object (object-list Z)}
    → (fs : Arrow'.Arrow (arrow-list (arrow-unit Y Z)) ys zs)
    → (gs : Arrow'.Arrow (arrow-list (arrow-unit X Y)) xs ys)
    → (k : Fin (List.length xs))
    → SplitMapListUnit.map-lookup X Z
      (Compose.compose (compose-list (compose-unit X Y Z)) fs gs) k
    ≡ ComposeListUnit.compose-lookup X Y Z
      (SplitMap.map (split-map-list-unit Y Z) refl refl fs)
      (SplitMap.map (split-map-list-unit X Y) refl refl gs) k
  map-lookup fs gs k
    with ArrowList.Arrow.lookup gs k
  ... | nothing
    = refl
  ... | just (l , _)
    with ArrowList.Arrow.lookup fs l
  ... | nothing
    = refl
  ... | just _
    = refl

  map
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {zs : Object'.Object (object-list Z)}
    → {xs' : Object'.Object (object-list X)}
    → {ys' : Object'.Object (object-list Y)}
    → {zs' : Object'.Object (object-list Z)}
    → (p : SplitBase.base (split-base-identity (object-list X)) xs ≡ just xs')
    → (q : SplitBase.base (split-base-identity (object-list Y)) ys ≡ just ys')
    → (r : SplitBase.base (split-base-identity (object-list Z)) zs ≡ just zs')
    → (fs : Arrow'.Arrow (arrow-list (arrow-unit Y Z)) ys zs)
    → (gs : Arrow'.Arrow (arrow-list (arrow-unit X Y)) xs ys)
    → Arrow'.ArrowEqual (arrow-list-unit X Z)
      (SplitMap.map (split-map-list-unit X Z) p r
        (Compose.compose (compose-list (compose-unit X Y Z)) fs gs))
      (Compose.compose (compose-list-unit X Y Z)
        (SplitMap.map (split-map-list-unit Y Z) q r fs)
        (SplitMap.map (split-map-list-unit X Y) p q gs))
  map refl refl refl fs gs
    = record
    { lookup
      = map-lookup fs gs
    }

  unmap-lookup
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {zs : Object'.Object (object-list Z)}
    → (fs : Arrow'.Arrow (arrow-list-unit Y Z) ys zs)
    → (gs : Arrow'.Arrow (arrow-list-unit X Y) xs ys)
    → (k : Fin (List.length xs))
    → ArrowList.LookupEqual (arrow-unit X Z) xs zs k
      (SplitMapListUnit.unmap-lookup X Z
        (Compose.compose (compose-list-unit X Y Z) fs gs) k)
      (ComposeList.compose-lookup (compose-unit X Y Z)
        (SplitMap.unmap (split-map-list-unit Y Z) fs)
        (SplitMap.unmap (split-map-list-unit X Y) gs) k)
  unmap-lookup fs gs k
    with ArrowListUnit.Arrow.lookup gs k
  ... | nothing
    = ArrowList.nothing
  ... | just l
    with ArrowListUnit.Arrow.lookup fs l
  ... | nothing
    = ArrowList.nothing
  ... | just m
    = ArrowList.just m ArrowUnit.tt

  unmap
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {zs : Object'.Object (object-list Z)}
    → (fs : Arrow'.Arrow (arrow-list-unit Y Z) ys zs)
    → (gs : Arrow'.Arrow (arrow-list-unit X Y) xs ys)
    → Arrow'.ArrowEqual (arrow-list (arrow-unit X Z))
      (SplitMap.unmap (split-map-list-unit X Z)
        (Compose.compose (compose-list-unit X Y Z) fs gs))
      (Compose.compose (compose-list (compose-unit X Y Z))
        (SplitMap.unmap (split-map-list-unit Y Z) fs)
        (SplitMap.unmap (split-map-list-unit X Y) gs))
  unmap fs gs
    = record
    { lookup
      = unmap-lookup fs gs
    }

split-compose-list-unit
  : (X Y Z : Object')
  → SplitCompose
    (compose-list
      (compose-unit X Y Z))
    (compose-list-unit X Y Z)
    (split-map-list-unit Y Z)
    (split-map-list-unit X Y)
    (split-map-list-unit X Z)
split-compose-list-unit X Y Z
  = record {SplitComposeListUnit X Y Z}

-- ## Dependent

-- ### DependentSplitMap

dependent-split-map-list-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → (X' : DependentObject X)
  → (Y' : DependentObject Y)
  → DependentSplitMap
    (dependent-arrow-list
      (dependent-arrow-unit X' Y'))
    (dependent-arrow-list-unit X' Y')
    (dependent-split-base-identity
      (dependent-object-list X'))
    (dependent-split-base-identity
      (dependent-object-list Y'))
dependent-split-map-list-unit {n = zero} X' Y'
  = split-map-list-unit X' Y'
dependent-split-map-list-unit {n = suc _} X' Y'
  = record
  { tail
    = λ x y → dependent-split-map-list-unit
      (DependentObject.tail X' x)
      (DependentObject.tail Y' y)
  }

-- ### DependentSplitIdentity

dependent-split-identity-list-unit
  : {n : ℕ}
  → {X : ChainObject n}
  → (X' : DependentObject X)
  → DependentSplitIdentity
    (dependent-identity-list
      (dependent-identity-unit X'))
    (dependent-identity-list-unit X')
    (dependent-split-map-list-unit X' X')
dependent-split-identity-list-unit {n = zero} X'
  = split-identity-list-unit X'
dependent-split-identity-list-unit {n = suc _} X'
  = record
  { tail
    = λ x → dependent-split-identity-list-unit
      (DependentObject.tail X' x)
  }

-- ### DependentSplitCompose

dependent-split-compose-list-unit
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → (X' : DependentObject X)
  → (Y' : DependentObject Y)
  → (Z' : DependentObject Z)
  → DependentSplitCompose
    (dependent-compose-list
      (dependent-compose-unit X' Y' Z'))
    (dependent-compose-list-unit X' Y' Z')
    (dependent-split-map-list-unit Y' Z')
    (dependent-split-map-list-unit X' Y')
    (dependent-split-map-list-unit X' Z')
dependent-split-compose-list-unit {n = zero} X' Y' Z'
  = split-compose-list-unit X' Y' Z'
dependent-split-compose-list-unit {n = suc _} X' Y' Z'
  = record
  { tail
    = λ x y z → dependent-split-compose-list-unit
      (DependentObject.tail X' x)
      (DependentObject.tail Y' y)
      (DependentObject.tail Z' z)
  }

