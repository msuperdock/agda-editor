module Category.Split.Core.Collection.Unit where

open import Category.Core
  using (Arrow'; ChainObject; Compose; DependentObject; Identity; Object')
open import Category.Core.Collection
  using (object-collection)
open import Category.Core.Collection.Unit
  using (module ArrowCollectionUnit; arrow-collection-unit;
    compose-collection-unit; dependent-arrow-collection-unit;
    dependent-compose-collection-unit; dependent-identity-collection-unit;
    identity-collection-unit)
open import Category.Core.Relation
  using (DependentDecidable; DependentRelation)
open import Category.Core.List
  using (object-list)
open import Category.Core.List.Unit
  using (arrow-list-unit; compose-list-unit; dependent-arrow-list-unit;
    dependent-compose-list-unit; dependent-identity-list-unit;
    identity-list-unit)
open import Category.Split.Core
  using (DependentSplitCompose; DependentSplitIdentity; DependentSplitMap;
    SplitBase; SplitCompose; SplitIdentity; SplitMap)
open import Category.Split.Core.Collection
  using (dependent-split-base-collection; split-base-collection)
open import Data.Collection
  using (Collection; collection)
open import Data.Equal
  using (_≡_; refl)
open import Data.Maybe
  using (just)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Relation
  using (Decidable; Relation; yes)

-- ## Base

-- ### SplitMap

module _
  {X Y : Object'}
  where

  module SplitMapCollectionUnit
    (R : Relation (Object'.Object X))
    (S : Relation (Object'.Object Y))
    (d : Decidable R)
    (e : Decidable S)
    where

    map
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-collection R)}
      → {ys' : Object'.Object (object-collection S)}
      → SplitBase.base (split-base-collection R d) xs ≡ just xs'
      → SplitBase.base (split-base-collection S e) ys ≡ just ys'
      → Arrow'.Arrow (arrow-list-unit X Y) xs ys
      → Arrow'.Arrow (arrow-collection-unit R S) xs' ys'
    map {xs = xs} {ys = ys} _ _
      with Collection.from-list' R d xs
      | Collection.from-list' S e ys
    map refl refl | yes _ | yes _
      = ArrowCollectionUnit.arrow

    map-equal
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-collection R)}
      → {ys' : Object'.Object (object-collection S)}
      → {fs₁ fs₂ : Arrow'.Arrow (arrow-list-unit X Y) xs ys}
      → (p : SplitBase.base (split-base-collection R d) xs ≡ just xs')
      → (q : SplitBase.base (split-base-collection S e) ys ≡ just ys')
      → Arrow'.ArrowEqual (arrow-list-unit X Y) fs₁ fs₂
      → Arrow'.ArrowEqual (arrow-collection-unit R S)
        (map p q fs₁)
        (map p q fs₂)
    map-equal {xs = xs} {ys = ys} _ _
      with Collection.from-list' R d xs
      | Collection.from-list' S e ys
    map-equal refl refl | yes _ | yes _
      = ArrowCollectionUnit.arrow-equal

    unmap
      : {xs : Object'.Object (object-collection R)}
      → {ys : Object'.Object (object-collection S)}
      → Arrow'.Arrow (arrow-collection-unit R S) xs ys
      → Arrow'.Arrow (arrow-list-unit X Y)
        (SplitBase.unbase (split-base-collection R d) xs)
        (SplitBase.unbase (split-base-collection S e) ys)
    unmap
      = ArrowCollectionUnit.Arrow.elements

    unmap-equal
      : {xs : Object'.Object (object-collection R)}
      → {ys : Object'.Object (object-collection S)}
      → {fs₁ fs₂ : Arrow'.Arrow (arrow-collection-unit R S) xs ys}
      → Arrow'.ArrowEqual (arrow-collection-unit R S) fs₁ fs₂
      → Arrow'.ArrowEqual (arrow-list-unit X Y) (unmap fs₁) (unmap fs₂)
    unmap-equal
      = ArrowCollectionUnit.ArrowEqual.elements

    map-unmap
      : {xs : Object'.Object (object-collection R)}
      → {ys : Object'.Object (object-collection S)}
      → (p : SplitBase.base (split-base-collection R d)
        (SplitBase.unbase (split-base-collection R d) xs)
        ≡ just xs)
      → (q : SplitBase.base (split-base-collection S e)
        (SplitBase.unbase (split-base-collection S e) ys)
        ≡ just ys)
      → (fs : Arrow'.Arrow (arrow-collection-unit R S) xs ys)
      → Arrow'.ArrowEqual (arrow-collection-unit R S) (map p q (unmap fs)) fs
    map-unmap {xs = collection xs _} {ys = collection ys _} _ _ _
      with Collection.from-list' R d xs
      | Collection.from-list' S e ys
    map-unmap refl refl _ | yes _ | yes _
      = Arrow'.arrow-refl (arrow-collection-unit R S)

  split-map-collection-unit
    : (R : Relation (Object'.Object X))
    → (S : Relation (Object'.Object Y))
    → (d : Decidable R)
    → (e : Decidable S)
    → SplitMap
      (arrow-list-unit X Y)
      (arrow-collection-unit R S)
      (split-base-collection R d)
      (split-base-collection S e)
  split-map-collection-unit R S d e
    = record {SplitMapCollectionUnit R S d e}

-- ### SplitIdentity

module _
  {X : Object'}
  where

  module SplitIdentityCollectionUnit
    (R : Relation (Object'.Object X))
    (d : Decidable R)
    where

    map
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-collection R)}
      → (p : SplitBase.base (split-base-collection R d) xs ≡ just xs')
      → Arrow'.ArrowEqual (arrow-collection-unit R R)
        (SplitMap.map (split-map-collection-unit R R d d) p p
          (Identity.identity (identity-list-unit X) xs))
        (Identity.identity (identity-collection-unit R) xs')
    map xs _
      with Collection.from-list' R d xs
    map _ refl | yes _
      = Arrow'.arrow-refl (arrow-collection-unit R R)

    unmap
      : (xs : Object'.Object (object-collection R))
      → Arrow'.ArrowEqual (arrow-list-unit X X)
        (SplitMap.unmap (split-map-collection-unit R R d d)
          (Identity.identity (identity-collection-unit R) xs))
        (Identity.identity (identity-list-unit X)
          (SplitBase.unbase (split-base-collection R d) xs))
    unmap _
      = Arrow'.arrow-refl (arrow-list-unit X X)

    normalize-arrow
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-collection R)}
      → SplitBase.base (split-base-collection R d) xs ≡ just xs'
      → Arrow'.Arrow (arrow-list-unit X X) xs
        (SplitBase.unbase (split-base-collection R d) xs')
    normalize-arrow xs _
      with Collection.from-list' R d xs
    normalize-arrow xs refl | yes _
      = Identity.identity (identity-list-unit X) xs

    normalize-valid
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-collection R)}
      → (p : SplitBase.base (split-base-collection R d) xs ≡ just xs')
      → (q : SplitBase.base (split-base-collection R d)
        (SplitBase.unbase (split-base-collection R d) xs')
        ≡ just xs')
      → Arrow'.ArrowEqual (arrow-collection-unit R R)
        (SplitMap.map (split-map-collection-unit R R d d) p q
          (normalize-arrow xs p))
        (Identity.identity (identity-collection-unit R) xs')
    normalize-valid xs {xs' = collection xs' _} _ _
      with Collection.from-list' R d xs
      | Collection.from-list' R d xs'
    normalize-valid _ refl refl | yes _ | yes _
      = Arrow'.arrow-refl (arrow-collection-unit R R)

  split-identity-collection-unit
    : (R : Relation (Object'.Object X))
    → (d : Decidable R)
    → SplitIdentity
      (identity-list-unit X)
      (identity-collection-unit R)
      (split-map-collection-unit R R d d)
  split-identity-collection-unit R d
    = record {SplitIdentityCollectionUnit R d}

-- ### SplitCompose

module _
  {X Y Z : Object'}
  where

  module SplitComposeCollectionUnit
    (R : Relation (Object'.Object X))
    (S : Relation (Object'.Object Y))
    (T : Relation (Object'.Object Z))
    (d : Decidable R)
    (e : Decidable S)
    (f : Decidable T)
    where

    map
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {zs : Object'.Object (object-list Z)}
      → {xs' : Object'.Object (object-collection R)}
      → {ys' : Object'.Object (object-collection S)}
      → {zs' : Object'.Object (object-collection T)}
      → (p : SplitBase.base (split-base-collection R d) xs ≡ just xs')
      → (q : SplitBase.base (split-base-collection S e) ys ≡ just ys')
      → (r : SplitBase.base (split-base-collection T f) zs ≡ just zs')
      → (fs' : Arrow'.Arrow (arrow-list-unit Y Z) ys zs)
      → (gs' : Arrow'.Arrow (arrow-list-unit X Y) xs ys)
      → Arrow'.ArrowEqual (arrow-collection-unit R T)
        (SplitMap.map (split-map-collection-unit R T d f) p r
          (Compose.compose (compose-list-unit X Y Z) fs' gs'))
        (Compose.compose (compose-collection-unit R S T)
          (SplitMap.map (split-map-collection-unit S T e f) q r fs')
          (SplitMap.map (split-map-collection-unit R S d e) p q gs'))
    map {xs = xs} {ys = ys} {zs = zs} _ _ _ _ _
      with Collection.from-list' R d xs
      | Collection.from-list' S e ys
      | Collection.from-list' T f zs
    map refl refl refl _ _ | yes _ | yes _ | yes _
      = Arrow'.arrow-refl (arrow-collection-unit R T)

    unmap
      : {xs : Object'.Object (object-collection R)}
      → {ys : Object'.Object (object-collection S)}
      → {zs : Object'.Object (object-collection T)}
      → (fs' : Arrow'.Arrow (arrow-collection-unit S T) ys zs)
      → (gs' : Arrow'.Arrow (arrow-collection-unit R S) xs ys)
      → Arrow'.ArrowEqual (arrow-list-unit X Z)
        (SplitMap.unmap (split-map-collection-unit R T d f)
          (Compose.compose (compose-collection-unit R S T) fs' gs'))
        (Compose.compose (compose-list-unit X Y Z)
          (SplitMap.unmap (split-map-collection-unit S T e f) fs')
          (SplitMap.unmap (split-map-collection-unit R S d e) gs'))
    unmap _ _
      = Arrow'.arrow-refl (arrow-list-unit X Z)

  split-compose-collection-unit
    : (R : Relation (Object'.Object X))
    → (S : Relation (Object'.Object Y))
    → (T : Relation (Object'.Object Z))
    → (d : Decidable R)
    → (e : Decidable S)
    → (f : Decidable T)
    → SplitCompose
      (compose-list-unit X Y Z)
      (compose-collection-unit R S T)
      (split-map-collection-unit S T e f)
      (split-map-collection-unit R S d e)
      (split-map-collection-unit R T d f)
  split-compose-collection-unit R S T d e f
    = record {SplitComposeCollectionUnit R S T d e f}

-- ## Dependent

-- ### DependentSplitMap

dependent-split-map-collection-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {R : DependentRelation X'}
  → {S : DependentRelation Y'}
  → (d : DependentDecidable R)
  → (e : DependentDecidable S)
  → DependentSplitMap
    (dependent-arrow-list-unit X' Y')
    (dependent-arrow-collection-unit R S)
    (dependent-split-base-collection d)
    (dependent-split-base-collection e)
dependent-split-map-collection-unit {n = zero} {R = R} {S = S} d e
  = split-map-collection-unit R S d e
dependent-split-map-collection-unit {n = suc _} d e
  = record
  { tail
    = λ x y → dependent-split-map-collection-unit
      (DependentDecidable.tail d x)
      (DependentDecidable.tail e y)
  }

-- ### DependentSplitIdentity

dependent-split-identity-collection-unit
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {R : DependentRelation X'}
  → (d : DependentDecidable R)
  → DependentSplitIdentity
    (dependent-identity-list-unit X')
    (dependent-identity-collection-unit R)
    (dependent-split-map-collection-unit d d)
dependent-split-identity-collection-unit {n = zero} {R = R} d
  = split-identity-collection-unit R d
dependent-split-identity-collection-unit {n = suc _} d
  = record
  { tail
    = λ x → dependent-split-identity-collection-unit
      (DependentDecidable.tail d x)
  }

-- ### DependentSplitCompose

dependent-split-compose-collection-unit
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {Z' : DependentObject Z}
  → {R : DependentRelation X'}
  → {S : DependentRelation Y'}
  → {T : DependentRelation Z'}
  → (d : DependentDecidable R)
  → (e : DependentDecidable S)
  → (f : DependentDecidable T)
  → DependentSplitCompose
    (dependent-compose-list-unit X' Y' Z')
    (dependent-compose-collection-unit R S T)
    (dependent-split-map-collection-unit e f)
    (dependent-split-map-collection-unit d e)
    (dependent-split-map-collection-unit d f)
dependent-split-compose-collection-unit {n = zero} {R = R} {S = S} {T = T} d e f
  = split-compose-collection-unit R S T d e f
dependent-split-compose-collection-unit {n = suc _} d e f
  = record
  { tail
    = λ x y z → dependent-split-compose-collection-unit
      (DependentDecidable.tail d x)
      (DependentDecidable.tail e y)
      (DependentDecidable.tail f z)
  }

