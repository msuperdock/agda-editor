module Category.Split.Core.Collection where

open import Category.Core
  using (Arrow'; ChainObject; Compose; DependentArrow; DependentCompose;
    DependentIdentity; DependentObject; Identity; Object')
open import Category.Core.Collection
  using (module ArrowCollection; arrow-collection; compose-collection;
    dependent-arrow-collection; dependent-compose-collection;
    dependent-identity-collection; dependent-object-collection;
    identity-collection; object-collection)
open import Category.Core.List
  using (arrow-list; compose-list; dependent-arrow-list; dependent-compose-list;
    dependent-identity-list; dependent-object-list; identity-list; object-list)
open import Category.Core.Relation
  using (DependentDecidable; DependentRelation)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitCompose; DependentSplitIdentity;
    DependentSplitMap; SplitBase; SplitCompose; SplitIdentity; SplitMap)
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

-- ### SplitBase

split-base-collection
  : {X : Object'}
  → (R : Relation (Object'.Object X))
  → Decidable R
  → SplitBase
    (object-list X)
    (object-collection R)
split-base-collection R d
  = record
  { base
    = Collection.from-list R d
  ; unbase
    = Collection.elements
  ; base-unbase
    = Collection.from-list-elements R d
  }

-- ### SplitMap

module _
  {X Y : Object'}
  where

  module SplitMapCollection
    (R : Relation (Object'.Object X))
    (S : Relation (Object'.Object Y))
    (d : Decidable R)
    (e : Decidable S)
    (F : Arrow' X Y)
    where

    map
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-collection R)}
      → {ys' : Object'.Object (object-collection S)}
      → SplitBase.base (split-base-collection R d) xs ≡ just xs'
      → SplitBase.base (split-base-collection S e) ys ≡ just ys'
      → Arrow'.Arrow (arrow-list F) xs ys
      → Arrow'.Arrow (arrow-collection R S F) xs' ys'
    map {xs = xs} {ys = ys} _ _
      with Collection.from-list' R d xs
      | Collection.from-list' S e ys
    map refl refl | yes _ | yes _
      = ArrowCollection.arrow

    map-equal
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-collection R)}
      → {ys' : Object'.Object (object-collection S)}
      → {fs₁ fs₂ : Arrow'.Arrow (arrow-list F) xs ys}
      → (p : SplitBase.base (split-base-collection R d) xs ≡ just xs')
      → (q : SplitBase.base (split-base-collection S e) ys ≡ just ys')
      → Arrow'.ArrowEqual (arrow-list F) fs₁ fs₂
      → Arrow'.ArrowEqual (arrow-collection R S F) (map p q fs₁) (map p q fs₂)
    map-equal {xs = xs} {ys = ys} _ _
      with Collection.from-list' R d xs
      | Collection.from-list' S e ys
    map-equal refl refl | yes _ | yes _
      = ArrowCollection.arrow-equal

    unmap
      : {xs : Object'.Object (object-collection R)}
      → {ys : Object'.Object (object-collection S)}
      → Arrow'.Arrow (arrow-collection R S F) xs ys
      → Arrow'.Arrow (arrow-list F)
        (SplitBase.unbase (split-base-collection R d) xs)
        (SplitBase.unbase (split-base-collection S e) ys)
    unmap
      = ArrowCollection.Arrow.elements

    unmap-equal
      : {xs : Object'.Object (object-collection R)}
      → {ys : Object'.Object (object-collection S)}
      → {fs₁ fs₂ : Arrow'.Arrow (arrow-collection R S F) xs ys}
      → Arrow'.ArrowEqual (arrow-collection R S F) fs₁ fs₂
      → Arrow'.ArrowEqual (arrow-list F) (unmap fs₁) (unmap fs₂)
    unmap-equal
      = ArrowCollection.ArrowEqual.elements

    map-unmap
      : {xs : Object'.Object (object-collection R)}
      → {ys : Object'.Object (object-collection S)}
      → (p : SplitBase.base (split-base-collection R d)
        (SplitBase.unbase (split-base-collection R d) xs)
        ≡ just xs)
      → (q : SplitBase.base (split-base-collection S e)
        (SplitBase.unbase (split-base-collection S e) ys)
        ≡ just ys)
      → (fs : Arrow'.Arrow (arrow-collection R S F) xs ys)
      → Arrow'.ArrowEqual (arrow-collection R S F) (map p q (unmap fs)) fs
    map-unmap {xs = collection xs _} {ys = collection ys _} _ _ _
      with Collection.from-list' R d xs
      | Collection.from-list' S e ys
    map-unmap refl refl _ | yes _ | yes _
      = Arrow'.arrow-refl (arrow-collection R S F)

  split-map-collection
    : (R : Relation (Object'.Object X))
    → (S : Relation (Object'.Object Y))
    → (d : Decidable R)
    → (e : Decidable S)
    → (F : Arrow' X Y)
    → SplitMap
      (arrow-list F)
      (arrow-collection R S F)
      (split-base-collection R d)
      (split-base-collection S e)
  split-map-collection R S d e F
    = record {SplitMapCollection R S d e F}

-- ### SplitIdentity

module _
  {X : Object'}
  where

  module SplitIdentityCollection
    (R : Relation (Object'.Object X))
    (d : Decidable R)
    {F : Arrow' X X}
    (i : Identity F)
    where

    map
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-collection R)}
      → (p : SplitBase.base (split-base-collection R d) xs ≡ just xs')
      → Arrow'.ArrowEqual (arrow-collection R R F)
        (SplitMap.map (split-map-collection R R d d F) p p
          (Identity.identity (identity-list i) xs))
        (Identity.identity (identity-collection R i) xs')
    map xs _
      with Collection.from-list' R d xs
    map _ refl | yes _
      = Arrow'.arrow-refl (arrow-collection R R F)

    unmap
      : (xs : Object'.Object (object-collection R))
      → Arrow'.ArrowEqual (arrow-list F)
        (SplitMap.unmap (split-map-collection R R d d F)
          (Identity.identity (identity-collection R i) xs))
        (Identity.identity (identity-list i)
          (SplitBase.unbase (split-base-collection R d) xs))
    unmap _
      = Arrow'.arrow-refl (arrow-list F)

    normalize-arrow
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-collection R)}
      → SplitBase.base (split-base-collection R d) xs ≡ just xs'
      → Arrow'.Arrow (arrow-list F) xs
        (SplitBase.unbase (split-base-collection R d) xs')
    normalize-arrow xs _
      with Collection.from-list' R d xs
    normalize-arrow xs refl | yes _
      = Identity.identity (identity-list i) xs

    normalize-valid
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-collection R)}
      → (p : SplitBase.base (split-base-collection R d) xs ≡ just xs')
      → (q : SplitBase.base (split-base-collection R d)
        (SplitBase.unbase (split-base-collection R d) xs')
        ≡ just xs')
      → Arrow'.ArrowEqual (arrow-collection R R F)
        (SplitMap.map (split-map-collection R R d d F) p q
          (normalize-arrow xs p))
        (Identity.identity (identity-collection R i) xs')
    normalize-valid xs {xs' = collection xs' _} _ _
      with Collection.from-list' R d xs
      | Collection.from-list' R d xs'
    normalize-valid _ refl refl | yes _ | yes _
      = Arrow'.arrow-refl (arrow-collection R R F)

  split-identity-collection
    : (R : Relation (Object'.Object X))
    → (d : Decidable R)
    → {F : Arrow' X X}
    → (i : Identity F)
    → SplitIdentity
      (identity-list i)
      (identity-collection R i)
      (split-map-collection R R d d F)
  split-identity-collection R d i
    = record {SplitIdentityCollection R d i}

-- ### SplitCompose

module _
  {X Y Z : Object'}
  where

  module SplitComposeCollection
    (R : Relation (Object'.Object X))
    (S : Relation (Object'.Object Y))
    (T : Relation (Object'.Object Z))
    (d : Decidable R)
    (e : Decidable S)
    (f : Decidable T)
    {F : Arrow' Y Z}
    {G : Arrow' X Y}
    {H : Arrow' X Z}
    (j : Compose F G H)
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
      → (fs' : Arrow'.Arrow (arrow-list F) ys zs)
      → (gs' : Arrow'.Arrow (arrow-list G) xs ys)
      → Arrow'.ArrowEqual (arrow-collection R T H)
        (SplitMap.map (split-map-collection R T d f H) p r
          (Compose.compose (compose-list j) fs' gs'))
        (Compose.compose (compose-collection R S T j)
          (SplitMap.map (split-map-collection S T e f F) q r fs')
          (SplitMap.map (split-map-collection R S d e G) p q gs'))
    map {xs = xs} {ys = ys} {zs = zs} _ _ _ _ _
      with Collection.from-list' R d xs
      | Collection.from-list' S e ys
      | Collection.from-list' T f zs
    map refl refl refl _ _ | yes _ | yes _ | yes _
      = Arrow'.arrow-refl (arrow-collection R T H)

    unmap
      : {xs : Object'.Object (object-collection R)}
      → {ys : Object'.Object (object-collection S)}
      → {zs : Object'.Object (object-collection T)}
      → (fs' : Arrow'.Arrow (arrow-collection S T F) ys zs)
      → (gs' : Arrow'.Arrow (arrow-collection R S G) xs ys)
      → Arrow'.ArrowEqual (arrow-list H)
        (SplitMap.unmap (split-map-collection R T d f H)
          (Compose.compose (compose-collection R S T j) fs' gs'))
        (Compose.compose (compose-list j)
          (SplitMap.unmap (split-map-collection S T e f F) fs')
          (SplitMap.unmap (split-map-collection R S d e G) gs'))
    unmap _ _
      = Arrow'.arrow-refl (arrow-list H)

  split-compose-collection
    : (R : Relation (Object'.Object X))
    → (S : Relation (Object'.Object Y))
    → (T : Relation (Object'.Object Z))
    → (d : Decidable R)
    → (e : Decidable S)
    → (f : Decidable T)
    → {F : Arrow' Y Z}
    → {G : Arrow' X Y}
    → {H : Arrow' X Z}
    → (j : Compose F G H)
    → SplitCompose
      (compose-list j)
      (compose-collection R S T j)
      (split-map-collection S T e f F)
      (split-map-collection R S d e G)
      (split-map-collection R T d f H)
  split-compose-collection R S T d e f j
    = record {SplitComposeCollection R S T d e f j}

-- ## Dependent

-- ### DependentSplitBase

dependent-split-base-collection
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {R : DependentRelation X'}
  → DependentDecidable R
  → DependentSplitBase
    (dependent-object-list X')
    (dependent-object-collection R)
dependent-split-base-collection {n = zero} {R = R} d
  = split-base-collection R d
dependent-split-base-collection {n = suc _} d
  = record
  { tail
    = λ x → dependent-split-base-collection
      (DependentDecidable.tail d x)
  }

-- ### DependentSplitMap

dependent-split-map-collection
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {R : DependentRelation X'}
  → {S : DependentRelation Y'}
  → (d : DependentDecidable R)
  → (e : DependentDecidable S)
  → (F : DependentArrow X' Y')
  → DependentSplitMap
    (dependent-arrow-list F)
    (dependent-arrow-collection R S F)
    (dependent-split-base-collection d)
    (dependent-split-base-collection e)
dependent-split-map-collection {n = zero} {R = R} {S = S} d e F
  = split-map-collection R S d e F
dependent-split-map-collection {n = suc _} d e F
  = record
  { tail
    = λ x y → dependent-split-map-collection
      (DependentDecidable.tail d x)
      (DependentDecidable.tail e y)
      (DependentArrow.tail F x y)
  }

-- ### DependentSplitIdentity

dependent-split-identity-collection
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {R : DependentRelation X'}
  → (d : DependentDecidable R)
  → {F : DependentArrow X' X'}
  → (i : DependentIdentity F)
  → DependentSplitIdentity
    (dependent-identity-list i)
    (dependent-identity-collection R i)
    (dependent-split-map-collection d d F)
dependent-split-identity-collection {n = zero} {R = R} d i
  = split-identity-collection R d i
dependent-split-identity-collection {n = suc _} d i
  = record
  { tail
    = λ x → dependent-split-identity-collection
      (DependentDecidable.tail d x)
      (DependentIdentity.tail i x)
  }

-- ### DependentSplitCompose

dependent-split-compose-collection
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
  → {F : DependentArrow Y' Z'}
  → {G : DependentArrow X' Y'}
  → {H : DependentArrow X' Z'}
  → (j : DependentCompose F G H)
  → DependentSplitCompose
    (dependent-compose-list j)
    (dependent-compose-collection R S T j)
    (dependent-split-map-collection e f F)
    (dependent-split-map-collection d e G)
    (dependent-split-map-collection d f H)
dependent-split-compose-collection {n = zero} {R = R} {S = S} {T = T} d e f j
  = split-compose-collection R S T d e f j
dependent-split-compose-collection {n = suc _} d e f j
  = record
  { tail
    = λ x y z → dependent-split-compose-collection
      (DependentDecidable.tail d x)
      (DependentDecidable.tail e y)
      (DependentDecidable.tail f z)
      (DependentCompose.tail j x y z)
  }

