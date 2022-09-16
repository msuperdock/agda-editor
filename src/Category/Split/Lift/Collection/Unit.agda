module Category.Split.Lift.Collection.Unit where

open import Category
  using (ChainCategory; DependentCategory)
open import Category.Core
  using (Arrow'; ChainArrow; ChainObject; DependentObject; Object')
open import Category.Core.Collection
  using (object-collection)
open import Category.Core.Collection.Unit
  using (arrow-collection-unit)
open import Category.Core.List
  using (object-list)
open import Category.Core.List.Unit
  using (arrow-list-unit)
open import Category.Core.Relation
  using (DependentDecidable; DependentRelation)
open import Category.Lift
  using (ChainPath; Path)
open import Category.Lift.Collection.Unit
  using (dependent-path-collection-unit; dependent-prelift-collection-unit;
    path-collection-unit)
open import Category.Lift.List.Unit
  using (module PathListUnit; dependent-path-list-unit; path-list-unit)
open import Category.List.Unit
  using (dependent-category-list-unit)
open import Category.Simple
  using (DependentSimpleCategory)
open import Category.Simple.Lift
  using (DependentSimpleLift; DependentSimplePath; SimplePath)
open import Category.Split.Core
  using (SplitBase; SplitMap)
open import Category.Split.Core.Collection
  using (split-base-collection)
open import Category.Split.Core.Collection.Unit
  using (dependent-split-map-collection-unit; split-map-collection-unit)
open import Category.Split.Lift
  using (DependentSplitPath'; DependentSplitPrelift'; SplitPath'; tt)
open import Data.Collection
  using (Collection; collection)
open import Data.Equal
  using (Equal; _≡_; refl; sym; trans)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Relation
  using (Decidable; Relation; yes)

-- ## Base

-- ### SplitPath'

module _
  {X Y : Object'}
  where

  module SplitPathCollectionUnit
    (R : Relation (Object'.Object X))
    (S : Relation (Object'.Object Y))
    (d : Decidable R)
    (e : Decidable S)
    (p : SimplePath X Y)
    where

    base-nothing
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-collection R)}
      → Path.base (path-list-unit p) xs ≡ nothing
      → SplitBase.base (split-base-collection R d) xs ≡ just xs'
      → Path.base (path-collection-unit R S e p) xs' ≡ nothing
    base-nothing xs _ _
      with Collection.from-list' R d xs
    base-nothing xs _ refl | yes _
      with PathListUnit.base p xs
    ... | nothing
      = refl

    base-just
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-collection R)}
      → Path.base (path-list-unit p) xs ≡ just ys
      → SplitBase.base (split-base-collection R d) xs ≡ just xs'
      → SplitBase.base (split-base-collection S e) ys
        ≡ Path.base (path-collection-unit R S e p) xs'
    base-just xs _ _
      with Collection.from-list' R d xs
    base-just xs _ refl | yes _
      with PathListUnit.base p xs
    base-just _ refl _ | _ | _
      = refl

    map
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-collection R)}
      → {ys' : Object'.Object (object-collection S)}
      → (q : Path.base (path-list-unit p) xs ≡ just ys)
      → (q' : Path.base (path-collection-unit R S e p) xs' ≡ just ys')
      → (r : SplitBase.base (split-base-collection R d) xs ≡ just xs')
      → (s : SplitBase.base (split-base-collection S e) ys ≡ just ys')
      → Arrow'.ArrowEqual (arrow-collection-unit R S)
        (SplitMap.map (split-map-collection-unit R S d e) r s
          (Path.map (path-list-unit p) xs q))
        (Path.map (path-collection-unit R S e p) xs' q')
    map xs {ys = ys} {xs' = collection xs' _} _ _ _ _
      with PathListUnit.base p xs'
      | inspect (PathListUnit.base p) xs'
    ... | just ys' | _
      with Collection.from-list' R d xs
      | Collection.from-list' S e ys
      | Collection.from-list' S e ys'
    map _ r refl refl refl | _ | [ r' ] | yes _ | yes _ | yes _
      with Equal.irrelevant r r'
    ... | refl
      = Arrow'.arrow-refl (arrow-collection-unit R S)
    
    unmap
      : (xs' : Object'.Object (object-collection R))
      → {ys : Object'.Object (object-list Y)}
      → {ys' : Object'.Object (object-collection S)}
      → (q : Path.base (path-list-unit p)
        (SplitBase.unbase (split-base-collection R d) xs')
        ≡ just ys)
      → (q' : Path.base (path-collection-unit R S e p) xs' ≡ just ys')
      → Arrow'.ArrowEqual' (arrow-list-unit X Y)
        (SplitMap.unmap (split-map-collection-unit R S d e)
          (Path.map (path-collection-unit R S e p) xs' q'))
        (Path.map (path-list-unit p)
          (SplitBase.unbase (split-base-collection R d) xs') q)
    unmap (collection xs _) r r'
      with PathListUnit.map p xs r
      | inspect (PathListUnit.map p xs) r
      | PathListUnit.base p xs
      | inspect (PathListUnit.base p) xs
    ... | _ | [ refl ] | just ys | _
      with Collection.from-list' S e ys
    unmap _ r' refl | _ | _ | _ | [ r'' ] | yes _
      with trans (sym r') r''
    ... | refl
      with Equal.irrelevant r' r''
    ... | refl
      = Arrow'.arrow-refl' (arrow-list-unit X Y)

  split-path-collection-unit
    : (R : Relation (Object'.Object X))
    → (S : Relation (Object'.Object Y))
    → (d : Decidable R)
    → (e : Decidable S)
    → (p : SimplePath X Y)
    → SplitPath'
      (path-list-unit p)
      (path-collection-unit R S e p)
      (split-map-collection-unit R S d e)
  split-path-collection-unit R S d e p
    = record {SplitPathCollectionUnit R S d e p}

-- ## Dependent

-- ### DependentSplitPath'

dependent-split-path-collection-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {R : DependentRelation X'}
  → {S : DependentRelation Y'}
  → (d : DependentDecidable R)
  → (e : DependentDecidable S)
  → {F : ChainArrow X Y}
  → {p : ChainPath F}
  → (p' : DependentSimplePath X' Y' p)
  → DependentSplitPath'
    (dependent-path-list-unit p')
    (dependent-path-collection-unit R e p')
    (dependent-split-map-collection-unit d e)
dependent-split-path-collection-unit {n = zero} {R = R} {S = S} d e p'
  = split-path-collection-unit R S d e p'
dependent-split-path-collection-unit {n = suc _} d e p'
  = record
  { tail
    = λ x {y} p'' → dependent-split-path-collection-unit
      (DependentDecidable.tail d x)
      (DependentDecidable.tail e y)
      (DependentSimplePath.tail p' x p'')
  }

-- ### DependentSplitPrelift'

dependent-split-prelift-collection-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C' : DependentSimpleCategory C)
  → {R : DependentRelation (DependentSimpleCategory.object C')}
  → (d : DependentDecidable R)
  → DependentSplitPrelift'
    (DependentCategory.lift
      (dependent-category-list-unit C'))
    (dependent-prelift-collection-unit d
      (DependentSimpleCategory.lift C'))
    (dependent-split-map-collection-unit d d)
dependent-split-prelift-collection-unit {n = zero} _ _
  = tt
dependent-split-prelift-collection-unit {n = suc _} C' d
  = record
  { path
    = λ {x} {y} f → dependent-split-path-collection-unit
      (DependentDecidable.tail d x)
      (DependentDecidable.tail d y)
      (DependentSimpleLift.path
        (DependentSimpleCategory.lift C') f)
  ; tail
    = λ x → dependent-split-prelift-collection-unit
      (DependentSimpleCategory.tail C' x)
      (DependentDecidable.tail d x)
  }

