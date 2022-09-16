module Category.Split.Lift.Collection where

open import Category.Core
  using (Arrow'; ChainArrow; ChainCompose; ChainIdentity; ChainObject;
    DependentArrow; DependentCompose; DependentIdentity; DependentObject;
    Object')
open import Category.Core.Collection
  using (arrow-collection; object-collection)
open import Category.Core.List
  using (arrow-list; object-list)
open import Category.Core.Relation
  using (DependentDecidable; DependentRelation)
open import Category.Lift
  using (ChainLift; ChainPath; DependentLift; DependentPath; Path)
open import Category.Lift.Collection
  using (dependent-path-collection; dependent-prelift-collection;
    path-collection)
open import Category.Lift.List
  using (module PathList; dependent-lift-list; dependent-path-list; path-list)
open import Category.Split.Core
  using (SplitBase; SplitMap)
open import Category.Split.Core.Collection
  using (dependent-split-map-collection; split-base-collection;
    split-map-collection)
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

  module SplitPathCollection
    (R : Relation (Object'.Object X))
    (S : Relation (Object'.Object Y))
    (d : Decidable R)
    (e : Decidable S)
    {F : Arrow' X Y}
    (p : Path F)
    where

    base-nothing
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-collection R)}
      → Path.base (path-list p) xs ≡ nothing
      → SplitBase.base (split-base-collection R d) xs ≡ just xs'
      → Path.base (path-collection R S e p) xs' ≡ nothing
    base-nothing xs _ _
      with Collection.from-list' R d xs
    base-nothing xs _ refl | yes _
      with PathList.base p xs
    ... | nothing
      = refl

    base-just
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-collection R)}
      → Path.base (path-list p) xs ≡ just ys
      → SplitBase.base (split-base-collection R d) xs ≡ just xs'
      → SplitBase.base (split-base-collection S e) ys
        ≡ Path.base (path-collection R S e p) xs'
    base-just xs _ _
      with Collection.from-list' R d xs
    base-just xs _ refl | yes _
      with PathList.base p xs
    base-just _ refl _ | _ | _
      = refl

    map
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-collection R)}
      → {ys' : Object'.Object (object-collection S)}
      → (r : Path.base (path-list p) xs ≡ just ys)
      → (r' : Path.base (path-collection R S e p) xs' ≡ just ys')
      → (s : SplitBase.base (split-base-collection R d) xs ≡ just xs')
      → (t : SplitBase.base (split-base-collection S e) ys ≡ just ys')
      → Arrow'.ArrowEqual (arrow-collection R S F)
        (SplitMap.map (split-map-collection R S d e F) s t
          (Path.map (path-list p) xs r))
        (Path.map (path-collection R S e p) xs' r')
    map xs {ys = ys} {xs' = collection xs' _} _ _ _ _
      with PathList.base p xs'
      | inspect (PathList.base p) xs'
    ... | just ys' | _
      with Collection.from-list' R d xs
      | Collection.from-list' S e ys
      | Collection.from-list' S e ys'
    map _ r refl refl refl | _ | [ r' ] | yes _ | yes _ | yes _
      with Equal.irrelevant r r'
    ... | refl
      = Arrow'.arrow-refl (arrow-collection R S F)
    
    unmap
      : (xs' : Object'.Object (object-collection R))
      → {ys : Object'.Object (object-list Y)}
      → {ys' : Object'.Object (object-collection S)}
      → (r : Path.base (path-list p)
        (SplitBase.unbase (split-base-collection R d) xs')
        ≡ just ys)
      → (r' : Path.base (path-collection R S e p) xs' ≡ just ys')
      → Arrow'.ArrowEqual' (arrow-list F)
        (SplitMap.unmap (split-map-collection R S d e F)
          (Path.map (path-collection R S e p) xs' r'))
        (Path.map (path-list p)
          (SplitBase.unbase (split-base-collection R d) xs') r)
    unmap (collection xs _) r r'
      with PathList.map p xs r
      | inspect (PathList.map p xs) r
      | PathList.base p xs
      | inspect (PathList.base p) xs
    ... | _ | [ refl ] | just ys | _
      with Collection.from-list' S e ys
    unmap _ r' refl | _ | _ | _ | [ r'' ] | yes _
      with trans (sym r') r''
    ... | refl
      with Equal.irrelevant r' r''
    ... | refl
      = Arrow'.arrow-refl' (arrow-list F)

  split-path-collection
    : (R : Relation (Object'.Object X))
    → (S : Relation (Object'.Object Y))
    → (d : Decidable R)
    → (e : Decidable S)
    → {F : Arrow' X Y}
    → (p : Path F)
    → SplitPath'
      (path-list p)
      (path-collection R S e p)
      (split-map-collection R S d e F)
  split-path-collection R S d e p
    = record {SplitPathCollection R S d e p}

-- ## Dependent

-- ### DependentSplitPath'

dependent-split-path-collection
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {R : DependentRelation X'}
  → {S : DependentRelation Y'}
  → (d : DependentDecidable R)
  → (e : DependentDecidable S)
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {p : ChainPath F}
  → (p' : DependentPath F' p)
  → DependentSplitPath'
    (dependent-path-list p')
    (dependent-path-collection R e p')
    (dependent-split-map-collection d e F')
dependent-split-path-collection {n = zero} {R = R} {S = S} d e p'
  = split-path-collection R S d e p'
dependent-split-path-collection {n = suc _} d e p'
  = record
  { tail
    = λ x {y} p''' → dependent-split-path-collection
      (DependentDecidable.tail d x)
      (DependentDecidable.tail e y)
      (DependentPath.tail p' x p''')
  }

-- ### DependentSplitPrelift'


dependent-split-prelift-collection
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {R : DependentRelation X'}
  → (d : DependentDecidable R)
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {i : ChainIdentity F}
  → {i' : DependentIdentity F'}
  → {j : ChainCompose F F F}
  → {j' : DependentCompose F' F' F'}
  → {l : ChainLift F}
  → (l' : DependentLift i i' j j' l)
  → DependentSplitPrelift'
    (dependent-lift-list l')
    (dependent-prelift-collection d l')
    (dependent-split-map-collection d d F')
dependent-split-prelift-collection {n = zero} _ _
  = tt
dependent-split-prelift-collection {n = suc _} d l'
  = record
  { path
    = λ {x} {y} f → dependent-split-path-collection
      (DependentDecidable.tail d x)
      (DependentDecidable.tail d y)
      (DependentLift.path l' f)
  ; tail
    = λ x → dependent-split-prelift-collection
      (DependentDecidable.tail d x)
      (DependentLift.tail l' x)
  }

