module Category.Lift.Collection where

open import Category.Core
  using (Arrow'; ChainArrow; ChainCompose; ChainIdentity; ChainObject;
    DependentArrow; DependentCompose; DependentIdentity; DependentObject;
    Object')
open import Category.Core.Collection
  using (module ArrowCollection; arrow-collection; dependent-arrow-collection;
    object-collection)
open import Category.Core.Relation
  using (DependentDecidable; DependentRelation)
open import Category.Lift
  using (ChainLift; ChainPath; DependentLift; DependentPath; DependentPrelift';
    Path; tt)
open import Category.Lift.List
  using (module PathList)
open import Data.Collection
  using (Collection; collection)
open import Data.Equal
  using (_≡_; refl)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Relation
  using (Decidable; Relation; yes)

-- ## Base

-- ### Path

module _
  {X Y : Object'}
  where

  module PathCollection
    (R : Relation (Object'.Object X))
    (S : Relation (Object'.Object Y))
    (d : Decidable S)
    {F : Arrow' X Y}
    (p : Path F)
    where

    base
      : Object'.Object (object-collection R)
      → Maybe (Object'.Object (object-collection S))
    base (collection xs _)
      with PathList.base p xs
    ... | nothing
      = nothing
    ... | just ys
      = Collection.from-list S d ys

    map
      : (xs : Object'.Object (object-collection R))
      → {ys : Object'.Object (object-collection S)}
      → base xs ≡ just ys
      → Arrow'.Arrow (arrow-collection R S F) xs ys
    map (collection xs _) _
      with PathList.base p xs
      | inspect (PathList.base p) xs
    ... | just ys | _
      with Collection.from-list' S d ys
    map (collection xs _) refl | _ | [ r ] | yes _
      = ArrowCollection.arrow
        (PathList.map p xs r)

  path-collection
    : (R : Relation (Object'.Object X))
    → (S : Relation (Object'.Object Y))
    → Decidable S
    → {F : Arrow' X Y}
    → Path F
    → Path
      (arrow-collection R S F)
  path-collection R S d p
    = record {PathCollection R S d p}

-- ## Dependent

-- ### DependentPath

dependent-path-collection
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → (R : DependentRelation X')
  → {S : DependentRelation Y'}
  → DependentDecidable S
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {p : ChainPath F}
  → DependentPath F' p
  → DependentPath
    (dependent-arrow-collection R S F') p
dependent-path-collection {n = zero} R {S = S} d p'
  = path-collection R S d p'
dependent-path-collection {n = suc _} R d p'
  = record
  { tail
    = λ x {y} p'' → dependent-path-collection
      (DependentRelation.tail R x)
      (DependentDecidable.tail d y)
      (DependentPath.tail p' x p'')
  }

-- ### DependentPrelift'

dependent-prelift-collection
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {R : DependentRelation X'}
  → DependentDecidable R
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {i : ChainIdentity F}
  → {i' : DependentIdentity F'}
  → {j : ChainCompose F F F}
  → {j' : DependentCompose F' F' F'}
  → {l : ChainLift F}
  → DependentLift i i' j j' l
  → DependentPrelift'
    (dependent-arrow-collection R R F') l
dependent-prelift-collection {n = zero} _ _
  = tt
dependent-prelift-collection {n = suc _} {R = R} d l'
  = record
  { path
    = λ {x} {y} f → dependent-path-collection
      (DependentRelation.tail R x)
      (DependentDecidable.tail d y)
      (DependentLift.path l' f)
  ; tail
    = λ x → dependent-prelift-collection
      (DependentDecidable.tail d x)
      (DependentLift.tail l' x)
  }

