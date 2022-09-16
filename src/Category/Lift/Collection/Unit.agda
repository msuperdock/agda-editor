module Category.Lift.Collection.Unit where

open import Category.Core
  using (Arrow'; ChainArrow; ChainCompose; ChainIdentity; ChainObject;
    DependentObject; Object')
open import Category.Core.Collection
  using (object-collection)
open import Category.Core.Collection.Unit
  using (module ArrowCollectionUnit; arrow-collection-unit;
    dependent-arrow-collection-unit)
open import Category.Core.Relation
  using (DependentDecidable; DependentRelation)
open import Category.Lift
  using (ChainLift; ChainPath; DependentPath; DependentPrelift'; Path; tt)
open import Category.Lift.List.Unit
  using (module PathListUnit)
open import Category.Simple.Lift
  using (DependentSimpleLift; DependentSimplePath; SimplePath)
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

  module PathCollectionUnit
    (R : Relation (Object'.Object X))
    (S : Relation (Object'.Object Y))
    (d : Decidable S)
    (p : SimplePath X Y)
    where

    base
      : Object'.Object (object-collection R)
      → Maybe (Object'.Object (object-collection S))
    base (collection xs _)
      with PathListUnit.base p xs
    ... | nothing
      = nothing
    ... | just ys
      = Collection.from-list S d ys

    map
      : (xs : Object'.Object (object-collection R))
      → {ys : Object'.Object (object-collection S)}
      → base xs ≡ just ys
      → Arrow'.Arrow (arrow-collection-unit R S) xs ys
    map (collection xs _) _
      with PathListUnit.base p xs
      | inspect (PathListUnit.base p) xs
    ... | just ys | [ r ]
      with Collection.from-list' S d ys
    map (collection xs _) refl | _ | [ r ] | yes _
      = ArrowCollectionUnit.arrow
        (PathListUnit.map p xs r)

  path-collection-unit
    : (R : Relation (Object'.Object X))
    → (S : Relation (Object'.Object Y))
    → Decidable S
    → SimplePath X Y
    → Path
      (arrow-collection-unit R S)
  path-collection-unit R S d p
    = record {PathCollectionUnit R S d p}

-- ## Dependent

-- ### DependentPath

dependent-path-collection-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → (R : DependentRelation X')
  → {S : DependentRelation Y'}
  → DependentDecidable S
  → {F : ChainArrow X Y}
  → {p : ChainPath F}
  → DependentSimplePath X' Y' p
  → DependentPath
    (dependent-arrow-collection-unit R S) p
dependent-path-collection-unit {n = zero} R {S = S} d p'
  = path-collection-unit R S d p'
dependent-path-collection-unit {n = suc _} R d p'
  = record
  { tail
    = λ x {y} p'' → dependent-path-collection-unit
      (DependentRelation.tail R x)
      (DependentDecidable.tail d y)
      (DependentSimplePath.tail p' x p'')
  }

-- ### DependentPrelift'

dependent-prelift-collection-unit
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {R : DependentRelation X'}
  → DependentDecidable R
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {j : ChainCompose F F F}
  → {l : ChainLift F}
  → DependentSimpleLift X' i j l
  → DependentPrelift'
    (dependent-arrow-collection-unit R R) l
dependent-prelift-collection-unit {n = zero} _ _
  = tt
dependent-prelift-collection-unit {n = suc _} {R = R} d l'
  = record
  { path
    = λ {x} {y} f → dependent-path-collection-unit
      (DependentRelation.tail R x)
      (DependentDecidable.tail d y)
      (DependentSimpleLift.path l' f)
  ; tail
    = λ x → dependent-prelift-collection-unit
      (DependentDecidable.tail d x)
      (DependentSimpleLift.tail l' x)
  }

