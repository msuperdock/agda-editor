module Category.Lift.List.Unit where

open import Category.Core
  using (Arrow'; ChainArrow; ChainCompose; ChainIdentity; ChainObject;
    DependentObject; Object')
open import Category.Core.List
  using (object-list)
open import Category.Core.List.Unit
  using (module ArrowListUnit; arrow-list-unit; dependent-arrow-list-unit)
open import Category.Lift
  using (ChainLift; ChainPath; DependentPath; DependentPrelift'; Path; tt)
open import Category.Simple.Lift
  using (DependentSimpleLift; DependentSimplePath; SimplePath)
open import Data.Any
  using (any)
open import Data.Equal
  using (_≡_; refl)
open import Data.List
  using (List)
open import Data.Maybe
  using (Maybe; just)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Vec
  using (Vec)

-- ## Base

-- ### Path

module _
  {X Y : Object'}
  where

  module PathListUnit
    (p : SimplePath X Y)
    where

    base
      : Object'.Object (object-list X)
      → Maybe (Object'.Object (object-list Y))
    base
      = List.map-maybe
        (SimplePath.base p)

    map
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → base xs ≡ just ys
      → Arrow'.Arrow (arrow-list-unit X Y) xs ys
    map (any xs) _
      with Vec.map-maybe (SimplePath.base p) xs
    map (any xs) refl | just ys
      = ArrowListUnit.arrow-identity X Y xs ys

  path-list-unit
    : SimplePath X Y
    → Path
      (arrow-list-unit X Y)
  path-list-unit p
    = record {PathListUnit p}

-- ## Dependent

-- ### DependentPath

dependent-path-list-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {p : ChainPath F}
  → DependentSimplePath X' Y' p
  → DependentPath
    (dependent-arrow-list-unit X' Y') p
dependent-path-list-unit {n = zero} p'
  = path-list-unit p'
dependent-path-list-unit {n = suc _} p'
  = record
  { tail
    = λ x p'' → dependent-path-list-unit
      (DependentSimplePath.tail p' x p'')
  }

-- ### DependentPrelift'

dependent-prelift-list-unit
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {j : ChainCompose F F F}
  → {l : ChainLift F}
  → DependentSimpleLift X' i j l
  → DependentPrelift'
    (dependent-arrow-list-unit X' X') l
dependent-prelift-list-unit {n = zero} _
  = tt
dependent-prelift-list-unit {n = suc _} l'
  = record
  { path
    = λ f → dependent-path-list-unit
      (DependentSimpleLift.path l' f)
  ; tail
    = λ x → dependent-prelift-list-unit
      (DependentSimpleLift.tail l' x)
  }

