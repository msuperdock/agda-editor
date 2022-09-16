module Category.Split.Lift.List.Unit where

open import Category.Core
  using (Arrow'; ChainArrow; ChainCompose; ChainIdentity; ChainObject;
    DependentObject; Object')
open import Category.Core.List
  using (module ArrowList; arrow-list; object-list)
open import Category.Core.List.Unit
  using (module ArrowListUnit; arrow-list-unit)
open import Category.Core.Unit
  using (module ArrowUnit; arrow-unit)
open import Category.Lift
  using (ChainLift; ChainPath; Path)
open import Category.Lift.List
  using (module PathList; dependent-lift-list; dependent-path-list; path-list)
open import Category.Lift.List.Unit
  using (dependent-path-list-unit; dependent-prelift-list-unit; path-list-unit)
open import Category.Lift.Unit
  using (dependent-lift-unit; dependent-path-unit; path-unit)
open import Category.Simple.Lift
  using (DependentSimpleLift; DependentSimplePath; SimplePath)
open import Category.Split.Core
  using (SplitBase; SplitMap)
open import Category.Split.Core.Identity
  using (split-base-identity)
open import Category.Split.Core.List.Unit
  using (module SplitMapListUnit; dependent-split-map-list-unit;
    split-map-list-unit)
open import Category.Split.Lift
  using (DependentSplitPath'; DependentSplitPrelift'; SplitPath'; tt)
open import Data.Any
  using (any)
open import Data.Empty
  using (⊥-elim)
open import Data.Equal
  using (_≡_; refl; sym; trans)
open import Data.Fin
  using (Fin)
open import Data.Function
  using (_$_)
open import Data.Inspect
  using ([_]; inspect)
open import Data.List
  using (List)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Vec
  using (Vec)

-- ## Base

-- ### SplitPath'

module _
  {X Y : Object'}
  where

  module SplitPathListUnit
    (p : SimplePath X Y)
    where

    base-nothing
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-list X)}
      → Path.base (path-list (path-unit p)) xs ≡ nothing
      → SplitBase.base (split-base-identity (object-list X)) xs ≡ just xs'
      → Path.base (path-list-unit p) xs' ≡ nothing
    base-nothing _ p' refl
      = p'

    base-just
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-list X)}
      → Path.base (path-list (path-unit p)) xs ≡ just ys
      → SplitBase.base (split-base-identity (object-list X)) xs ≡ just xs'
      → SplitBase.base (split-base-identity (object-list Y)) ys
        ≡ Path.base (path-list-unit p) xs'
    base-just _ p' refl
      = sym p'

    map-lookup
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → (q : Path.base (path-list (path-unit p)) xs ≡ just ys)
      → (q' : Path.base (path-list-unit p) xs ≡ just ys)
      → (k : Fin (List.length xs))
      → ArrowListUnit.Arrow.lookup
        (SplitMap.map (split-map-list-unit X Y) refl refl
          (Path.map (path-list (path-unit p)) xs q)) k
      ≡ ArrowListUnit.Arrow.lookup
        (Path.map (path-list-unit p) xs q') k
    map-lookup xs@(any xs') q _ k
      with PathList.map-lookup (path-unit p) xs q k
      | inspect (PathList.map-lookup (path-unit p) xs q) k
    ... | nothing | _
      with Vec.map-maybe (SimplePath.base p) xs'
      | inspect (Vec.map-maybe (SimplePath.base p)) xs'
    map-lookup _ refl _ _ | _ | [ r ] | just _ | _
      = ⊥-elim (Maybe.just≢nothing r)
    map-lookup (any xs') _ _ _ | just _ | _
      with Vec.map-maybe (SimplePath.base p) xs'
      | inspect (Vec.map-maybe (SimplePath.base p)) xs'
    map-lookup _ refl refl _ | _ | [ refl ] | just _ | _
      = refl

    map
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-list X)}
      → {ys' : Object'.Object (object-list Y)}
      → (q : Path.base (path-list (path-unit p)) xs ≡ just ys)
      → (q' : Path.base (path-list-unit p) xs' ≡ just ys')
      → (r : SplitBase.base (split-base-identity (object-list X)) xs ≡ just xs')
      → (s : SplitBase.base (split-base-identity (object-list Y)) ys ≡ just ys')
      → Arrow'.ArrowEqual (arrow-list-unit X Y)
        (SplitMap.map (split-map-list-unit X Y) r s
          (Path.map (path-list (path-unit p)) xs q))
        (Path.map (path-list-unit p) xs' q')
    map xs q q' refl refl
      = record
      { lookup
        = map-lookup xs q q'
      }
    
    unmap-lookup
      : {n : ℕ}
      → (xs : Vec (Object'.Object X) n)
      → {ys : Vec (Object'.Object Y) n}
      → (q q' : List.map-maybe (SimplePath.base p) (any xs) ≡ just (any ys))
      → (k : Fin n)
      → ArrowList.LookupEqual (arrow-unit X Y) (any xs) (any ys) k
        (SplitMapListUnit.unmap-lookup X Y
          (Path.map (path-list-unit p) (any xs) q') k)
        (PathList.map-lookup (path-unit p)
          (SplitBase.unbase (split-base-identity (object-list X)) (any xs)) q k)
    unmap-lookup xs _ _ _
      with Vec.map-maybe (SimplePath.base p) xs
      | inspect (Vec.map-maybe (SimplePath.base p)) xs
    unmap-lookup _ refl refl k | just _ | _
      = ArrowList.just k ArrowUnit.tt

    unmap
      : (xs : Object'.Object (object-list X))
      → {ys ys' : Object'.Object (object-list Y)}
      → (q : Path.base (path-list (path-unit p))
        (SplitBase.unbase (split-base-identity (object-list X)) xs)
        ≡ just ys)
      → (q' : Path.base (path-list-unit p) xs ≡ just ys')
      → Arrow'.ArrowEqual' (arrow-list (arrow-unit X Y))
        (SplitMap.unmap (split-map-list-unit X Y)
          (Path.map (path-list-unit p) xs q'))
        (Path.map (path-list (path-unit p))
          (SplitBase.unbase (split-base-identity (object-list X)) xs) q)
    unmap xs@(any xs') q q'
      with List.map-maybe-length (SimplePath.base p) xs q
      | List.map-maybe-length (SimplePath.base p) xs q'
      | trans (sym q) q'
    ... | refl | refl | refl
      = Arrow'.arrow-equal
      $ record
      { lookup
        = unmap-lookup xs' q q'
      }

  split-path-list-unit
    : (p : SimplePath X Y)
    → SplitPath'
      (path-list
        (path-unit p))
      (path-list-unit p)
      (split-map-list-unit X Y)
  split-path-list-unit p
    = record {SplitPathListUnit p}

-- ## Dependent

-- ### DependentSplitPath'

dependent-split-path-list-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {p : ChainPath F}
  → (p' : DependentSimplePath X' Y' p)
  → DependentSplitPath'
    (dependent-path-list
      (dependent-path-unit p'))
    (dependent-path-list-unit p')
    (dependent-split-map-list-unit X' Y')
dependent-split-path-list-unit {n = zero} p'
  = split-path-list-unit p'
dependent-split-path-list-unit {n = suc _} p'
  = record
  { tail
    = λ x p''' → dependent-split-path-list-unit
      (DependentSimplePath.tail p' x p''')
  }

-- ### DependentSplitPrelift'

dependent-split-prelift-list-unit
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {j : ChainCompose F F F}
  → {l : ChainLift F}
  → (l' : DependentSimpleLift X' i j l)
  → DependentSplitPrelift'
    (dependent-lift-list
      (dependent-lift-unit l'))
    (dependent-prelift-list-unit l')
    (dependent-split-map-list-unit X' X')
dependent-split-prelift-list-unit {n = zero} _
  = tt
dependent-split-prelift-list-unit {n = suc _} l'
  = record
  { path
    = λ f → dependent-split-path-list-unit
      (DependentSimpleLift.path l' f)
  ; tail
    = λ x → dependent-split-prelift-list-unit
      (DependentSimpleLift.tail l' x)
  }

