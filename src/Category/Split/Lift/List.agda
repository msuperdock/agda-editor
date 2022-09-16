module Category.Split.Lift.List where

open import Category.Core
  using (Arrow'; ChainArrow; ChainCompose; ChainIdentity; ChainObject;
    DependentArrow; DependentCompose; DependentIdentity; DependentObject;
    Object')
open import Category.Core.List
  using (module ArrowList; arrow-equal-list; arrow-list; object-list)
open import Category.Lift
  using (ChainLift; ChainPath; DependentLift; DependentPath; Path)
open import Category.Lift.List
  using (module PathList; dependent-lift-list; dependent-path-list; path-list)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitMap; SplitBase; SplitMap)
open import Category.Split.Core.List
  using (module SplitMapList; dependent-split-map-list; split-base-list;
    split-map-list)
open import Category.Split.Lift
  using (DependentSplitLift; DependentSplitPath; SplitPath; tt)
open import Category.State.Lift
  using (DependentStateLift; DependentStatePath; StatePath)
open import Category.State.Lift.List
  using (module StatePathList; dependent-state-lift-list;
    dependent-state-path-list; state-path-list)
open import Data.Any
  using (any)
open import Data.Equal
  using (_≡_; refl; sub; sym; trans)
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
  using (Vec; cons; nil)

-- ## Base

-- ### SplitPath

module _
  {X Y X' Y' : Object'}
  {F : Arrow' X Y}
  {F' : Arrow' X' Y'}
  {p : StatePath F}
  {p' : Path F'}
  {a : SplitBase X X'}
  {b : SplitBase Y Y'}
  {m : SplitMap F F' a b}
  where

  module SplitPathList
    (q : SplitPath p p' m)
    where

    base'
      : {n : ℕ}
      → (xs : Vec (Object'.Object X) n)
      → {xs' : Vec (Object'.Object X') n}
      → Vec.map-maybe (SplitBase.base a) xs ≡ just xs'
      → Vec.map-maybe (SplitBase.base b)
        (Vec.map (StatePath.base p) xs)
      ≡ Vec.map-maybe (Path.base p') xs'
    base' nil {xs' = nil} _
      = refl
    base' (cons x (any xs)) _
      with SplitBase.base a x
      | inspect (SplitBase.base a) x
      | Vec.map-maybe (SplitBase.base a) xs
      | inspect (Vec.map-maybe (SplitBase.base a)) xs
    base' (cons x (any xs)) {xs' = cons x' (any xs')} refl
      | just _ | [ r ] | just _ | [ rs ]
      with SplitBase.base b (StatePath.base p x)
      | Path.base p' x'
      | SplitPath.base q x r
      | Vec.map-maybe (SplitBase.base b)
        (Vec.map (StatePath.base p) xs)
      | Vec.map-maybe (Path.base p') xs'
      | base' xs rs
    ... | nothing | _ | refl | _ | _ | _
      = refl
    ... | just _ | _ | refl | nothing | _ | refl
      = refl
    ... | just _ | _ | refl | just _ | _ | refl
      = refl

    base
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-list X')}
      → SplitBase.base (split-base-list a) xs ≡ just xs'
      → SplitBase.base (split-base-list b)
        (StatePath.base (state-path-list p) xs)
      ≡ Path.base (path-list p') xs'
    base (any xs) _
      with Vec.map-maybe (SplitBase.base a) xs
      | inspect (Vec.map-maybe (SplitBase.base a)) xs
    base (any xs) refl | just _ | [ r ]
      = sub (Maybe.map any) (base' xs r)

    map-lookup
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-list X')}
      → {ys' : Object'.Object (object-list Y')}
      → (p'' : Path.base (path-list p') xs' ≡ just ys')
      → (r : SplitBase.base (split-base-list a) xs ≡ just xs')
      → (s : SplitBase.base (split-base-list b)
        (StatePath.base (state-path-list p) xs)
        ≡ just ys')
      → (k : Fin (List.length xs'))
      → ArrowList.LookupEqual F' xs' ys' k
        (SplitMapList.map-lookup m r s
          (StatePath.map (state-path-list p) xs) k)
        (PathList.map-lookup p' xs' p'' k)
    map-lookup (any xs) {xs' = any xs'} _ _ _ _
      with Vec.map-maybe (Path.base p') xs'
      | inspect (Vec.map-maybe (Path.base p')) xs'
      | Vec.map-maybe (SplitBase.base a) xs
      | inspect (Vec.map-maybe (SplitBase.base a)) xs
      | Vec.map-maybe (SplitBase.base b)
        (Vec.map (StatePath.base p) xs)
      | inspect (Vec.map-maybe (SplitBase.base b))
        (Vec.map (StatePath.base p) xs)
    map-lookup (any xs) {xs' = any xs'} refl refl refl k
      | just _ | [ p'' ] | just _ | [ r ] | just _ | [ s ]
      = ArrowList.just k
      $ Arrow'.arrow-equal' F'
      $ Arrow'.arrow-trans' F' (SplitMap.map-equal' m r' r' s' v
        (Arrow'.arrow-refl'' F refl u))
      $ SplitPath.map' q (Vec.lookup xs k) p''' r' v
      where
        ys = Vec.map (StatePath.base p) xs
        r' = Vec.lookup-map-just (SplitBase.base a) xs r k
        s' = Vec.lookup-map-just (SplitBase.base b) ys s k
        p''' = Vec.lookup-map-just (Path.base p') xs' p'' k
        u = Vec.lookup-map (StatePath.base p) xs k
        v = trans (SplitPath.base q (Vec.lookup xs k) r') p'''

    map
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-list X')}
      → {ys' : Object'.Object (object-list Y')}
      → (p'' : Path.base (path-list p') xs' ≡ just ys')
      → (r : SplitBase.base (split-base-list a) xs ≡ just xs')
      → (s : SplitBase.base (split-base-list b)
        (StatePath.base (state-path-list p) xs)
        ≡ just ys')
      → Arrow'.ArrowEqual (arrow-list F')
        (SplitMap.map (split-map-list m) r s
          (StatePath.map (state-path-list p) xs))
        (Path.map (path-list p') xs' p'')
    map xs p'' r s
      = record
      { lookup
        = map-lookup xs p'' r s
      }
    
    unbase
      : {n : ℕ}
      → (xs : Vec (Object'.Object X') n)
      → {ys : Vec (Object'.Object Y') n}
      → Path.base (path-list p') (any xs) ≡ just (any ys)
      → Vec.map (SplitBase.unbase b) ys
      ≡ Vec.map (StatePath.base p)
        (Vec.map (SplitBase.unbase a) xs)
    unbase nil {ys = nil} _
      = refl
    unbase (cons x (any xs)) _
      with Path.base p' x
      | inspect (Path.base p') x
      | Vec.map-maybe (Path.base p') xs
      | inspect (Vec.map-maybe (Path.base p')) xs
    unbase (cons x (any xs)) refl
      | just _ | [ p'' ] | just _ | [ ps'' ]
      = Vec.cons-equal
        (SplitPath.unbase q x p'')
        (unbase xs (sub (Maybe.map any) ps''))

    unmap-lookup
      : {n : ℕ}
      → (xs : Vec (Object'.Object X') n)
      → {ys : Vec (Object'.Object Y') n}
      → (p'' : Path.base (path-list p') (any xs) ≡ just (any ys))
      → (k : Fin n)
      → ArrowList.LookupEqual' F
        (Vec.map (SplitBase.unbase a) xs)
        (Vec.map (SplitBase.unbase a) xs)
        (Vec.map (SplitBase.unbase b) ys)
        (Vec.map (StatePath.base p)
          (Vec.map (SplitBase.unbase a) xs)) k
        (SplitMapList.unmap-lookup m
          (Path.map (path-list p') (any xs) p'') k)
        (StatePathList.map-lookup p
          (SplitBase.unbase (split-base-list a) (any xs)) k)
    unmap-lookup xs {ys = ys} p'' k
      with PathList.map-lookup p' (any xs) p'' k
      | PathList.map-lookup-equal p' xs p'' k
    ... | _ | refl
      = ArrowList.just' k
      $ Arrow'.arrow-trans' F (Arrow'.arrow-refl'' F s t)
      $ Arrow'.arrow-trans' F (SplitPath.unmap q x r')
      $ Arrow'.arrow-trans' F (StatePath.map-equal p (sym s))
      $ Arrow'.arrow-sym' F (Arrow'.arrow-refl'' F refl r)
      where
        x = Vec.lookup xs k
        r = Vec.lookup-map (StatePath.base p)
          (Vec.map (SplitBase.unbase a) xs) k
        r' = List.lookup-map-just (Path.base p') xs p'' k
        s = Vec.lookup-map (SplitBase.unbase a) xs k
        t = Vec.lookup-map (SplitBase.unbase b) ys k

    unmap
      : (xs : Object'.Object (object-list X'))
      → {ys : Object'.Object (object-list Y')}
      → (p'' : Path.base (path-list p') xs ≡ just ys)
      → Arrow'.ArrowEqual' (arrow-list F)
        (SplitMap.unmap (split-map-list m)
          (Path.map (path-list p') xs p''))
        (StatePath.map (state-path-list p)
          (SplitBase.unbase (split-base-list a) xs))
    unmap xs@(any xs') p''
      with List.map-maybe-length (Path.base p') xs p''
    ... | refl
      = arrow-equal-list F refl
        (unbase xs' p'')
        (unmap-lookup xs' p'')

  split-path-list
    : SplitPath p p' m
    → SplitPath
      (state-path-list p)
      (path-list p')
      (split-map-list m)
  split-path-list q
    = record {SplitPathList q}

-- ## Dependent

-- ### DependentSplitPath

dependent-split-path-list
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {F'' : DependentArrow X'' Y''}
  → {p : ChainPath F}
  → {p' : DependentStatePath F' p}
  → {p'' : DependentPath F'' p}
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → {m : DependentSplitMap F' F'' a b}
  → DependentSplitPath p' p'' m
  → DependentSplitPath
    (dependent-state-path-list p')
    (dependent-path-list p'')
    (dependent-split-map-list m)
dependent-split-path-list {n = zero} q
  = split-path-list q
dependent-split-path-list {n = suc _} q
  = record
  { tail
    = λ x p''' → dependent-split-path-list
      (DependentSplitPath.tail q x p''')
  }

-- ### DependentSplitLift

dependent-split-lift-list
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {F'' : DependentArrow X'' X''}
  → {i : ChainIdentity F}
  → {i' : DependentIdentity F'}
  → {i'' : DependentIdentity F''}
  → {j : ChainCompose F F F}
  → {j'' : DependentCompose F'' F'' F''}
  → {l : ChainLift F}
  → {l' : DependentStateLift i i' l}
  → {l'' : DependentLift i i'' j j'' l}
  → {a : DependentSplitBase X' X''}
  → {m : DependentSplitMap F' F'' a a}
  → DependentSplitLift l' l'' m
  → DependentSplitLift
    (dependent-state-lift-list l')
    (dependent-lift-list l'')
    (dependent-split-map-list m)
dependent-split-lift-list {n = zero} _
  = tt
dependent-split-lift-list {n = suc _} p
  = record
  { path
    = λ f → dependent-split-path-list
      (DependentSplitLift.path p f)
  ; tail
    = λ x → dependent-split-lift-list
      (DependentSplitLift.tail p x)
  }

