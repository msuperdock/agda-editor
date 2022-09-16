module Category.Split.Lift.Compose where

open import Category.Core
  using (Arrow'; ChainArrow; ChainCompose; ChainIdentity; ChainObject;
    DependentArrow; DependentCompose; DependentIdentity; DependentObject;
    Object')
open import Category.Lift
  using (ChainLift; ChainPath; DependentLift; DependentPath; Path)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitMap; SplitBase; SplitMap)
open import Category.Split.Core.Compose
  using (dependent-split-map-compose; split-base-compose; split-map-compose)
open import Category.Split.Lift
  using (DependentSplitLift; DependentSplitLift'; DependentSplitPath;
    DependentSplitPath'; SplitPath; SplitPath'; tt)
open import Category.State.Lift
  using (DependentStateLift; DependentStatePath; StatePath)
open import Data.Equal
  using (_≡_; sym; trans)
open import Data.Function
  using (_$_)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### SplitPath

module _
  {X Y X' Y' X'' Y'' : Object'}
  {F : Arrow' X Y}
  {F' : Arrow' X' Y'}
  {F'' : Arrow' X'' Y''}
  {p : StatePath F}
  {p' : Path F'}
  {p'' : Path F''}
  {a' : SplitBase X' X''}
  {b' : SplitBase Y' Y''}
  {a : SplitBase X X'}
  {b : SplitBase Y Y'}
  {m' : SplitMap F' F'' a' b'}
  {m : SplitMap F F' a b}
  where

  module SplitPathCompose
    (q' : SplitPath' p' p'' m')
    (q : SplitPath p p' m)
    where

    base
      : (x : Object'.Object X)
      → {x' : Object'.Object X''}
      → SplitBase.base (split-base-compose a' a) x ≡ just x'
      → SplitBase.base (split-base-compose b' b)
        (StatePath.base p x)
      ≡ Path.base p'' x'
    base x r'
      with SplitBase.base a x
      | inspect (SplitBase.base a) x
      | SplitBase.base b (StatePath.base p x)
      | inspect (SplitBase.base b) (StatePath.base p x)
    ... | just x' | [ r ] | nothing | [ s ]
      = sym (SplitPath'.base-nothing q' x'
        (trans (sym (SplitPath.base q x r)) s) r')
    ... | just x' | [ r ] | just _ | [ s ]
      = SplitPath'.base-just q' x'
        (trans (sym (SplitPath.base q x r)) s) r'

    map
      : (x : Object'.Object X)
      → {x' : Object'.Object X''}
      → {y' : Object'.Object Y''}
      → (r : Path.base p'' x' ≡ just y')
      → (s : SplitBase.base (split-base-compose a' a) x ≡ just x')
      → (t : SplitBase.base (split-base-compose b' b)
        (StatePath.base p x)
        ≡ just y')
      → Arrow'.ArrowEqual F''
        (SplitMap.map (split-map-compose m' m) s t
          (StatePath.map p x))
        (Path.map p'' x' r)
    map x r' s' t'
      with SplitBase.base a x
      | inspect (SplitBase.base a) x
      | SplitBase.base b (StatePath.base p x)
      | inspect (SplitBase.base b) (StatePath.base p x)
    ... | just x' | [ s ] | just _ | [ t ]
      = Arrow'.arrow-trans F'' (SplitMap.map-equal m' s' t'
        (SplitPath.map q x r s t))
      $ SplitPath'.map q' x' r r' s' t'
      where
        r = trans (sym (SplitPath.base q x s)) t
    
    unmap
      : (x : Object'.Object X'')
      → {y : Object'.Object Y''}
      → (r : Path.base p'' x ≡ just y)
      → Arrow'.ArrowEqual' F
        (SplitMap.unmap (split-map-compose m' m)
          (Path.map p'' x r))
        (StatePath.map p
          (SplitBase.unbase (split-base-compose a' a) x))
    unmap x' r'
      = Arrow'.arrow-trans' F (SplitMap.unmap-equal' m
        (SplitPath'.unmap q' x' r r'))
      $ SplitPath.unmap q x r
      where
        x = SplitBase.unbase a' x'
        r = SplitPath'.unbase' q' x' r'

  split-path-compose
    : SplitPath' p' p'' m'
    → SplitPath p p' m
    → SplitPath p p''
      (split-map-compose m' m)
  split-path-compose q' q
    = record {SplitPathCompose q' q}

-- ## Dependent

-- ### DependentSplitPath

dependent-split-path-compose
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' X''' : DependentObject X}
  → {Y' Y'' Y''' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {F'' : DependentArrow X'' Y''}
  → {F''' : DependentArrow X''' Y'''}
  → {p : ChainPath F}
  → {p' : DependentStatePath F' p}
  → {p'' : DependentPath F'' p}
  → {p''' : DependentPath F''' p}
  → {a' : DependentSplitBase X'' X'''}
  → {b' : DependentSplitBase Y'' Y'''}
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → {m' : DependentSplitMap F'' F''' a' b'}
  → {m : DependentSplitMap F' F'' a b}
  → DependentSplitPath' p'' p''' m'
  → DependentSplitPath p' p'' m
  → DependentSplitPath p' p'''
    (dependent-split-map-compose m' m)
dependent-split-path-compose {n = zero} q' q
  = split-path-compose q' q
dependent-split-path-compose {n = suc _} q' q
  = record
  { tail
    = λ x p'''' → dependent-split-path-compose
      (DependentSplitPath'.tail q' x p'''')
      (DependentSplitPath.tail q x p'''')
  }

-- ### DependentSplitLift

dependent-split-lift-compose
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' X''' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {F'' : DependentArrow X'' X''}
  → {F''' : DependentArrow X''' X'''}
  → {i : ChainIdentity F}
  → {i' : DependentIdentity F'}
  → {i'' : DependentIdentity F''}
  → {i''' : DependentIdentity F'''}
  → {j : ChainCompose F F F}
  → {j'' : DependentCompose F'' F'' F''}
  → {j''' : DependentCompose F''' F''' F'''}
  → {l : ChainLift F}
  → {l' : DependentStateLift i i' l}
  → {l'' : DependentLift i i'' j j'' l}
  → {l''' : DependentLift i i''' j j''' l}
  → {a' : DependentSplitBase X'' X'''}
  → {a : DependentSplitBase X' X''}
  → {m' : DependentSplitMap F'' F''' a' a'}
  → {m : DependentSplitMap F' F'' a a}
  → DependentSplitLift' l'' l''' m'
  → DependentSplitLift l' l'' m
  → DependentSplitLift l' l'''
    (dependent-split-map-compose m' m)
dependent-split-lift-compose {n = zero} _ _
  = tt
dependent-split-lift-compose {n = suc _} p' p
  = record
  { path
    = λ f → dependent-split-path-compose
      (DependentSplitLift'.path p' f)
      (DependentSplitLift.path p f)
  ; tail
    = λ x → dependent-split-lift-compose
      (DependentSplitLift'.tail p' x)
      (DependentSplitLift.tail p x)
  }

