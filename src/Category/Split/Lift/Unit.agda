module Category.Split.Lift.Unit where

open import Category.Core
  using (ChainArrow; ChainCompose; ChainIdentity; ChainObject; DependentObject;
    Object')
open import Category.Core.Unit
  using (arrow-equal-unit)
open import Category.Lift
  using (ChainLift; ChainPath)
open import Category.Lift.Unit
  using (dependent-lift-unit; dependent-path-unit; path-unit)
open import Category.Simple.Lift
  using (DependentSimpleLift; DependentSimplePath; SimplePath)
open import Category.Simple.State.Lift
  using (DependentSimpleStateLift; DependentSimpleStatePath; SimpleStatePath)
open import Category.Simple.Split.Lift
  using (DependentSimpleSplitLift; DependentSimpleSplitPath; SimpleSplitPath;
    SimpleSplitPath')
open import Category.Split.Core
  using (DependentSplitBase; SplitBase)
open import Category.Split.Core.Unit
  using (dependent-split-map-unit; split-map-unit)
open import Category.Split.Lift
  using (DependentSplitLift; DependentSplitPath; SplitPath; SplitPath'; tt)
open import Category.State.Lift.Unit
  using (dependent-state-lift-unit; dependent-state-path-unit; state-path-unit)
open import Data.Equal
  using (refl)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### SplitPath

split-path-unit
  : {X Y X' Y' : Object'}
  → {p : SimpleStatePath X Y}
  → {p' : SimplePath X' Y'}
  → {a : SplitBase X X'}
  → {b : SplitBase Y Y'}
  → SimpleSplitPath p p' a b
  → SplitPath
    (state-path-unit p)
    (path-unit p')
    (split-map-unit a b)
split-path-unit q
  = record
  { SimpleSplitPath q
  ; unmap
    = λ x r → arrow-equal-unit refl
      (SimpleSplitPath.unbase q x r)
  }

-- ### SplitPath'

split-path-unit'
  : {X Y X' Y' : Object'}
  → {p : SimplePath X Y}
  → {p' : SimplePath X' Y'}
  → {a : SplitBase X X'}
  → {b : SplitBase Y Y'}
  → SimpleSplitPath' p p' a b
  → SplitPath'
    (path-unit p)
    (path-unit p')
    (split-map-unit a b)
split-path-unit' q
  = record
  { SimpleSplitPath' q
  ; unmap
    = λ x r r' → arrow-equal-unit refl
      (SimpleSplitPath'.unbase q x r r')
  }

-- ## Dependent

-- ### DependentSplitPath

dependent-split-path-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {p : ChainPath F}
  → {p' : DependentSimpleStatePath X' Y' p}
  → {p'' : DependentSimplePath X'' Y'' p}
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → DependentSimpleSplitPath p' p'' a b
  → DependentSplitPath
    (dependent-state-path-unit p')
    (dependent-path-unit p'')
    (dependent-split-map-unit a b)
dependent-split-path-unit {n = zero} q
  = split-path-unit q
dependent-split-path-unit {n = suc _} q
  = record
  { tail
    = λ x p''' → dependent-split-path-unit
      (DependentSimpleSplitPath.tail q x p''')
  }

-- ### DependentSplitLift

dependent-split-lift-unit
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {j : ChainCompose F F F}
  → {l : ChainLift F}
  → {l' : DependentSimpleStateLift X' i l}
  → {l'' : DependentSimpleLift X'' i j l}
  → {a : DependentSplitBase X' X''}
  → DependentSimpleSplitLift l' l'' a
  → DependentSplitLift
    (dependent-state-lift-unit l')
    (dependent-lift-unit l'')
    (dependent-split-map-unit a a)
dependent-split-lift-unit {n = zero} _
  = tt
dependent-split-lift-unit {n = suc _} p
  = record
  { path
    = λ f → dependent-split-path-unit
      (DependentSimpleSplitLift.path p f)
  ; tail
    = λ x → dependent-split-lift-unit
      (DependentSimpleSplitLift.tail p x)
  }

