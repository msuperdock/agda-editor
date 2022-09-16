module Category.Simple.Split.Lift.Compose where

open import Category.Core
  using (ChainArrow; ChainCompose; ChainIdentity; ChainObject; DependentObject;
    Object')
open import Category.Lift
  using (ChainLift; ChainPath)
open import Category.Simple.Lift
  using (DependentSimpleLift; DependentSimplePath; SimplePath)
open import Category.Simple.Split.Lift
  using (DependentSimpleSplitLift; DependentSimpleSplitLift';
    DependentSimpleSplitPath; DependentSimpleSplitPath'; SimpleSplitPath;
    SimpleSplitPath'; tt)
open import Category.Simple.State.Lift
  using (DependentSimpleStateLift; DependentSimpleStatePath; SimpleStatePath)
open import Category.Split.Core
  using (DependentSplitBase; SplitBase)
open import Category.Split.Core.Compose
  using (dependent-split-base-compose; split-base-compose)
open import Category.Split.Lift
  using (SplitPath)
open import Category.Split.Lift.Compose
  using (split-path-compose)
open import Category.Split.Lift.Unit
  using (split-path-unit; split-path-unit')
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### SimpleSplitPath

simple-split-path-compose
  : {X Y X' Y' X'' Y'' : Object'}
  → {p : SimpleStatePath X Y}
  → {p' : SimplePath X' Y'}
  → {p'' : SimplePath X'' Y''}
  → {a' : SplitBase X' X''}
  → {b' : SplitBase Y' Y''}
  → {a : SplitBase X X'}
  → {b : SplitBase Y Y'}
  → SimpleSplitPath' p' p'' a' b'
  → SimpleSplitPath p p' a b
  → SimpleSplitPath p p''
    (split-base-compose a' a)
    (split-base-compose b' b)
simple-split-path-compose q' q
  = record
  { SplitPath
    (split-path-compose
      (split-path-unit' q')
      (split-path-unit q))
  }

-- ## Dependent

-- ### DependentSimpleSplitPath

dependent-simple-split-path-compose
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' X''' : DependentObject X}
  → {Y' Y'' Y''' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {p : ChainPath F}
  → {p' : DependentSimpleStatePath X' Y' p}
  → {p'' : DependentSimplePath X'' Y'' p}
  → {p''' : DependentSimplePath X''' Y''' p}
  → {a' : DependentSplitBase X'' X'''}
  → {b' : DependentSplitBase Y'' Y'''}
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → DependentSimpleSplitPath' p'' p''' a' b'
  → DependentSimpleSplitPath p' p'' a b
  → DependentSimpleSplitPath p' p'''
    (dependent-split-base-compose a' a)
    (dependent-split-base-compose b' b)
dependent-simple-split-path-compose {n = zero} q' q
  = simple-split-path-compose q' q
dependent-simple-split-path-compose {n = suc _} q' q
  = record
  { tail
    = λ x p'''' → dependent-simple-split-path-compose
      (DependentSimpleSplitPath'.tail q' x p'''')
      (DependentSimpleSplitPath.tail q x p'''')
  }

-- ### DependentSimpleSplitLift

dependent-simple-split-lift-compose
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' X''' : DependentObject X}
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {j : ChainCompose F F F}
  → {l : ChainLift F}
  → {l' : DependentSimpleStateLift X' i l}
  → {l'' : DependentSimpleLift X'' i j l}
  → {l''' : DependentSimpleLift X''' i j l}
  → {a' : DependentSplitBase X'' X'''}
  → {a : DependentSplitBase X' X''}
  → DependentSimpleSplitLift' l'' l''' a'
  → DependentSimpleSplitLift l' l'' a
  → DependentSimpleSplitLift l' l'''
    (dependent-split-base-compose a' a)
dependent-simple-split-lift-compose {n = zero} _ _
  = tt
dependent-simple-split-lift-compose {n = suc _} p' p
  = record
  { path
    = λ f → dependent-simple-split-path-compose
      (DependentSimpleSplitLift'.path p' f)
      (DependentSimpleSplitLift.path p f)
  ; tail
    = λ x → dependent-simple-split-lift-compose
      (DependentSimpleSplitLift'.tail p' x)
      (DependentSimpleSplitLift.tail p x)
  }

