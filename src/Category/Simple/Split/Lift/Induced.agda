module Category.Simple.Split.Lift.Induced where

open import Category.Core
  using (ChainArrow; ChainCompose; ChainIdentity; ChainObject; DependentObject)
open import Category.Lift
  using (ChainLift)
open import Category.Simple.Lift
  using (DependentSimpleLift; DependentSimplePrelift; DependentSimplePrelift')
open import Category.Simple.Lift.Induced
  using (dependent-simple-lift-induced; dependent-simple-lift-induced')
open import Category.Simple.Split.Lift
  using (DependentSimpleSplitLift; DependentSimpleSplitLift';
    DependentSimpleSplitPrelift; DependentSimpleSplitPrelift'; tt)
open import Category.Simple.State.Lift
  using (DependentSimpleStateLift)
open import Category.Split.Core
  using (DependentSplitBase)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Dependent

-- ### DependentSimpleSplitLift

dependent-simple-split-lift-induced
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {j : ChainCompose F F F}
  → {l : ChainLift F}
  → {l' : DependentSimpleStateLift X' i l}
  → {l'' : DependentSimplePrelift X'' j l}
  → {a : DependentSplitBase X' X''}
  → (p : DependentSimpleSplitPrelift l' l'' a)
  → DependentSimpleSplitLift l'
    (dependent-simple-lift-induced p) a
dependent-simple-split-lift-induced {n = zero} _
  = tt
dependent-simple-split-lift-induced {n = suc _} p
  = record
  { DependentSimpleSplitPrelift p
  ; tail
    = λ x → dependent-simple-split-lift-induced
      (DependentSimpleSplitPrelift.tail p x)
  }

-- ### DependentSimpleSplitLift'

dependent-simple-split-lift-induced'
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {j : ChainCompose F F F}
  → {l : ChainLift F}
  → {l' : DependentSimpleLift X' i j l}
  → {l'' : DependentSimplePrelift' X'' l}
  → {a : DependentSplitBase X' X''}
  → (p : DependentSimpleSplitPrelift' l' l'' a)
  → DependentSimpleSplitLift' l'
    (dependent-simple-lift-induced' p) a
dependent-simple-split-lift-induced' {n = zero} _
  = tt
dependent-simple-split-lift-induced' {n = suc _} p
  = record
  { DependentSimpleSplitPrelift' p
  ; tail
    = λ x → dependent-simple-split-lift-induced'
      (DependentSimpleSplitPrelift'.tail p x)
  }

