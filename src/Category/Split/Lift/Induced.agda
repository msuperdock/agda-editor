module Category.Split.Lift.Induced where

open import Category.Core
  using (ChainArrow; ChainCompose; ChainIdentity; ChainObject; DependentArrow;
    DependentCompose; DependentComposeEqual; DependentIdentity; DependentObject)
open import Category.Lift
  using (ChainLift; DependentLift; DependentPrelift; DependentPrelift')
open import Category.Lift.Induced
  using (dependent-lift-induced; dependent-lift-induced')
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitCompose; DependentSplitIdentity;
    DependentSplitMap)
open import Category.Split.Lift
  using (DependentSplitLift; DependentSplitLift'; DependentSplitPrelift;
    DependentSplitPrelift'; tt)
open import Category.State.Lift
  using (DependentStateLift)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Dependent

-- ### DependentSplitLift

dependent-split-lift-induced
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
  → {l'' : DependentPrelift j j'' l}
  → {a : DependentSplitBase X' X''}
  → {m : DependentSplitMap F' F'' a a}
  → (p : DependentSplitIdentity i' i'' m)
  → (q : DependentSplitPrelift l' l'' m)
  → DependentSplitLift l'
    (dependent-lift-induced p q) m
dependent-split-lift-induced {n = zero} _ _
  = tt
dependent-split-lift-induced {n = suc _} p q
  = record
  { DependentSplitPrelift q
  ; tail
    = λ x → dependent-split-lift-induced
      (DependentSplitIdentity.tail p x)
      (DependentSplitPrelift.tail q x)
  }

-- ### DependentSplitLift'

dependent-split-lift-induced'
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
  → {j' : DependentCompose F' F' F'}
  → {j'' : DependentCompose F'' F'' F''}
  → (p : DependentComposeEqual j')
  → {l : ChainLift F}
  → {l' : DependentLift i i' j j' l}
  → {l'' : DependentPrelift' F'' l}
  → {a : DependentSplitBase X' X''}
  → {m : DependentSplitMap F' F'' a a}
  → (q : DependentSplitIdentity i' i'' m)
  → (r : DependentSplitCompose j' j'' m m m)
  → (s : DependentSplitPrelift' l' l'' m)
  → DependentSplitLift' l'
    (dependent-lift-induced' p q r s) m
dependent-split-lift-induced' {n = zero} _ _ _ _
  = tt
dependent-split-lift-induced' {n = suc _} p q r s
  = record
  { DependentSplitPrelift' s
  ; tail
    = λ x → dependent-split-lift-induced'
      (DependentComposeEqual.tail p x x x)
      (DependentSplitIdentity.tail q x)
      (DependentSplitCompose.tail r x x x)
      (DependentSplitPrelift'.tail s x)
  }

