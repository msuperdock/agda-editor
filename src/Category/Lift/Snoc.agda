module Category.Lift.Snoc where

open import Category.Core
  using (ChainArrow; ChainCompose; ChainIdentity; ChainObject; DependentArrow;
    DependentCompose; DependentIdentity; DependentObject)
open import Category.Core.Snoc
  using (chain-arrow-snoc)
open import Category.Lift
  using (ChainLift; ChainPath; DependentLift; DependentPath; chain-lift₁;
    chain-path₁)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Chain

-- ### ChainPath

chain-path-snoc
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {p : ChainPath F}
  → DependentPath F' p
  → ChainPath
    (chain-arrow-snoc F F')
chain-path-snoc {n = zero} p'
  = chain-path₁ p'
chain-path-snoc {n = suc _} {p = p} p'
  = record
  { ChainPath p
  ; tail
    = λ x y → chain-path-snoc
      (DependentPath.tail p' x y)
  }

-- ### ChainLift

chain-lift-snoc
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {i : ChainIdentity F}
  → {i' : DependentIdentity F'}
  → {j : ChainCompose F F F}
  → {j' : DependentCompose F' F' F'}
  → {l : ChainLift F}
  → DependentLift i i' j j' l
  → ChainLift
    (chain-arrow-snoc F F')
chain-lift-snoc {n = zero} {F' = F'} _
  = chain-lift₁ F'
chain-lift-snoc {n = suc _} l'
  = record
  { path
    = λ x → chain-path-snoc
      (DependentLift.path l' x)
  ; tail
    = λ x → chain-lift-snoc
      (DependentLift.tail l' x)
  }

