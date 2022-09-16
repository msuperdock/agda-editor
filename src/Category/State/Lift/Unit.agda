module Category.State.Lift.Unit where

open import Category.Core
  using (ChainArrow; ChainIdentity; ChainObject; DependentObject; Object')
open import Category.Core.Unit
  using (arrow-equal-unit; arrow-unit; dependent-arrow-unit;
    dependent-identity-unit; identity-unit)
open import Category.Lift
  using (ChainLift; ChainPath)
open import Category.Simple.State.Lift
  using (DependentSimpleStateLift; DependentSimpleStatePath;
    DependentSimpleStatePathEqual; DependentSimpleStatePathIdentity;
    SimpleStatePath; SimpleStatePathEqual; SimpleStatePathIdentity)
open import Category.State.Lift
  using (DependentStateLift; DependentStatePath; DependentStatePathEqual;
    DependentStatePathIdentity; StatePath; StatePathEqual; StatePathIdentity;
    tt)
open import Data.Equal
  using (refl)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### StatePath

state-path-unit
  : {X Y : Object'}
  → SimpleStatePath X Y
  → StatePath
    (arrow-unit X Y)
state-path-unit p
  = record {SimpleStatePath p}

-- ### StatePathEqual

state-path-equal-unit
  : {X Y : Object'}
  → {p₁ p₂ : SimpleStatePath X Y}
  → SimpleStatePathEqual p₁ p₂
  → StatePathEqual
    (state-path-unit p₁)
    (state-path-unit p₂)
state-path-equal-unit q
  = record
  { SimpleStatePathEqual q
  ; map
    = λ x → arrow-equal-unit refl
      (SimpleStatePathEqual.base q x)
  }

-- ### StatePathIdentity

state-path-identity-unit
  : {X : Object'}
  → {p : SimpleStatePath X X}
  → SimpleStatePathIdentity p
  → StatePathIdentity
    (identity-unit X)
    (state-path-unit p)
state-path-identity-unit q
  = record
  { SimpleStatePathIdentity q
  ; map
    = λ x → arrow-equal-unit refl
      (SimpleStatePathIdentity.base q x)
  }

-- ## Dependent

-- ### DependentStatePath

dependent-state-path-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {p : ChainPath F}
  → DependentSimpleStatePath X' Y' p
  → DependentStatePath
    (dependent-arrow-unit X' Y') p
dependent-state-path-unit {n = zero} p'
  = state-path-unit p'
dependent-state-path-unit {n = suc _} p'
  = record
  { tail
    = λ x p'' → dependent-state-path-unit
      (DependentSimpleStatePath.tail p' x p'')
  }

-- ### DependentStatePathEqual

dependent-state-path-equal-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {p₁ p₂ : ChainPath F}
  → {p₁' : DependentSimpleStatePath X' Y' p₁}
  → {p₂' : DependentSimpleStatePath X' Y' p₂}
  → DependentSimpleStatePathEqual p₁' p₂'
  → DependentStatePathEqual
    (dependent-state-path-unit p₁')
    (dependent-state-path-unit p₂')
dependent-state-path-equal-unit {n = zero} q
  = state-path-equal-unit q
dependent-state-path-equal-unit {n = suc _} q
  = record
  { tail
    = λ x p₁'' p₂'' → dependent-state-path-equal-unit
      (DependentSimpleStatePathEqual.tail q x p₁'' p₂'')
  }

-- ### DependentStatePathIdentity

dependent-state-path-identity-unit
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {p : ChainPath F}
  → {p' : DependentSimpleStatePath X' X' p}
  → DependentSimpleStatePathIdentity p'
  → DependentStatePathIdentity
    (dependent-identity-unit X')
    (dependent-state-path-unit p')
dependent-state-path-identity-unit {n = zero} q
  = state-path-identity-unit q
dependent-state-path-identity-unit {n = suc _} q
  = record
  { tail
    = λ p'' → dependent-state-path-identity-unit
      (DependentSimpleStatePathIdentity.tail q p'')
  }

-- ### DependentStateLift

dependent-state-lift-unit
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {l : ChainLift F}
  → DependentSimpleStateLift X' i l
  → DependentStateLift i
    (dependent-identity-unit X') l
dependent-state-lift-unit {n = zero} _
  = tt
dependent-state-lift-unit {n = suc _} l'
  = record
  { path
    = λ f → dependent-state-path-unit
      (DependentSimpleStateLift.path l' f)
  ; path-equal
    = λ p → dependent-state-path-equal-unit
      (DependentSimpleStateLift.path-equal l' p)
  ; path-identity
    = λ x → dependent-state-path-identity-unit
      (DependentSimpleStateLift.path-identity l' x)
  ; tail
    = λ x → dependent-state-lift-unit
      (DependentSimpleStateLift.tail l' x)
  }

