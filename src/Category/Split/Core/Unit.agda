module Category.Split.Core.Unit where

open import Category.Core
  using (ChainObject; DependentObject; Object')
open import Category.Core.Unit
  using (arrow-unit; dependent-arrow-unit; dependent-compose-unit;
    dependent-identity-unit; compose-unit; identity-unit)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitCompose; DependentSplitIdentity;
    DependentSplitMap; SplitBase; SplitCompose; SplitIdentity; SplitMap)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### SplitMap

split-map-unit
  : {X Y X' Y' : Object'}
  → (a : SplitBase X X')
  → (b : SplitBase Y Y')
  → SplitMap
    (arrow-unit X Y)
    (arrow-unit X' Y') a b
split-map-unit _ _
  = record {}

-- ### SplitIdentity

split-identity-unit
  : {X X' : Object'}
  → (a : SplitBase X X')
  → SplitIdentity
    (identity-unit X)
    (identity-unit X')
    (split-map-unit a a)
split-identity-unit _
  = record {}

-- ### SplitCompose

split-compose-unit
  : {X Y Z X' Y' Z' : Object'}
  → (a : SplitBase X X')
  → (b : SplitBase Y Y')
  → (c : SplitBase Z Z')
  → SplitCompose
    (compose-unit X Y Z)
    (compose-unit X' Y' Z')
    (split-map-unit b c)
    (split-map-unit a b)
    (split-map-unit a c)
split-compose-unit _ _ _
  = record {}

-- ## Dependent

-- ### DependentSplitMap

dependent-split-map-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → (a : DependentSplitBase X' X'')
  → (b : DependentSplitBase Y' Y'')
  → DependentSplitMap
    (dependent-arrow-unit X' Y')
    (dependent-arrow-unit X'' Y'') a b
dependent-split-map-unit {n = zero} a b
  = split-map-unit a b
dependent-split-map-unit {n = suc _} a b
  = record
  { tail
    = λ x y → dependent-split-map-unit
      (DependentSplitBase.tail a x)
      (DependentSplitBase.tail b y)
  }

-- ### DependentSplitIdentity

dependent-split-identity-unit
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → (a : DependentSplitBase X' X'')
  → DependentSplitIdentity
    (dependent-identity-unit X')
    (dependent-identity-unit X'')
    (dependent-split-map-unit a a)
dependent-split-identity-unit {n = zero} a
  = split-identity-unit a
dependent-split-identity-unit {n = suc _} a
  = record
  { tail
    = λ x → dependent-split-identity-unit
      (DependentSplitBase.tail a x)
  }

-- ### DependentSplitCompose

dependent-split-compose-unit
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {Z' Z'' : DependentObject Z}
  → (a : DependentSplitBase X' X'')
  → (b : DependentSplitBase Y' Y'')
  → (c : DependentSplitBase Z' Z'')
  → DependentSplitCompose
    (dependent-compose-unit X' Y' Z')
    (dependent-compose-unit X'' Y'' Z'')
    (dependent-split-map-unit b c)
    (dependent-split-map-unit a b)
    (dependent-split-map-unit a c)
dependent-split-compose-unit {n = zero} a b c
  = split-compose-unit a b c
dependent-split-compose-unit {n = suc _} a b c
  = record
  { tail
    = λ x y z → dependent-split-compose-unit
      (DependentSplitBase.tail a x)
      (DependentSplitBase.tail b y)
      (DependentSplitBase.tail c z)
  }

