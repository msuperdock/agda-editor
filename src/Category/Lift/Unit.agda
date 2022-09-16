module Category.Lift.Unit where

open import Category.Core
  using (ChainArrow; ChainCompose; ChainIdentity; ChainObject; DependentObject;
    Object')
open import Category.Core.Unit
  using (arrow-unit; compose-unit; dependent-arrow-unit; dependent-compose-unit;
    dependent-identity-unit; identity-unit)
open import Category.Lift
  using (ChainLift; ChainPath; DependentLift; DependentPath;
    DependentPathCompose; DependentPathEqual; DependentPathIdentity; Path;
    PathCompose; PathEqual; PathIdentity; tt)
open import Category.Simple.Lift
  using (DependentSimpleLift; DependentSimplePath; DependentSimplePathCompose;
    DependentSimplePathEqual; DependentSimplePathIdentity; SimplePath;
    SimplePathCompose; SimplePathEqual; SimplePathIdentity)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### Path

path-unit
  : {X Y : Object'}
  → SimplePath X Y
  → Path
    (arrow-unit X Y)
path-unit p
  = record {SimplePath p}

-- ### PathEqual

path-equal-unit
  : {X Y : Object'}
  → {p₁ p₂ : SimplePath X Y}
  → SimplePathEqual p₁ p₂
  → PathEqual
    (path-unit p₁)
    (path-unit p₂)
path-equal-unit q
  = record {SimplePathEqual q}

-- ### PathIdentity

path-identity-unit
  : {X : Object'}
  → {p : SimplePath X X}
  → SimplePathIdentity p
  → PathIdentity
    (identity-unit X)
    (path-unit p)
path-identity-unit q
  = record {SimplePathIdentity q}

-- ### PathCompose

path-compose-unit
  : {X Y Z : Object'}
  → {p : SimplePath Y Z}
  → {q : SimplePath X Y}
  → {r : SimplePath X Z}
  → SimplePathCompose p q r
  → PathCompose
    (compose-unit X Y Z)
    (path-unit p)
    (path-unit q)
    (path-unit r)
path-compose-unit s
  = record {SimplePathCompose s}

-- ## Dependent

-- ### DependentPath

dependent-path-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {p : ChainPath F}
  → DependentSimplePath X' Y' p
  → DependentPath
    (dependent-arrow-unit X' Y') p
dependent-path-unit {n = zero} p'
  = path-unit p'
dependent-path-unit {n = suc _} p'
  = record
  { tail
    = λ x p'' → dependent-path-unit
      (DependentSimplePath.tail p' x p'')
  }

-- ### DependentPathEqual

dependent-path-equal-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {p₁ p₂ : ChainPath F}
  → {p₁' : DependentSimplePath X' Y' p₁}
  → {p₂' : DependentSimplePath X' Y' p₂}
  → DependentSimplePathEqual p₁' p₂'
  → DependentPathEqual
    (dependent-path-unit p₁')
    (dependent-path-unit p₂')
dependent-path-equal-unit {n = zero} q
  = path-equal-unit q
dependent-path-equal-unit {n = suc _} q
  = record
  { tail
    = λ x p₁'' p₂'' → dependent-path-equal-unit
      (DependentSimplePathEqual.tail q x p₁'' p₂'')
  }

-- ### DependentPathIdentity

dependent-path-identity-unit
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {p : ChainPath F}
  → {p' : DependentSimplePath X' X' p}
  → DependentSimplePathIdentity p'
  → DependentPathIdentity
    (dependent-identity-unit X')
    (dependent-path-unit p')
dependent-path-identity-unit {n = zero} q
  = path-identity-unit q
dependent-path-identity-unit {n = suc _} q
  = record
  { tail
    = λ p'' → dependent-path-identity-unit
      (DependentSimplePathIdentity.tail q p'')
  }

-- ### DependentPathCompose

dependent-path-compose-unit
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {Z' : DependentObject Z}
  → {F : ChainArrow Y Z}
  → {G : ChainArrow X Y}
  → {H : ChainArrow X Z}
  → {p : ChainPath F}
  → {q : ChainPath G}
  → {r : ChainPath H}
  → {p' : DependentSimplePath Y' Z' p}
  → {q' : DependentSimplePath X' Y' q}
  → {r' : DependentSimplePath X' Z' r}
  → DependentSimplePathCompose p' q' r'
  → DependentPathCompose
    (dependent-compose-unit X' Y' Z')
    (dependent-path-unit p')
    (dependent-path-unit q')
    (dependent-path-unit r')
dependent-path-compose-unit {n = zero} s
  = path-compose-unit s
dependent-path-compose-unit {n = suc _} s
  = record
  { tail
    = λ x p'' q'' r'' → dependent-path-compose-unit
      (DependentSimplePathCompose.tail s x p'' q'' r'')
  }

-- ### DependentLift

dependent-lift-unit
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {j : ChainCompose F F F}
  → {l : ChainLift F}
  → DependentSimpleLift X' i j l
  → DependentLift i
    (dependent-identity-unit X') j
    (dependent-compose-unit X' X' X') l
dependent-lift-unit {n = zero} _
  = tt
dependent-lift-unit {n = suc _} l'
  = record
  { path
    = λ f → dependent-path-unit
      (DependentSimpleLift.path l' f)
  ; path-equal
    = λ p → dependent-path-equal-unit
      (DependentSimpleLift.path-equal l' p)
  ; path-identity
    = λ x → dependent-path-identity-unit
      (DependentSimpleLift.path-identity l' x)
  ; path-compose
    = λ f g → dependent-path-compose-unit
      (DependentSimpleLift.path-compose l' f g)
  ; tail
    = λ x → dependent-lift-unit
      (DependentSimpleLift.tail l' x)
  }

