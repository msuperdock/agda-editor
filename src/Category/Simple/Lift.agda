module Category.Simple.Lift where

open import Category.Core
  using (Arrow'; ChainArrow; ChainArrow₀; ChainCompose; ChainCompose₀;
    ChainIdentity; ChainIdentity₀; ChainObject; ChainObject₀; DependentArrow;
    DependentCompose; DependentIdentity; DependentObject; Compose; Identity;
    Object')
open import Category.Lift
  using (ChainLift; ChainLift₀; ChainPath; DependentLift; DependentPath;
    DependentPathCompose; DependentPathEqual; DependentPathIdentity; Path;
    PathCompose; PathEqual; PathIdentity)
open import Data.Equal
  using (_≡_)
open import Data.Maybe
  using (Maybe; just)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### SimplePath

-- #### Definition

record SimplePath
  (X Y : Object')
  : Set
  where

  field

    base
      : Object'.Object X
      → Maybe (Object'.Object Y)

-- #### Conversion

path-simple
  : {X Y : Object'}
  → {F : Arrow' X Y}
  → Path F
  → SimplePath X Y
path-simple p
  = record {Path p}

-- ### SimplePathEqual

-- #### Definition

record SimplePathEqual
  {X Y : Object'}
  (p₁ p₂ : SimplePath X Y)
  : Set
  where

  field

    base
      : (x : Object'.Object X)
      → SimplePath.base p₁ x
        ≡ SimplePath.base p₂ x

-- #### Conversion

path-equal-simple
  : {X Y : Object'}
  → {F : Arrow' X Y}
  → {p₁ p₂ : Path F}
  → PathEqual p₁ p₂
  → SimplePathEqual
    (path-simple p₁)
    (path-simple p₂)
path-equal-simple q
  = record {PathEqual q}

-- ### SimplePathIdentity

-- #### Definition

record SimplePathIdentity
  {X : Object'}
  (p : SimplePath X X)
  : Set
  where

  field

    base
      : (x : Object'.Object X)
      → SimplePath.base p x ≡ just x

-- #### Conversion

path-identity-simple
  : {X : Object'}
  → {F : Arrow' X X}
  → {i : Identity F}
  → {p : Path F}
  → PathIdentity i p
  → SimplePathIdentity
    (path-simple p)
path-identity-simple q
  = record {PathIdentity q}

-- ### SimplePathCompose

-- #### Definition

record SimplePathCompose
  {X Y Z : Object'}
  (p : SimplePath Y Z)
  (q : SimplePath X Y)
  (r : SimplePath X Z)
  : Set
  where

  field

    base
      : (x : Object'.Object X)
      → {y : Object'.Object Y}
      → SimplePath.base q x ≡ just y
      → SimplePath.base r x
        ≡ SimplePath.base p y

-- #### Conversion

path-compose-simple
  : {X Y Z : Object'}
  → {F : Arrow' Y Z}
  → {G : Arrow' X Y}
  → {H : Arrow' X Z}
  → {j : Compose F G H}
  → {p : Path F}
  → {q : Path G}
  → {r : Path H}
  → PathCompose j p q r
  → SimplePathCompose
    (path-simple p)
    (path-simple q)
    (path-simple r)
path-compose-simple s
  = record {PathCompose s}

-- ## Dependent

-- ### DependentSimplePath

-- #### Types

DependentSimplePath
  : {n : ℕ}
  → {X Y : ChainObject n}
  → DependentObject X
  → DependentObject Y
  → {F : ChainArrow X Y}
  → ChainPath F
  → Set

record DependentSimplePath'
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  (X' : DependentObject X)
  (Y' : DependentObject Y)
  {F : ChainArrow X Y}
  (p : ChainPath F)
  : Set

-- #### Definitions

DependentSimplePath {n = zero} X' Y' _
  = SimplePath X' Y'
DependentSimplePath {n = suc _} X' Y' p
  = DependentSimplePath' X' Y' p

record DependentSimplePath' {_ X Y} X' Y' p where

  inductive
  no-eta-equality

  field

    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → (p' : ChainPath.base p x ≡ just y)
      → DependentSimplePath
        (DependentObject.tail X' x)
        (DependentObject.tail Y' y)
        (ChainPath.tail p x p')

module DependentSimplePath
  = DependentSimplePath'

-- #### Conversion

dependent-path-simple
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {p : ChainPath F}
  → DependentPath F' p
  → DependentSimplePath X' Y' p
dependent-path-simple {n = zero} p'
  = path-simple p'
dependent-path-simple {n = suc _} p'
  = record
  { tail
    = λ x p'' → dependent-path-simple
      (DependentPath.tail p' x p'')
  }

-- ### DependentSimplePathEqual

-- #### Types

DependentSimplePathEqual
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {p₁ p₂ : ChainPath F}
  → DependentSimplePath X' Y' p₁
  → DependentSimplePath X' Y' p₂
  → Set

record DependentSimplePathEqual'
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  {X' : DependentObject X}
  {Y' : DependentObject Y}
  {F : ChainArrow X Y}
  {p₁ p₂ : ChainPath F}
  (p₁' : DependentSimplePath X' Y' p₁)
  (p₂' : DependentSimplePath X' Y' p₂)
  : Set

-- #### Definitions

DependentSimplePathEqual {n = zero}
  = SimplePathEqual
DependentSimplePathEqual {n = suc _}
  = DependentSimplePathEqual'

record DependentSimplePathEqual' {_ X Y _ _ _ p₁ p₂} p₁' p₂' where

  inductive

  field
  
    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → (p₁'' : ChainPath.base p₁ x ≡ just y)
      → (p₂'' : ChainPath.base p₂ x ≡ just y)
      → DependentSimplePathEqual
        (DependentSimplePath.tail p₁' x p₁'')
        (DependentSimplePath.tail p₂' x p₂'')

module DependentSimplePathEqual
  = DependentSimplePathEqual'

-- #### Conversion

dependent-path-equal-simple
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {p₁ p₂ : ChainPath F}
  → {p₁' : DependentPath F' p₁}
  → {p₂' : DependentPath F' p₂}
  → DependentPathEqual p₁' p₂'
  → DependentSimplePathEqual
    (dependent-path-simple p₁')
    (dependent-path-simple p₂')
dependent-path-equal-simple {n = zero} q
  = path-equal-simple q
dependent-path-equal-simple {n = suc _} q
  = record
  { tail
    = λ x p₁'' p₂'' → dependent-path-equal-simple
      (DependentPathEqual.tail q x p₁'' p₂'')
  }

-- ### DependentSimplePathIdentity

-- #### Types

DependentSimplePathIdentity
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {p : ChainPath F}
  → DependentSimplePath X' X' p
  → Set

record DependentSimplePathIdentity'
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' : DependentObject X}
  {F : ChainArrow X X}
  {p : ChainPath F}
  (p' : DependentSimplePath X' X' p)
  : Set

-- #### Definitions

DependentSimplePathIdentity {n = zero} p'
  = SimplePathIdentity p'
DependentSimplePathIdentity {n = suc _} p'
  = DependentSimplePathIdentity' p'

record DependentSimplePathIdentity' {_ X _ _ p} p' where

  inductive

  field

    tail
      : {x : ChainObject.Object X}
      → (p'' : ChainPath.base p x ≡ just x)
      → DependentSimplePathIdentity
        (DependentSimplePath.tail p' x p'')

module DependentSimplePathIdentity
  = DependentSimplePathIdentity'

-- #### Conversion

dependent-path-identity-simple
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {i : DependentIdentity F'}
  → {p : ChainPath F}
  → {p' : DependentPath F' p}
  → DependentPathIdentity i p'
  → DependentSimplePathIdentity
    (dependent-path-simple p')
dependent-path-identity-simple {n = zero} q
  = path-identity-simple q
dependent-path-identity-simple {n = suc _} q
  = record
  { tail
    = λ p'' → dependent-path-identity-simple
      (DependentPathIdentity.tail q p'')
  }

-- ### DependentSimplePathCompose

-- #### Types

DependentSimplePathCompose
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
  → DependentSimplePath Y' Z' p
  → DependentSimplePath X' Y' q
  → DependentSimplePath X' Z' r
  → Set

record DependentSimplePathCompose'
  {n : ℕ}
  {X Y Z : ChainObject (suc n)}
  {X' : DependentObject X}
  {Y' : DependentObject Y}
  {Z' : DependentObject Z}
  {F : ChainArrow Y Z}
  {G : ChainArrow X Y}
  {H : ChainArrow X Z}
  {p : ChainPath F}
  {q : ChainPath G}
  {r : ChainPath H}
  (p' : DependentSimplePath Y' Z' p)
  (q' : DependentSimplePath X' Y' q)
  (r' : DependentSimplePath X' Z' r)
  : Set

-- #### Definitions

DependentSimplePathCompose {n = zero} p' q' r'
  = SimplePathCompose p' q' r'
DependentSimplePathCompose {n = suc _} p' q' r'
  = DependentSimplePathCompose' p' q' r'

record DependentSimplePathCompose' {_ X Y Z _ _ _ _ _ _ p q r} p' q' r' where

  inductive

  field

    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → {z : ChainObject.Object Z}
      → (p'' : ChainPath.base p y ≡ just z)
      → (q'' : ChainPath.base q x ≡ just y)
      → (r'' : ChainPath.base r x ≡ just z)
      → DependentSimplePathCompose
        (DependentSimplePath.tail p' y p'')
        (DependentSimplePath.tail q' x q'')
        (DependentSimplePath.tail r' x r'')

module DependentSimplePathCompose
  = DependentSimplePathCompose'

-- #### Conversion

dependent-path-compose-simple
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {Z' : DependentObject Z}
  → {F : ChainArrow Y Z}
  → {G : ChainArrow X Y}
  → {H : ChainArrow X Z}
  → {F' : DependentArrow Y' Z'}
  → {G' : DependentArrow X' Y'}
  → {H' : DependentArrow X' Z'}
  → {j : DependentCompose F' G' H'}
  → {p : ChainPath F}
  → {q : ChainPath G}
  → {r : ChainPath H}
  → {p' : DependentPath F' p}
  → {q' : DependentPath G' q}
  → {r' : DependentPath H' r}
  → DependentPathCompose j p' q' r'
  → DependentSimplePathCompose
    (dependent-path-simple p')
    (dependent-path-simple q')
    (dependent-path-simple r')
dependent-path-compose-simple {n = zero} s
  = path-compose-simple s
dependent-path-compose-simple {n = suc _} s
  = record
  { tail
    = λ x p'' q'' r'' → dependent-path-compose-simple
      (DependentPathCompose.tail s x p'' q'' r'')
  }

-- ### DependentSimplePrelift

-- #### Base

record DependentSimplePrelift₀
  {X : ChainObject₀}
  (X' : DependentObject X)
  {F : ChainArrow₀ X X}
  (j : ChainCompose₀ F F F)
  (l : ChainLift₀ F)
  : Set
  where

  constructor

    tt

-- #### Types

DependentSimplePrelift
  : {n : ℕ}
  → {X : ChainObject n}
  → DependentObject X
  → {F : ChainArrow X X}
  → ChainCompose F F F
  → ChainLift F
  → Set

record DependentSimplePrelift''
  {n : ℕ}
  {X : ChainObject (suc n)}
  (X' : DependentObject X)
  {F : ChainArrow X X}
  (j : ChainCompose F F F)
  (l : ChainLift F)
  : Set

-- #### Definitions

DependentSimplePrelift {n = zero}
  = DependentSimplePrelift₀
DependentSimplePrelift {n = suc _}
  = DependentSimplePrelift''

record DependentSimplePrelift'' {_ X} X' {F} j l where

  inductive
  no-eta-equality

  field

    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentSimplePath
        (DependentObject.tail X' x)
        (DependentObject.tail X' y)
        (ChainLift.path l f)

    path-compose
      : {x y z : ChainObject.Object X}
      → (f : ChainArrow.Arrow F y z)
      → (g : ChainArrow.Arrow F x y)
      → DependentSimplePathCompose
        (path f)
        (path g)
        (path (ChainCompose.compose j f g))

    tail
      : (x : ChainObject.Object X)
      → DependentSimplePrelift
        (DependentObject.tail X' x)
        (ChainCompose.tail j x x x)
        (ChainLift.tail l x)

module DependentSimplePrelift
  = DependentSimplePrelift''

-- ### DependentSimplePrelift'

-- #### Base

record DependentSimplePrelift₀'
  {X : ChainObject₀}
  (X' : DependentObject X)
  {F : ChainArrow₀ X X}
  (l : ChainLift₀ F)
  : Set
  where

  constructor

    tt

-- #### Types

DependentSimplePrelift'
  : {n : ℕ}
  → {X : ChainObject n}
  → DependentObject X
  → {F : ChainArrow X X}
  → ChainLift F
  → Set

record DependentSimplePrelift'''
  {n : ℕ}
  {X : ChainObject (suc n)}
  (X' : DependentObject X)
  {F : ChainArrow X X}
  (l : ChainLift F)
  : Set

-- #### Definitions

DependentSimplePrelift' {n = zero}
  = DependentSimplePrelift₀'
DependentSimplePrelift' {n = suc _}
  = DependentSimplePrelift'''

record DependentSimplePrelift''' {_ X} X' {F} l where

  inductive
  no-eta-equality

  field

    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentSimplePath
        (DependentObject.tail X' x)
        (DependentObject.tail X' y)
        (ChainLift.path l f)

    tail
      : (x : ChainObject.Object X)
      → DependentSimplePrelift'
        (DependentObject.tail X' x)
        (ChainLift.tail l x)

module DependentSimplePrelift'
  = DependentSimplePrelift'''

-- ### DependentSimpleLift

-- #### Base

record DependentSimpleLift₀
  {X : ChainObject₀}
  (X' : DependentObject X)
  {F : ChainArrow₀ X X}
  (i : ChainIdentity₀ F)
  (j : ChainCompose₀ F F F)
  (l : ChainLift₀ F)
  : Set
  where

  constructor

    tt

-- #### Types

DependentSimpleLift
  : {n : ℕ}
  → {X : ChainObject n}
  → DependentObject X
  → {F : ChainArrow X X}
  → ChainIdentity F
  → ChainCompose F F F
  → ChainLift F
  → Set

record DependentSimpleLift'
  {n : ℕ}
  {X : ChainObject (suc n)}
  (X' : DependentObject X)
  {F : ChainArrow X X}
  (i : ChainIdentity F)
  (j : ChainCompose F F F)
  (l : ChainLift F)
  : Set

-- #### Definitions

DependentSimpleLift {n = zero}
  = DependentSimpleLift₀
DependentSimpleLift {n = suc _}
  = DependentSimpleLift'

record DependentSimpleLift' {_ X} X' {F} i j l where

  inductive
  no-eta-equality

  field

    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentSimplePath
        (DependentObject.tail X' x)
        (DependentObject.tail X' y)
        (ChainLift.path l f)

    path-equal
      : {x y : ChainObject.Object X}
      → {f₁ f₂ : ChainArrow.Arrow F x y}
      → ChainArrow.ArrowEqual F f₁ f₂
      → DependentSimplePathEqual
        (path f₁)
        (path f₂)

    path-identity
      : (x : ChainObject.Object X)
      → DependentSimplePathIdentity
        (path (ChainIdentity.identity i x))

    path-compose
      : {x y z : ChainObject.Object X}
      → (f : ChainArrow.Arrow F y z)
      → (g : ChainArrow.Arrow F x y)
      → DependentSimplePathCompose
        (path f)
        (path g)
        (path (ChainCompose.compose j f g))

    tail
      : (x : ChainObject.Object X)
      → DependentSimpleLift
        (DependentObject.tail X' x)
        (ChainIdentity.tail i x)
        (ChainCompose.tail j x x x)
        (ChainLift.tail l x)

module DependentSimpleLift
  = DependentSimpleLift'

-- #### Conversion

dependent-lift-simple
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
  → DependentSimpleLift X' i j l
dependent-lift-simple {n = zero} _
  = tt
dependent-lift-simple {n = suc _} l
  = record
  { path
    = λ f → dependent-path-simple
      (DependentLift.path l f)
  ; path-equal
    = λ p → dependent-path-equal-simple
      (DependentLift.path-equal l p)
  ; path-identity
    = λ x → dependent-path-identity-simple
      (DependentLift.path-identity l x)
  ; path-compose
    = λ f g → dependent-path-compose-simple
      (DependentLift.path-compose l f g)
  ; tail
    = λ x → dependent-lift-simple
      (DependentLift.tail l x)
  }

