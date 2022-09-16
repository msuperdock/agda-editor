module Category.Lift where

open import Category.Core
  using (Arrow'; ChainArrow; ChainArrow₀; ChainCompose; ChainCompose₀;
    ChainIdentity; ChainIdentity₀; ChainObject; ChainObject₀; Compose;
    DependentArrow; DependentArrow₁; DependentCompose; DependentCompose₁;
    DependentIdentity; DependentIdentity₁; DependentObject; DependentObject₁;
    Identity; Object'; chain-arrow₁)
open import Data.Equal
  using (_≡_)
open import Data.Maybe
  using (Maybe; just)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### Path

record Path
  {X Y : Object'}
  (F : Arrow' X Y)
  : Set
  where

  no-eta-equality

  field

    base
      : Object'.Object X
      → Maybe (Object'.Object Y)

    map
      : (x : Object'.Object X)
      → {y : Object'.Object Y}
      → base x ≡ just y
      → Arrow'.Arrow F x y

-- ### PathEqual

record PathEqual
  {X Y : Object'}
  {F : Arrow' X Y}
  (p₁ p₂ : Path F)
  : Set
  where

  field

    base
      : (x : Object'.Object X)
      → Path.base p₁ x
        ≡ Path.base p₂ x

    map
      : (x : Object'.Object X)
      → {y : Object'.Object Y}
      → (p₁' : Path.base p₁ x ≡ just y)
      → (p₂' : Path.base p₂ x ≡ just y)
      → Arrow'.ArrowEqual F
        (Path.map p₁ x p₁')
        (Path.map p₂ x p₂')

-- ### PathIdentity

record PathIdentity
  {X : Object'}
  {F : Arrow' X X}
  (i : Identity F)
  (p : Path F)
  : Set
  where

  field

    base
      : (x : Object'.Object X)
      → Path.base p x ≡ just x

    map
      : {x : Object'.Object X}
      → (p' : Path.base p x ≡ just x)
      → Arrow'.ArrowEqual F
        (Path.map p x p')
        (Identity.identity i x)

-- ### PathCompose

record PathCompose
  {X Y Z : Object'}
  {F : Arrow' Y Z}
  {G : Arrow' X Y}
  {H : Arrow' X Z}
  (j : Compose F G H)
  (p : Path F)
  (q : Path G)
  (r : Path H)
  : Set
  where

  field

    base
      : (x : Object'.Object X)
      → {y : Object'.Object Y}
      → Path.base q x ≡ just y
      → Path.base r x
        ≡ Path.base p y

    map
      : (x : Object'.Object X)
      → {y : Object'.Object Y}
      → {z : Object'.Object Z}
      → (p' : Path.base p y ≡ just z)
      → (q' : Path.base q x ≡ just y)
      → (r' : Path.base r x ≡ just z)
      → Arrow'.ArrowEqual H
        (Path.map r x r')
        (Compose.compose j
          (Path.map p y p')
          (Path.map q x q'))

-- ## Chain

-- ### ChainPath

-- #### Base

record ChainPath₀
  {X Y : ChainObject₀}
  (F : ChainArrow₀ X Y)
  : Set
  where

  constructor

    tt

-- #### Types

ChainPath
  : {n : ℕ}
  → {X Y : ChainObject n}
  → ChainArrow X Y
  → Set

record ChainPath'
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  (F : ChainArrow X Y)
  : Set

-- #### Definitions

ChainPath {n = zero}
  = ChainPath₀
ChainPath {n = suc _}
  = ChainPath'

record ChainPath' {_ X Y} F where

  inductive
  no-eta-equality

  field

    head
      : Path
        (ChainArrow.head F)

  open Path head public

  field

    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → base x ≡ just y
      → ChainPath
        (ChainArrow.tail F x y)

module ChainPath
  = ChainPath'

-- #### Construction

chain-path₁
  : {X Y : Object'}
  → {F : Arrow' X Y}
  → Path F
  → ChainPath
    (chain-arrow₁ F)
chain-path₁ p
  = record
  { head
    = p
  }

-- ### ChainLift

-- #### Base

record ChainLift₀
  {X : ChainObject₀}
  (F : ChainArrow₀ X X)
  : Set
  where

  constructor

    tt

-- #### Types

ChainLift
  : {n : ℕ}
  → {X : ChainObject n}
  → ChainArrow X X
  → Set

record ChainLift'
  {n : ℕ}
  {X : ChainObject (suc n)}
  (F : ChainArrow X X)
  : Set

-- #### Definitions

ChainLift {n = zero}
  = ChainLift₀
ChainLift {n = suc _}
  = ChainLift'

record ChainLift' {_ X} F where

  inductive
  no-eta-equality

  field

    path
      : {x y : ChainObject.Object X}
      → ChainArrow.Arrow F x y
      → ChainPath
        (ChainArrow.tail F x y)

    tail
      : (x : ChainObject.Object X)
      → ChainLift
        (ChainArrow.tail F x x)

module ChainLift
  = ChainLift'

-- #### Construction

chain-lift₁
  : {X : Object'}
  → (F : Arrow' X X)
  → ChainLift
    (chain-arrow₁ F)
chain-lift₁ _
  = record {}

-- ## Dependent

-- ### DependentPath

-- #### Types

DependentPath
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → DependentArrow X' Y'
  → ChainPath F
  → Set

record DependentPath'
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  {X' : DependentObject X}
  {Y' : DependentObject Y}
  {F : ChainArrow X Y}
  (F' : DependentArrow X' Y')
  (p : ChainPath F)
  : Set

-- #### Definitions

DependentPath {n = zero} F' _
  = Path F'
DependentPath {n = suc _} F' p
  = DependentPath' F' p

record DependentPath' {_ X Y} F' p where

  inductive
  no-eta-equality

  field

    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → (p' : ChainPath.base p x ≡ just y)
      → DependentPath
        (DependentArrow.tail F' x y)
        (ChainPath.tail p x p')

module DependentPath
  = DependentPath'

-- ### DependentPathEqual

-- #### Types

DependentPathEqual
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {p₁ p₂ : ChainPath F}
  → DependentPath F' p₁
  → DependentPath F' p₂
  → Set

record DependentPathEqual'
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  {X' : DependentObject X}
  {Y' : DependentObject Y}
  {F : ChainArrow X Y}
  {F' : DependentArrow X' Y'}
  {p₁ p₂ : ChainPath F}
  (p₁' : DependentPath F' p₁)
  (p₂' : DependentPath F' p₂)
  : Set

-- #### Definitions

DependentPathEqual {n = zero}
  = PathEqual
DependentPathEqual {n = suc _}
  = DependentPathEqual'

record DependentPathEqual' {_ X Y _ _ _ _ p₁ p₂} p₁' p₂' where

  inductive

  field

    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → (p₁'' : ChainPath.base p₁ x ≡ just y)
      → (p₂'' : ChainPath.base p₂ x ≡ just y)
      → DependentPathEqual
        (DependentPath.tail p₁' x p₁'')
        (DependentPath.tail p₂' x p₂'')

module DependentPathEqual
  = DependentPathEqual'

-- ### DependentPathIdentity

-- #### Types

DependentPathIdentity
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → DependentIdentity F'
  → {p : ChainPath F}
  → DependentPath F' p
  → Set

record DependentPathIdentity'
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' : DependentObject X}
  {F : ChainArrow X X}
  {F' : DependentArrow X' X'}
  (i : DependentIdentity F')
  {p : ChainPath F}
  (p' : DependentPath F' p)
  : Set

-- #### Definitions

DependentPathIdentity {n = zero} i p'
  = PathIdentity i p'
DependentPathIdentity {n = suc _} i p'
  = DependentPathIdentity' i p'

record DependentPathIdentity' {_ X} i {p} p' where

  inductive

  field

    tail
      : {x : ChainObject.Object X}
      → (p'' : ChainPath.base p x ≡ just x)
      → DependentPathIdentity
        (DependentIdentity.tail i x)
        (DependentPath.tail p' x p'')

module DependentPathIdentity
  = DependentPathIdentity'

-- ### DependentPathCompose

-- #### Types

DependentPathCompose
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
  → DependentCompose F' G' H'
  → {p : ChainPath F}
  → {q : ChainPath G}
  → {r : ChainPath H}
  → DependentPath F' p
  → DependentPath G' q
  → DependentPath H' r
  → Set

record DependentPathCompose'
  {n : ℕ}
  {X Y Z : ChainObject (suc n)}
  {X' : DependentObject X}
  {Y' : DependentObject Y}
  {Z' : DependentObject Z}
  {F : ChainArrow Y Z}
  {G : ChainArrow X Y}
  {H : ChainArrow X Z}
  {F' : DependentArrow Y' Z'}
  {G' : DependentArrow X' Y'}
  {H' : DependentArrow X' Z'}
  (j : DependentCompose F' G' H')
  {p : ChainPath F}
  {q : ChainPath G}
  {r : ChainPath H}
  (p' : DependentPath F' p)
  (q' : DependentPath G' q)
  (r' : DependentPath H' r)
  : Set

-- #### Definitions

DependentPathCompose {n = zero} j p' q' r'
  = PathCompose j p' q' r'
DependentPathCompose {n = suc _} j p' q' r'
  = DependentPathCompose' j p' q' r'

record DependentPathCompose' {_ X Y Z} j {p q r} p' q' r' where

  inductive

  field

    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → {z : ChainObject.Object Z}
      → (p'' : ChainPath.base p y ≡ just z)
      → (q'' : ChainPath.base q x ≡ just y)
      → (r'' : ChainPath.base r x ≡ just z)
      → DependentPathCompose
        (DependentCompose.tail j x y z)
        (DependentPath.tail p' y p'')
        (DependentPath.tail q' x q'')
        (DependentPath.tail r' x r'')

module DependentPathCompose
  = DependentPathCompose'

-- ### DependentPrelift

-- #### Base

record DependentPrelift₀
  {X : ChainObject₀}
  {X' : DependentObject X}
  {F : ChainArrow₀ X X}
  {F' : DependentArrow X' X'}
  (j : ChainCompose₀ F F F)
  (j' : DependentCompose F' F' F')
  (l : ChainLift₀ F)
  : Set
  where

  constructor

    tt

-- #### Types

DependentPrelift
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → ChainCompose F F F
  → DependentCompose F' F' F'
  → ChainLift F
  → Set

record DependentPrelift''
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' : DependentObject X}
  {F : ChainArrow X X}
  {F' : DependentArrow X' X'}
  (j : ChainCompose F F F)
  (j' : DependentCompose F' F' F')
  (l : ChainLift F)
  : Set

-- #### Definitions

DependentPrelift {n = zero}
  = DependentPrelift₀
DependentPrelift {n = suc _}
  = DependentPrelift''

record DependentPrelift'' {_ X _ F F'} j j' l where

  inductive
  no-eta-equality

  field

    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentPath
        (DependentArrow.tail F' x y)
        (ChainLift.path l f)

    path-compose
      : {x y z : ChainObject.Object X}
      → (f : ChainArrow.Arrow F y z)
      → (g : ChainArrow.Arrow F x y)
      → DependentPathCompose
        (DependentCompose.tail j' x y z)
        (path f)
        (path g)
        (path (ChainCompose.compose j f g))

    tail
      : (x : ChainObject.Object X)
      → DependentPrelift
        (ChainCompose.tail j x x x)
        (DependentCompose.tail j' x x x)
        (ChainLift.tail l x)

module DependentPrelift
  = DependentPrelift''

-- ### DependentPrelift'

-- #### Base

record DependentPrelift₀'
  {X : ChainObject₀}
  {X' : DependentObject X}
  {F : ChainArrow₀ X X}
  (F' : DependentArrow X' X')
  (l : ChainLift₀ F)
  : Set
  where

  constructor

    tt

-- #### Types

DependentPrelift'
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → DependentArrow X' X'
  → ChainLift F
  → Set

record DependentPrelift'''
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' : DependentObject X}
  {F : ChainArrow X X}
  (F' : DependentArrow X' X')
  (l : ChainLift F)
  : Set

-- #### Definitions

DependentPrelift' {n = zero}
  = DependentPrelift₀'
DependentPrelift' {n = suc _}
  = DependentPrelift'''

record DependentPrelift''' {_ X _ F} F' l where

  inductive
  no-eta-equality

  field

    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentPath
        (DependentArrow.tail F' x y)
        (ChainLift.path l f)

    tail
      : (x : ChainObject.Object X)
      → DependentPrelift'
        (DependentArrow.tail F' x x)
        (ChainLift.tail l x)

module DependentPrelift'
  = DependentPrelift'''

-- ### DependentLift

-- #### Base

record DependentLift₀
  {X : ChainObject₀}
  {X' : DependentObject X}
  {F : ChainArrow₀ X X}
  {F' : DependentArrow X' X'}
  (i : ChainIdentity₀ F)
  (i' : DependentIdentity F')
  (j : ChainCompose₀ F F F)
  (j' : DependentCompose F' F' F')
  (l : ChainLift₀ F)
  : Set
  where

  constructor

    tt

-- #### Types

DependentLift
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → ChainIdentity F
  → DependentIdentity F'
  → ChainCompose F F F
  → DependentCompose F' F' F'
  → ChainLift F
  → Set

record DependentLift'
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' : DependentObject X}
  {F : ChainArrow X X}
  {F' : DependentArrow X' X'}
  (i : ChainIdentity F)
  (i' : DependentIdentity F')
  (j : ChainCompose F F F)
  (j' : DependentCompose F' F' F')
  (l : ChainLift F)
  : Set

-- #### Definitions

DependentLift {n = zero}
  = DependentLift₀
DependentLift {n = suc _}
  = DependentLift'

record DependentLift' {_ X _ F F'} i i' j j' l where

  inductive
  no-eta-equality

  field

    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentPath
        (DependentArrow.tail F' x y)
        (ChainLift.path l f)

    path-equal
      : {x y : ChainObject.Object X}
      → {f₁ f₂ : ChainArrow.Arrow F x y}
      → ChainArrow.ArrowEqual F f₁ f₂
      → DependentPathEqual
        (path f₁)
        (path f₂)

    path-identity
      : (x : ChainObject.Object X)
      → DependentPathIdentity
        (DependentIdentity.tail i' x)
        (path (ChainIdentity.identity i x))

    path-compose
      : {x y z : ChainObject.Object X}
      → (f : ChainArrow.Arrow F y z)
      → (g : ChainArrow.Arrow F x y)
      → DependentPathCompose
        (DependentCompose.tail j' x y z)
        (path f)
        (path g)
        (path (ChainCompose.compose j f g))

    tail
      : (x : ChainObject.Object X)
      → DependentLift
        (ChainIdentity.tail i x)
        (DependentIdentity.tail i' x)
        (ChainCompose.tail j x x x)
        (DependentCompose.tail j' x x x)
        (ChainLift.tail l x)

module DependentLift
  = DependentLift'

-- ## Dependent₁

-- ### DependentPath₁

-- #### Definition

DependentPath₁
  : {X Y : Object'}
  → {X' : DependentObject₁ X}
  → {Y' : DependentObject₁ Y}
  → {F : Arrow' X Y}
  → DependentArrow₁ X' Y'
  → Path F
  → Set
DependentPath₁ F' p
  = DependentPath F'
    (chain-path₁ p)

-- #### Module

module DependentPath₁
  {X Y : Object'}
  {X' : DependentObject₁ X}
  {Y' : DependentObject₁ Y}
  {F : Arrow' X Y}
  {F' : DependentArrow₁ X' Y'}
  {p : Path F}
  (p' : DependentPath₁ F' p)
  where

  open DependentPath p' public

  open module Path' {x y} p''
    = Path (tail x {y} p'') public

-- ### DependentPathEqual₁

-- #### Definition

DependentPathEqual₁
  : {X Y : Object'}
  → {X' : DependentObject₁ X}
  → {Y' : DependentObject₁ Y}
  → {F : Arrow' X Y}
  → {F' : DependentArrow₁ X' Y'}
  → {p₁ p₂ : Path F}
  → DependentPath₁ F' p₁
  → DependentPath₁ F' p₂
  → Set
DependentPathEqual₁
  = DependentPathEqual

-- #### Module

module DependentPathEqual₁
  {X Y : Object'}
  {X' : DependentObject₁ X}
  {Y' : DependentObject₁ Y}
  {F : Arrow' X Y}
  {F' : DependentArrow₁ X' Y'}
  {p₁ p₂ : Path F}
  {p₁' : DependentPath₁ F' p₁}
  {p₂' : DependentPath₁ F' p₂}
  (q : DependentPathEqual₁ p₁' p₂')
  where

  open DependentPathEqual q public

  open module PathEqual' {x y} p₁'' p₂''
    = PathEqual (tail x {y} p₁'' p₂'') public

-- ### DependentPathIdentity₁

-- #### Definition

DependentPathIdentity₁
  : {X : Object'}
  → {X' : DependentObject₁ X}
  → {F : Arrow' X X}
  → {F' : DependentArrow₁ X' X'}
  → DependentIdentity₁ F'
  → {p : Path F}
  → DependentPath₁ F' p
  → Set
DependentPathIdentity₁ i
  = DependentPathIdentity i

-- #### Module

module DependentPathIdentity₁
  {X : Object'}
  {X' : DependentObject₁ X}
  {F : Arrow' X X}
  {F' : DependentArrow₁ X' X'}
  {i : DependentIdentity₁ F'}
  {p : Path F}
  {p' : DependentPath₁ F' p}
  (q : DependentPathIdentity₁ i p')
  where

  open DependentPathIdentity q public
  
  open module PathIdentity' {x} p''
    = PathIdentity (tail {x} p'') public

-- ### DependentPathCompose₁

-- #### Definition

DependentPathCompose₁
  : {X Y Z : Object'}
  → {X' : DependentObject₁ X}
  → {Y' : DependentObject₁ Y}
  → {Z' : DependentObject₁ Z}
  → {F : Arrow' Y Z}
  → {G : Arrow' X Y}
  → {H : Arrow' X Z}
  → {F' : DependentArrow₁ Y' Z'}
  → {G' : DependentArrow₁ X' Y'}
  → {H' : DependentArrow₁ X' Z'}
  → DependentCompose₁ F' G' H'
  → {p : Path F}
  → {q : Path G}
  → {r : Path H}
  → DependentPath₁ F' p
  → DependentPath₁ G' q
  → DependentPath₁ H' r
  → Set
DependentPathCompose₁ j
  = DependentPathCompose j

-- #### Module

module DependentPathCompose₁
  {X Y Z : Object'}
  {X' : DependentObject₁ X}
  {Y' : DependentObject₁ Y}
  {Z' : DependentObject₁ Z}
  {F : Arrow' Y Z}
  {G : Arrow' X Y}
  {H : Arrow' X Z}
  {F' : DependentArrow₁ Y' Z'}
  {G' : DependentArrow₁ X' Y'}
  {H' : DependentArrow₁ X' Z'}
  {j : DependentCompose₁ F' G' H'}
  {p : Path F}
  {q : Path G}
  {r : Path H}
  {p' : DependentPath₁ F' p}
  {q' : DependentPath₁ G' q}
  {r' : DependentPath₁ H' r}
  (s : DependentPathCompose₁ j p' q' r')
  where

  open DependentPathCompose s public
  
  open module PathCompose' {x y z} p'' q'' r''
    = PathCompose (tail x {y} {z} p'' q'' r'') public

