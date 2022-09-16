module Category.State.Lift where

open import Category.Core
  using (Arrow'; ChainArrow; ChainArrow₀; ChainIdentity; ChainIdentity₀;
    ChainObject; ChainObject₀; DependentArrow₁; DependentArrow;
    DependentIdentity; DependentIdentity₁; DependentObject; DependentObject₁;
    Identity; Object'; chain-identity₁)
open import Category.Lift
  using (ChainLift; ChainLift₀; ChainPath; Path; chain-lift₁; chain-path₁)
open import Data.Equal
  using (_≡_; refl)
open import Data.Maybe
  using (just)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### StatePath

record StatePath
  {X Y : Object'}
  (F : Arrow' X Y)
  : Set
  where

  no-eta-equality

  field

    base
      : Object'.Object X
      → Object'.Object Y

    map
      : (x : Object'.Object X)
      → Arrow'.Arrow F x (base x)

  map-equal
    : {x₁ x₂ : Object'.Object X}
    → x₁ ≡ x₂
    → Arrow'.ArrowEqual' F (map x₁) (map x₂)
  map-equal refl
    = Arrow'.arrow-refl' F

-- ### StatePathEqual

record StatePathEqual
  {X Y : Object'}
  {F : Arrow' X Y}
  (p₁ p₂ : StatePath F)
  : Set
  where

  field

    map
      : (x : Object'.Object X)
      → Arrow'.ArrowEqual' F
        (StatePath.map p₁ x)
        (StatePath.map p₂ x)

  base
    : (x : Object'.Object X)
    → StatePath.base p₁ x
      ≡ StatePath.base p₂ x
  base x
    = Arrow'.arrow-codomain F (map x)

-- ### StatePathIdentity

record StatePathIdentity
  {X : Object'}
  {F : Arrow' X X}
  (i : Identity F)
  (p : StatePath F)
  : Set
  where

  field

    map
      : (x : Object'.Object X)
      → Arrow'.ArrowEqual' F
        (StatePath.map p x)
        (Identity.identity i x)

  base
    : (x : Object'.Object X)
    → StatePath.base p x ≡ x
  base x
    = Arrow'.arrow-codomain F (map x)

-- ## Dependent

-- ### DependentStatePath

-- #### Types

DependentStatePath
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → DependentArrow X' Y'
  → ChainPath F
  → Set

record DependentStatePath'
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  {X' : DependentObject X}
  {Y' : DependentObject Y}
  {F : ChainArrow X Y}
  (F' : DependentArrow X' Y')
  (p : ChainPath F)
  : Set

-- #### Definitions

DependentStatePath {n = zero} F' _
  = StatePath F'
DependentStatePath {n = suc _} F' p
  = DependentStatePath' F' p

record DependentStatePath' {_ X Y} F' p where

  inductive
  no-eta-equality

  field

    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → (p' : ChainPath.base p x ≡ just y)
      → DependentStatePath
        (DependentArrow.tail F' x y)
        (ChainPath.tail p x p')

module DependentStatePath
  = DependentStatePath'

-- ### DependentStatePathEqual

-- #### Types

DependentStatePathEqual
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {p₁ p₂ : ChainPath F}
  → DependentStatePath F' p₁
  → DependentStatePath F' p₂
  → Set

record DependentStatePathEqual'
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  {X' : DependentObject X}
  {Y' : DependentObject Y}
  {F : ChainArrow X Y}
  {F' : DependentArrow X' Y'}
  {p₁ p₂ : ChainPath F}
  (p₁' : DependentStatePath F' p₁)
  (p₂' : DependentStatePath F' p₂)
  : Set

-- #### Definitions

DependentStatePathEqual {n = zero}
  = StatePathEqual
DependentStatePathEqual {n = suc _}
  = DependentStatePathEqual'

record DependentStatePathEqual' {_ X Y _ _ _ _ p₁ p₂} p₁' p₂' where

  inductive

  field

    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → (p₁'' : ChainPath.base p₁ x ≡ just y)
      → (p₂'' : ChainPath.base p₂ x ≡ just y)
      → DependentStatePathEqual
        (DependentStatePath.tail p₁' x p₁'')
        (DependentStatePath.tail p₂' x p₂'')

module DependentStatePathEqual
  = DependentStatePathEqual'

-- ### DependentStatePathIdentity

-- #### Types

DependentStatePathIdentity
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → DependentIdentity F'
  → {p : ChainPath F}
  → DependentStatePath F' p
  → Set

record DependentStatePathIdentity'
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' : DependentObject X}
  {F : ChainArrow X X}
  {F' : DependentArrow X' X'}
  (i : DependentIdentity F')
  {p : ChainPath F}
  (p' : DependentStatePath F' p)
  : Set

-- #### Definitions

DependentStatePathIdentity {n = zero} i p'
  = StatePathIdentity i p'
DependentStatePathIdentity {n = suc _} i p'
  = DependentStatePathIdentity' i p'

record DependentStatePathIdentity' {_ X} i {p} p' where

  inductive

  field

    tail
      : {x : ChainObject.Object X}
      → (p'' : ChainPath.base p x ≡ just x)
      → DependentStatePathIdentity
        (DependentIdentity.tail i x)
        (DependentStatePath.tail p' x p'')

module DependentStatePathIdentity
  = DependentStatePathIdentity'

-- ### DependentStateLift

-- #### Base

record DependentStateLift₀
  {X : ChainObject₀}
  {X' : DependentObject X}
  {F : ChainArrow₀ X X}
  {F' : DependentArrow X' X'}
  (i : ChainIdentity₀ F)
  (i' : DependentIdentity F')
  (l : ChainLift₀ F)
  : Set₁
  where

  constructor

    tt

-- #### Types

DependentStateLift
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → ChainIdentity F
  → DependentIdentity F'
  → ChainLift F
  → Set₁

record DependentStateLift'
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' : DependentObject X}
  {F : ChainArrow X X}
  {F' : DependentArrow X' X'}
  (i : ChainIdentity F)
  (i' : DependentIdentity F')
  (l : ChainLift F)
  : Set₁

-- #### Definitions

DependentStateLift {n = zero}
  = DependentStateLift₀
DependentStateLift {n = suc _}
  = DependentStateLift'

record DependentStateLift' {_ X _ F F'} i i' l where

  inductive
  no-eta-equality

  field

    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentStatePath
        (DependentArrow.tail F' x y)
        (ChainLift.path l f)

    path-equal
      : {x y : ChainObject.Object X}
      → {f₁ f₂ : ChainArrow.Arrow F x y}
      → ChainArrow.ArrowEqual F f₁ f₂
      → DependentStatePathEqual
        (path f₁)
        (path f₂)

    path-identity
      : (x : ChainObject.Object X)
      → DependentStatePathIdentity
        (DependentIdentity.tail i' x)
        (path (ChainIdentity.identity i x))

    tail
      : (x : ChainObject.Object X)
      → DependentStateLift
        (ChainIdentity.tail i x)
        (DependentIdentity.tail i' x)
        (ChainLift.tail l x)

module DependentStateLift
  = DependentStateLift'

-- ## Dependent₁

-- ### DependentStatePath₁

-- #### Definition

DependentStatePath₁
  : {X Y : Object'}
  → {X' : DependentObject₁ X}
  → {Y' : DependentObject₁ Y}
  → {F : Arrow' X Y}
  → DependentArrow₁ X' Y'
  → Path F
  → Set
DependentStatePath₁ F' p
  = DependentStatePath F'
    (chain-path₁ p)

-- #### Module

module DependentStatePath₁
  {X Y : Object'}
  {X' : DependentObject₁ X}
  {Y' : DependentObject₁ Y}
  {F : Arrow' X Y}
  {F' : DependentArrow₁ X' Y'}
  {p : Path F}
  (p' : DependentStatePath₁ F' p)
  where

  open DependentStatePath p' public

  open module StatePath' {x y} p''
    = StatePath (tail x {y} p'') public

-- ### DependentStatePathEqual₁

-- #### Definition

DependentStatePathEqual₁
  : {X Y : Object'}
  → {X' : DependentObject₁ X}
  → {Y' : DependentObject₁ Y}
  → {F : Arrow' X Y}
  → {F' : DependentArrow₁ X' Y'}
  → {p₁ p₂ : Path F}
  → DependentStatePath₁ F' p₁
  → DependentStatePath₁ F' p₂
  → Set
DependentStatePathEqual₁
  = DependentStatePathEqual

-- #### Module

module DependentStatePathEqual₁
  {X Y : Object'}
  {X' : DependentObject₁ X}
  {Y' : DependentObject₁ Y}
  {F : Arrow' X Y}
  {F' : DependentArrow₁ X' Y'}
  {p₁ p₂ : Path F}
  {p₁' : DependentStatePath₁ F' p₁}
  {p₂' : DependentStatePath₁ F' p₂}
  (q : DependentStatePathEqual₁ p₁' p₂')
  where

  open DependentStatePathEqual q public

  open module StatePathEqual' {x y} p₁'' p₂''
    = StatePathEqual (tail x {y} p₁'' p₂'') public

-- ### DependentStatePathIdentity₁

-- #### Definition

DependentStatePathIdentity₁
  : {X : Object'}
  → {X' : DependentObject₁ X}
  → {F : Arrow' X X}
  → {F' : DependentArrow₁ X' X'}
  → DependentIdentity₁ F'
  → {p : Path F}
  → DependentStatePath₁ F' p
  → Set
DependentStatePathIdentity₁ i
  = DependentStatePathIdentity i

-- #### Module

module DependentStatePathIdentity₁
  {X : Object'}
  {X' : DependentObject₁ X}
  {F : Arrow' X X}
  {F' : DependentArrow₁ X' X'}
  {i : DependentIdentity₁ F'}
  {p : Path F}
  {p' : DependentStatePath₁ F' p}
  (q : DependentStatePathIdentity₁ i p')
  where

  open DependentStatePathIdentity q public
  
  open module StatePathIdentity' {x} p''
    = StatePathIdentity (tail {x} p'') public

-- ### DependentStateLift₁

-- #### Definition

DependentStateLift₁
  : {X : Object'}
  → {X' : DependentObject₁ X}
  → {F : Arrow' X X}
  → {F' : DependentArrow₁ X' X'}
  → Identity F
  → DependentIdentity₁ F'
  → Set₁
DependentStateLift₁ {F = F} i i'
  = DependentStateLift
    (chain-identity₁ i) i'
    (chain-lift₁ F)

-- #### Module

module DependentStateLift₁
  {X : Object'}
  {X' : DependentObject₁ X}
  {F : Arrow' X X}
  {F' : DependentArrow₁ X' X'}
  {i : Identity F}
  {i' : DependentIdentity₁ F'}
  (l : DependentStateLift₁ i i')
  where

  open DependentStateLift l public
  
  open module StatePath' {x y} f
    = StatePath (path {x} {y} f) public

