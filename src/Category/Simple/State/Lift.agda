module Category.Simple.State.Lift where

open import Category.Core
  using (Arrow'; ChainArrow; ChainArrow₀; ChainIdentity; ChainIdentity₀;
    ChainObject; ChainObject₀; DependentArrow; DependentIdentity;
    DependentObject; Identity; Object')
open import Category.Lift
  using (ChainLift; ChainLift₀; ChainPath)
open import Category.State.Lift
  using (DependentStateLift; DependentStatePath; DependentStatePathEqual;
    DependentStatePathIdentity; StatePath; StatePathEqual; StatePathIdentity)
open import Data.Equal
  using (_≡_)
open import Data.Maybe
  using (just)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### SimpleStatePath

-- #### Definition

record SimpleStatePath
  (X Y : Object')
  : Set
  where

  no-eta-equality

  field

    base
      : Object'.Object X
      → Object'.Object Y

-- #### Conversion

state-path-simple
  : {X Y : Object'}
  → {F : Arrow' X Y}
  → StatePath F
  → SimpleStatePath X Y
state-path-simple p
  = record {StatePath p}

-- ### SimpleStatePathEqual

-- #### Definition

record SimpleStatePathEqual
  {X Y : Object'}
  (p₁ p₂ : SimpleStatePath X Y)
  : Set
  where

  field

    base
      : (x : Object'.Object X)
      → SimpleStatePath.base p₁ x
        ≡ SimpleStatePath.base p₂ x

-- #### Conversion

state-path-equal-simple
  : {X Y : Object'}
  → {F : Arrow' X Y}
  → {p₁ p₂ : StatePath F}
  → StatePathEqual p₁ p₂
  → SimpleStatePathEqual
    (state-path-simple p₁)
    (state-path-simple p₂)
state-path-equal-simple q
  = record {StatePathEqual q}

-- ### SimpleStatePathIdentity

-- #### Definition

record SimpleStatePathIdentity
  {X : Object'}
  (p : SimpleStatePath X X)
  : Set
  where

  field

    base
      : (x : Object'.Object X)
      → SimpleStatePath.base p x ≡ x

-- #### Conversion

state-path-identity-simple
  : {X : Object'}
  → {F : Arrow' X X}
  → {i : Identity F}
  → {p : StatePath F}
  → StatePathIdentity i p
  → SimpleStatePathIdentity
    (state-path-simple p)
state-path-identity-simple q
  = record {StatePathIdentity q}

-- ## Dependent

-- ### DependentSimpleStatePath

-- #### Types

DependentSimpleStatePath
  : {n : ℕ}
  → {X Y : ChainObject n}
  → DependentObject X
  → DependentObject Y
  → {F : ChainArrow X Y}
  → ChainPath F
  → Set

record DependentSimpleStatePath'
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  (X' : DependentObject X)
  (Y' : DependentObject Y)
  {F : ChainArrow X Y}
  (p : ChainPath F)
  : Set

-- #### Definitions

DependentSimpleStatePath {n = zero} X' Y' _
  = SimpleStatePath X' Y'
DependentSimpleStatePath {n = suc _} X' Y' p
  = DependentSimpleStatePath' X' Y' p

record DependentSimpleStatePath' {_ X Y} X' Y' p where

  inductive
  no-eta-equality

  field
  
    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → (p' : ChainPath.base p x ≡ just y)
      → DependentSimpleStatePath
        (DependentObject.tail X' x)
        (DependentObject.tail Y' y)
        (ChainPath.tail p x p')

module DependentSimpleStatePath
  = DependentSimpleStatePath'

-- #### Conversion

dependent-state-path-simple
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {p : ChainPath F}
  → DependentStatePath F' p
  → DependentSimpleStatePath X' Y' p
dependent-state-path-simple {n = zero} p'
  = state-path-simple p'
dependent-state-path-simple {n = suc _} p'
  = record
  { tail
    = λ x p'' → dependent-state-path-simple
      (DependentStatePath.tail p' x p'')
  }

-- ### DependentSimpleStatePathEqual

-- #### Types

DependentSimpleStatePathEqual
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {p₁ p₂ : ChainPath F}
  → DependentSimpleStatePath X' Y' p₁
  → DependentSimpleStatePath X' Y' p₂
  → Set

record DependentSimpleStatePathEqual'
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  {X' : DependentObject X}
  {Y' : DependentObject Y}
  {F : ChainArrow X Y}
  {p₁ p₂ : ChainPath F}
  (p₁' : DependentSimpleStatePath X' Y' p₁)
  (p₂' : DependentSimpleStatePath X' Y' p₂)
  : Set

-- #### Definitions

DependentSimpleStatePathEqual {n = zero}
  = SimpleStatePathEqual
DependentSimpleStatePathEqual {n = suc _}
  = DependentSimpleStatePathEqual'

record DependentSimpleStatePathEqual' {_ X Y _ _ _ p₁ p₂} p₁' p₂' where

  inductive

  field
  
    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → (p₁'' : ChainPath.base p₁ x ≡ just y)
      → (p₂'' : ChainPath.base p₂ x ≡ just y)
      → DependentSimpleStatePathEqual
        (DependentSimpleStatePath.tail p₁' x p₁'')
        (DependentSimpleStatePath.tail p₂' x p₂'')

module DependentSimpleStatePathEqual
  = DependentSimpleStatePathEqual'

-- #### Conversion

dependent-state-path-equal-simple
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {p₁ p₂ : ChainPath F}
  → {p₁' : DependentStatePath F' p₁}
  → {p₂' : DependentStatePath F' p₂}
  → DependentStatePathEqual p₁' p₂'
  → DependentSimpleStatePathEqual
    (dependent-state-path-simple p₁')
    (dependent-state-path-simple p₂')
dependent-state-path-equal-simple {n = zero} q
  = state-path-equal-simple q
dependent-state-path-equal-simple {n = suc _} q
  = record
  { tail
    = λ x p₁'' p₂'' → dependent-state-path-equal-simple
      (DependentStatePathEqual.tail q x p₁'' p₂'')
  }

-- ### DependentSimpleStatePathIdentity

-- #### Types

DependentSimpleStatePathIdentity
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {p : ChainPath F}
  → DependentSimpleStatePath X' X' p
  → Set

record DependentSimpleStatePathIdentity'
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' : DependentObject X}
  {F : ChainArrow X X}
  {p : ChainPath F}
  (p' : DependentSimpleStatePath X' X' p)
  : Set

-- #### Definitions

DependentSimpleStatePathIdentity {n = zero}
  = SimpleStatePathIdentity
DependentSimpleStatePathIdentity {n = suc _}
  = DependentSimpleStatePathIdentity'

record DependentSimpleStatePathIdentity' {_ X _ _ p} p' where

  inductive

  field

    tail
      : {x : ChainObject.Object X}
      → (p'' : ChainPath.base p x ≡ just x)
      → DependentSimpleStatePathIdentity
        (DependentSimpleStatePath.tail p' x p'')

module DependentSimpleStatePathIdentity
  = DependentSimpleStatePathIdentity'

-- #### Conversion

dependent-state-path-identity-simple
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {i : DependentIdentity F'}
  → {p : ChainPath F}
  → {p' : DependentStatePath F' p}
  → DependentStatePathIdentity i p'
  → DependentSimpleStatePathIdentity
    (dependent-state-path-simple p')
dependent-state-path-identity-simple {n = zero} q
  = state-path-identity-simple q
dependent-state-path-identity-simple {n = suc _} q
  = record
  { tail
    = λ p'' → dependent-state-path-identity-simple
      (DependentStatePathIdentity.tail q p'')
  }

-- ### DependentSimpleStateLift

-- #### Base

record DependentSimpleStateLift₀
  {X : ChainObject₀}
  (X' : DependentObject X)
  {F : ChainArrow₀ X X}
  (i : ChainIdentity₀ F)
  (l : ChainLift₀ F)
  : Set₁
  where

  constructor
  
    tt

-- #### Types

DependentSimpleStateLift
  : {n : ℕ}
  → {X : ChainObject n}
  → DependentObject X
  → {F : ChainArrow X X}
  → ChainIdentity F
  → ChainLift F
  → Set₁

record DependentSimpleStateLift'
  {n : ℕ}
  {X : ChainObject (suc n)}
  (X' : DependentObject X)
  {F : ChainArrow X X}
  (i : ChainIdentity F)
  (l : ChainLift F)
  : Set₁

-- #### Definitions

DependentSimpleStateLift {n = zero}
  = DependentSimpleStateLift₀
DependentSimpleStateLift {n = suc _}
  = DependentSimpleStateLift'

record DependentSimpleStateLift' {_ X} X' {F} i l where

  inductive
  no-eta-equality

  field

    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentSimpleStatePath
        (DependentObject.tail X' x)
        (DependentObject.tail X' y)
        (ChainLift.path l f)

    path-equal
      : {x y : ChainObject.Object X}
      → {f₁ f₂ : ChainArrow.Arrow F x y}
      → ChainArrow.ArrowEqual F f₁ f₂
      → DependentSimpleStatePathEqual
        (path f₁)
        (path f₂)

    path-identity
      : (x : ChainObject.Object X)
      → DependentSimpleStatePathIdentity
        (path (ChainIdentity.identity i x))

    tail
      : (x : ChainObject.Object X)
      → DependentSimpleStateLift
        (DependentObject.tail X' x)
        (ChainIdentity.tail i x)
        (ChainLift.tail l x)

module DependentSimpleStateLift
  = DependentSimpleStateLift'

-- #### Conversion

dependent-state-lift-simple
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {i : ChainIdentity F}
  → {i' : DependentIdentity F'}
  → {l : ChainLift F}
  → DependentStateLift i i' l
  → DependentSimpleStateLift X' i l
dependent-state-lift-simple {n = zero} _
  = tt
dependent-state-lift-simple {n = suc _} l
  = record
  { path
    = λ f → dependent-state-path-simple
      (DependentStateLift.path l f)
  ; path-equal
    = λ p → dependent-state-path-equal-simple
      (DependentStateLift.path-equal l p)
  ; path-identity
    = λ x → dependent-state-path-identity-simple
      (DependentStateLift.path-identity l x)
  ; tail
    = λ x → dependent-state-lift-simple
      (DependentStateLift.tail l x)
  }

