module Category.Split.Core where

open import Category.Core
  using (Arrow'; ChainObject; DependentArrow; DependentArrow₁; DependentCompose;
    DependentCompose₁; DependentIdentity; DependentIdentity₁; DependentObject;
    DependentObject₁; Compose; Identity; Object'; object')
open import Data.Bool
  using (Bool)
open import Data.Equal
  using (Equal; _≡_; refl; sub; sym; trans)
open import Data.Function
  using (_∘_)
open import Data.Maybe
  using (Maybe; just)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Retraction
  using (Retraction)

-- ## Base

-- ### SplitBase

-- #### Definition

record SplitBase
  (X X' : Object')
  : Set
  where

  no-eta-equality

  field

    base
      : Object'.Object X
      → Maybe (Object'.Object X')

    unbase
      : Object'.Object X'
      → Object'.Object X

    base-unbase
      : (x : Object'.Object X')
      → base (unbase x) ≡ just x

  bool-function
    : Object'.Object X
    → Bool
  bool-function x
    = Maybe.is-just (base x)

-- #### Conversion

split-base-from-retraction
  : {A B : Set}
  → Retraction A B
  → SplitBase (object' A) (object' B)
split-base-from-retraction F
  = record
  { base
    = just ∘ Retraction.to F
  ; unbase
    = Retraction.from F
  ; base-unbase
    = sub just ∘ Retraction.to-from F
  }

-- ### SplitMap

record SplitMap
  {X Y X' Y' : Object'}
  (F : Arrow' X Y)
  (F' : Arrow' X' Y')
  (a : SplitBase X X')
  (b : SplitBase Y Y')
  : Set
  where

  no-eta-equality

  field

    map
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → {x' : Object'.Object X'}
      → {y' : Object'.Object Y'}
      → SplitBase.base a x ≡ just x'
      → SplitBase.base b y ≡ just y'
      → Arrow'.Arrow F x y
      → Arrow'.Arrow F' x' y'

    map-equal
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → {x' : Object'.Object X'}
      → {y' : Object'.Object Y'}
      → {f₁ f₂ : Arrow'.Arrow F x y}
      → (p : SplitBase.base a x ≡ just x')
      → (q : SplitBase.base b y ≡ just y')
      → Arrow'.ArrowEqual F f₁ f₂
      → Arrow'.ArrowEqual F' (map p q f₁) (map p q f₂)

    unmap
      : {x : Object'.Object X'}
      → {y : Object'.Object Y'}
      → Arrow'.Arrow F' x y
      → Arrow'.Arrow F
        (SplitBase.unbase a x)
        (SplitBase.unbase b y)

    unmap-equal
      : {x : Object'.Object X'}
      → {y : Object'.Object Y'}
      → {f₁ f₂ : Arrow'.Arrow F' x y}
      → Arrow'.ArrowEqual F' f₁ f₂
      → Arrow'.ArrowEqual F (unmap f₁) (unmap f₂)

    map-unmap
      : {x : Object'.Object X'}
      → {y : Object'.Object Y'}
      → (p : SplitBase.base a
        (SplitBase.unbase a x)
        ≡ just x)
      → (q : SplitBase.base b
        (SplitBase.unbase b y)
        ≡ just y)
      → (f : Arrow'.Arrow F' x y)
      → Arrow'.ArrowEqual F' (map p q (unmap f)) f

  map-equal'
    : {x₁ x₂ : Object'.Object X}
    → {y₁ y₂ : Object'.Object Y}
    → {x₁' x₂' : Object'.Object X'}
    → {y₁' y₂' : Object'.Object Y'}
    → {f₁ : Arrow'.Arrow F x₁ y₁}
    → {f₂ : Arrow'.Arrow F x₂ y₂}
    → (p₁ : SplitBase.base a x₁ ≡ just x₁')
    → (p₂ : SplitBase.base a x₂ ≡ just x₂')
    → (q₁ : SplitBase.base b y₁ ≡ just y₁')
    → (q₂ : SplitBase.base b y₂ ≡ just y₂')
    → Arrow'.ArrowEqual' F f₁ f₂
    → Arrow'.ArrowEqual' F' (map p₁ q₁ f₁) (map p₂ q₂ f₂)
  map-equal' p₁ p₂ q₁ q₂ (Arrow'.arrow-equal r)
    with trans (sym p₁) p₂
    | trans (sym q₁) q₂
  ... | refl | refl
    with Equal.irrelevant p₁ p₂
    | Equal.irrelevant q₁ q₂
  ... | refl | refl
    = Arrow'.arrow-equal (map-equal p₁ q₁ r)

  unmap-equal'
    : {x₁ x₂ : Object'.Object X'}
    → {y₁ y₂ : Object'.Object Y'}
    → {f₁ : Arrow'.Arrow F' x₁ y₁}
    → {f₂ : Arrow'.Arrow F' x₂ y₂}
    → Arrow'.ArrowEqual' F' f₁ f₂
    → Arrow'.ArrowEqual' F (unmap f₁) (unmap f₂)
  unmap-equal' (Arrow'.arrow-equal p)
    = Arrow'.arrow-equal (unmap-equal p)

  map-unmap'
    : {x : Object'.Object X'}
    → {y : Object'.Object Y'}
    → (p : SplitBase.base a
      (SplitBase.unbase a x)
      ≡ just x)
    → (q : SplitBase.base b
      (SplitBase.unbase b y)
      ≡ just y)
    → (f : Arrow'.Arrow F' x y)
    → Arrow'.ArrowEqual' F' (map p q (unmap f)) f
  map-unmap' p q f
    = Arrow'.arrow-equal (map-unmap p q f)

-- ### SplitIdentity

record SplitIdentity
  {X X' : Object'}
  {F : Arrow' X X}
  {F' : Arrow' X' X'}
  (i : Identity F)
  (i' : Identity F')
  {a : SplitBase X X'}
  (m : SplitMap F F' a a)
  : Set
  where

  field

    map
      : (x : Object'.Object X)
      → {x' : Object'.Object X'}
      → (p : SplitBase.base a x ≡ just x')
      → Arrow'.ArrowEqual F'
        (SplitMap.map m p p
          (Identity.identity i x))
        (Identity.identity i' x')

    unmap
      : (x : Object'.Object X')
      → Arrow'.ArrowEqual F
        (SplitMap.unmap m
          (Identity.identity i' x))
        (Identity.identity i
          (SplitBase.unbase a x))

    normalize-arrow
      : (x : Object'.Object X)
      → {x' : Object'.Object X'}
      → SplitBase.base a x ≡ just x'
      → Arrow'.Arrow F x
        (SplitBase.unbase a x')

    normalize-valid
      : (x : Object'.Object X)
      → {x' : Object'.Object X'}
      → (p : SplitBase.base a x ≡ just x')
      → (q : SplitBase.base a
        (SplitBase.unbase a x')
        ≡ just x')
      → Arrow'.ArrowEqual F'
        (SplitMap.map m p q (normalize-arrow x p))
        (Identity.identity i' x')

  map'
    : (x : Object'.Object X)
    → {x' : Object'.Object X'}
    → (p : SplitBase.base a x ≡ just x')
    → Arrow'.ArrowEqual' F'
      (SplitMap.map m p p
        (Identity.identity i x))
      (Identity.identity i' x')
  map' x p
    = Arrow'.arrow-equal (map x p)

  unmap'
    : (x : Object'.Object X')
    → Arrow'.ArrowEqual' F
      (SplitMap.unmap m
        (Identity.identity i' x))
      (Identity.identity i
        (SplitBase.unbase a x))
  unmap' x
    = Arrow'.arrow-equal (unmap x)

  normalize-valid'
    : (x : Object'.Object X)
    → {x' x'' : Object'.Object X'}
    → (p : SplitBase.base a x ≡ just x')
    → (p' : SplitBase.base a x ≡ just x'')
    → (q : SplitBase.base a
      (SplitBase.unbase a x')
      ≡ just x')
    → Arrow'.ArrowEqual' F'
      (SplitMap.map m p' q (normalize-arrow x p))
      (Identity.identity i' x')
  normalize-valid' x p p' q
    with trans (sym p) p'
  ... | refl
    with Equal.irrelevant p p'
  ... | refl
    = Arrow'.arrow-equal (normalize-valid x p q)

-- ### SplitCompose

record SplitCompose
  {X Y Z X' Y' Z' : Object'}
  {F : Arrow' Y Z}
  {G : Arrow' X Y}
  {H : Arrow' X Z}
  {F' : Arrow' Y' Z'}
  {G' : Arrow' X' Y'}
  {H' : Arrow' X' Z'}
  (j : Compose F G H)
  (j' : Compose F' G' H')
  {a : SplitBase X X'}
  {b : SplitBase Y Y'}
  {c : SplitBase Z Z'}
  (m : SplitMap F F' b c)
  (n : SplitMap G G' a b)
  (o : SplitMap H H' a c)
  : Set
  where

  field

    map
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → {z : Object'.Object Z}
      → {x' : Object'.Object X'}
      → {y' : Object'.Object Y'}
      → {z' : Object'.Object Z'}
      → (p : SplitBase.base a x ≡ just x')
      → (q : SplitBase.base b y ≡ just y')
      → (r : SplitBase.base c z ≡ just z')
      → (f : Arrow'.Arrow F y z)
      → (g : Arrow'.Arrow G x y)
      → Arrow'.ArrowEqual H'
        (SplitMap.map o p r
          (Compose.compose j f g))
        (Compose.compose j'
          (SplitMap.map m q r f)
          (SplitMap.map n p q g))

    unmap
      : {x : Object'.Object X'}
      → {y : Object'.Object Y'}
      → {z : Object'.Object Z'}
      → (f : Arrow'.Arrow F' y z)
      → (g : Arrow'.Arrow G' x y)
      → Arrow'.ArrowEqual H
        (SplitMap.unmap o
          (Compose.compose j' f g))
        (Compose.compose j
          (SplitMap.unmap m f)
          (SplitMap.unmap n g))

  unmap'
    : {x : Object'.Object X'}
    → {y : Object'.Object Y'}
    → {z : Object'.Object Z'}
    → (f : Arrow'.Arrow F' y z)
    → (g : Arrow'.Arrow G' x y)
    → Arrow'.ArrowEqual' H
      (SplitMap.unmap o
        (Compose.compose j' f g))
      (Compose.compose j
        (SplitMap.unmap m f)
        (SplitMap.unmap n g))
  unmap' f g
    = Arrow'.arrow-equal (unmap f g)

-- ## Dependent

-- ### DependentSplitBase

-- #### Types

DependentSplitBase
  : {n : ℕ}
  → {X : ChainObject n}
  → DependentObject X
  → DependentObject X
  → Set

record DependentSplitBase'
  {n : ℕ}
  {X : ChainObject (suc n)}
  (X' X'' : DependentObject X)
  : Set

-- #### Definitions

DependentSplitBase {n = zero}
  = SplitBase
DependentSplitBase {n = suc _}
  = DependentSplitBase'

record DependentSplitBase' {_ X} X' X'' where

  inductive
  no-eta-equality

  field

    tail
      : (x : ChainObject.Object X)
      → DependentSplitBase
        (DependentObject.tail X' x)
        (DependentObject.tail X'' x)

module DependentSplitBase
  = DependentSplitBase'

-- ### DependentSplitMap

-- #### Types

DependentSplitMap
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → DependentArrow X' Y'
  → DependentArrow X'' Y''
  → DependentSplitBase X' X''
  → DependentSplitBase Y' Y''
  → Set

record DependentSplitMap'
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {Y' Y'' : DependentObject Y}
  (F : DependentArrow X' Y')
  (F' : DependentArrow X'' Y'')
  (a : DependentSplitBase X' X'')
  (b : DependentSplitBase Y' Y'')
  : Set

-- #### Definitions

DependentSplitMap {n = zero}
  = SplitMap
DependentSplitMap {n = suc _}
  = DependentSplitMap'

record DependentSplitMap' {_ X Y} F F' a b where

  inductive
  no-eta-equality

  field

    tail
      : (x : ChainObject.Object X)
      → (y : ChainObject.Object Y)
      → DependentSplitMap
        (DependentArrow.tail F x y)
        (DependentArrow.tail F' x y)
        (DependentSplitBase.tail a x)
        (DependentSplitBase.tail b y)

module DependentSplitMap
  = DependentSplitMap'

-- ### DependentSplitIdentity

-- #### Types

DependentSplitIdentity
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : DependentArrow X' X'}
  → {F' : DependentArrow X'' X''}
  → DependentIdentity F
  → DependentIdentity F'
  → {a : DependentSplitBase X' X''}
  → DependentSplitMap F F' a a
  → Set

record DependentSplitIdentity'
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {F : DependentArrow X' X'}
  {F' : DependentArrow X'' X''}
  (i : DependentIdentity F)
  (i' : DependentIdentity F')
  {a : DependentSplitBase X' X''}
  (m : DependentSplitMap F F' a a)
  : Set

-- #### Definitions

DependentSplitIdentity {n = zero}
  = SplitIdentity
DependentSplitIdentity {n = suc _}
  = DependentSplitIdentity'

record DependentSplitIdentity' {_ X} i i' m where

  inductive

  field

    tail
      : (x : ChainObject.Object X)
      → DependentSplitIdentity
        (DependentIdentity.tail i x)
        (DependentIdentity.tail i' x)
        (DependentSplitMap.tail m x x)

module DependentSplitIdentity
  = DependentSplitIdentity'

-- ### DependentSplitCompose

-- #### Types

DependentSplitCompose
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {Z' Z'' : DependentObject Z}
  → {F : DependentArrow Y' Z'}
  → {G : DependentArrow X' Y'}
  → {H : DependentArrow X' Z'}
  → {F' : DependentArrow Y'' Z''}
  → {G' : DependentArrow X'' Y''}
  → {H' : DependentArrow X'' Z''}
  → DependentCompose F G H
  → DependentCompose F' G' H'
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → {c : DependentSplitBase Z' Z''}
  → DependentSplitMap F F' b c
  → DependentSplitMap G G' a b
  → DependentSplitMap H H' a c
  → Set

record DependentSplitCompose'
  {n : ℕ}
  {X Y Z : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {Y' Y'' : DependentObject Y}
  {Z' Z'' : DependentObject Z}
  {F : DependentArrow Y' Z'}
  {G : DependentArrow X' Y'}
  {H : DependentArrow X' Z'}
  {F' : DependentArrow Y'' Z''}
  {G' : DependentArrow X'' Y''}
  {H' : DependentArrow X'' Z''}
  (j : DependentCompose F G H)
  (j' : DependentCompose F' G' H')
  {a : DependentSplitBase X' X''}
  {b : DependentSplitBase Y' Y''}
  {c : DependentSplitBase Z' Z''}
  (m : DependentSplitMap F F' b c)
  (n : DependentSplitMap G G' a b)
  (o : DependentSplitMap H H' a c)
  : Set

-- #### Definitions

DependentSplitCompose {n = zero}
  = SplitCompose
DependentSplitCompose {n = suc _}
  = DependentSplitCompose'

record DependentSplitCompose' {_ X Y Z} j j' m n o where

  inductive

  field
  
    tail
      : (x : ChainObject.Object X)
      → (y : ChainObject.Object Y)
      → (z : ChainObject.Object Z)
      → DependentSplitCompose
        (DependentCompose.tail j x y z)
        (DependentCompose.tail j' x y z)
        (DependentSplitMap.tail m y z)
        (DependentSplitMap.tail n x y)
        (DependentSplitMap.tail o x z)

module DependentSplitCompose
  = DependentSplitCompose'

-- ## Dependent₁

-- ### DependentSplitBase₁

-- #### Definition

DependentSplitBase₁
  : {X : Object'}
  → DependentObject₁ X
  → DependentObject₁ X
  → Set
DependentSplitBase₁
  = DependentSplitBase

-- #### Module

module DependentSplitBase₁
  {X : Object'}
  {X' X'' : DependentObject₁ X}
  (a : DependentSplitBase₁ X' X'')
  where

  open DependentSplitBase a public

  open module SplitBase' {x}
    = SplitBase (tail x) public

-- ### DependentSplitMap₁

-- #### Definition

DependentSplitMap₁
  : {X Y : Object'}
  → {X' X'' : DependentObject₁ X}
  → {Y' Y'' : DependentObject₁ Y}
  → DependentArrow₁ X' Y'
  → DependentArrow₁ X'' Y''
  → DependentSplitBase₁ X' X''
  → DependentSplitBase₁ Y' Y''
  → Set
DependentSplitMap₁
  = DependentSplitMap

-- #### Module

module DependentSplitMap₁
  {X Y : Object'}
  {X' X'' : DependentObject₁ X}
  {Y' Y'' : DependentObject₁ Y}
  {F : DependentArrow₁ X' Y'}
  {F' : DependentArrow₁ X'' Y''}
  {a : DependentSplitBase₁ X' X''}
  {b : DependentSplitBase₁ Y' Y''}
  (m : DependentSplitMap₁ F F' a b)
  where

  open DependentSplitMap m public

  open module SplitMap' {x y}
    = SplitMap (tail x y) public

-- ### DependentSplitIdentity₁

-- #### Definition

DependentSplitIdentity₁
  : {X : Object'}
  → {X' X'' : DependentObject₁ X}
  → {F : DependentArrow₁ X' X'}
  → {F' : DependentArrow₁ X'' X''}
  → DependentIdentity₁ F
  → DependentIdentity₁ F'
  → {a : DependentSplitBase₁ X' X''}
  → DependentSplitMap₁ F F' a a
  → Set
DependentSplitIdentity₁
  = DependentSplitIdentity

-- #### Module

module DependentSplitIdentity₁
  {X : Object'}
  {X' X'' : DependentObject₁ X}
  {F : DependentArrow₁ X' X'}
  {F' : DependentArrow₁ X'' X''}
  {i : DependentIdentity₁ F}
  {i' : DependentIdentity₁ F'}
  {a : DependentSplitBase₁ X' X''}
  {m : DependentSplitMap₁ F F' a a}
  (p : DependentSplitIdentity₁ i i' m)
  where

  open DependentSplitIdentity p public

  open module SplitIdentity' {x}
    = SplitIdentity (tail x) public

-- ### DependentSplitCompose₁

-- #### Definition

DependentSplitCompose₁
  : {X Y Z : Object'}
  → {X' X'' : DependentObject₁ X}
  → {Y' Y'' : DependentObject₁ Y}
  → {Z' Z'' : DependentObject₁ Z}
  → {F : DependentArrow₁ Y' Z'}
  → {G : DependentArrow₁ X' Y'}
  → {H : DependentArrow₁ X' Z'}
  → {F' : DependentArrow₁ Y'' Z''}
  → {G' : DependentArrow₁ X'' Y''}
  → {H' : DependentArrow₁ X'' Z''}
  → DependentCompose₁ F G H
  → DependentCompose₁ F' G' H'
  → {a : DependentSplitBase₁ X' X''}
  → {b : DependentSplitBase₁ Y' Y''}
  → {c : DependentSplitBase₁ Z' Z''}
  → DependentSplitMap₁ F F' b c
  → DependentSplitMap₁ G G' a b
  → DependentSplitMap₁ H H' a c
  → Set
DependentSplitCompose₁
  = DependentSplitCompose

-- #### Module

module DependentSplitCompose₁
  {X Y Z : Object'}
  {X' X'' : DependentObject₁ X}
  {Y' Y'' : DependentObject₁ Y}
  {Z' Z'' : DependentObject₁ Z}
  {F : DependentArrow₁ Y' Z'}
  {G : DependentArrow₁ X' Y'}
  {H : DependentArrow₁ X' Z'}
  {F' : DependentArrow₁ Y'' Z''}
  {G' : DependentArrow₁ X'' Y''}
  {H' : DependentArrow₁ X'' Z''}
  {j : DependentCompose₁ F G H}
  {j' : DependentCompose₁ F' G' H'}
  {a : DependentSplitBase₁ X' X''}
  {b : DependentSplitBase₁ Y' Y''}
  {c : DependentSplitBase₁ Z' Z''}
  {m : DependentSplitMap₁ F F' b c}
  {n : DependentSplitMap₁ G G' a b}
  {o : DependentSplitMap₁ H H' a c}
  (p : DependentSplitCompose₁ j j' m n o)
  where

  open DependentSplitCompose p public

  open module SplitCompose' {x y z}
    = SplitCompose (tail x y z) public

