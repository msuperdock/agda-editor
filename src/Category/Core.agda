module Category.Core where

open import Data.Equal
  using (_≡_; refl)
open import Data.Function
  using (id)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### Object'

record Object'
  : Set₁
  where

  constructor

    object'

  field

    Object
      : Set

-- ### Arrow'

record Arrow'
  (X Y : Object')
  : Set₁
  where

  no-eta-equality

  field

    Arrow
      : Object'.Object X
      → Object'.Object Y
      → Set

    ArrowEqual
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → Arrow x y
      → Arrow x y
      → Set

    arrow-refl
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → {f : Arrow x y}
      → ArrowEqual f f

    arrow-sym
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → {f₁ f₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₁

    arrow-trans
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → {f₁ f₂ f₃ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₃
      → ArrowEqual f₁ f₃
    
  arrow
    : {x₁ x₂ : Object'.Object X}
    → {y₁ y₂ : Object'.Object Y}
    → x₁ ≡ x₂
    → y₁ ≡ y₂
    → Arrow x₂ y₂
    → Arrow x₁ y₁
  arrow refl refl
    = id

  data ArrowEqual'
    : {x₁ x₂ : Object'.Object X}
    → {y₁ y₂ : Object'.Object Y}
    → Arrow x₁ y₁
    → Arrow x₂ y₂
    → Set
    where

    arrow-equal
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → {f₁ f₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual' f₁ f₂

  arrow-equal'
    : {x : Object'.Object X}
    → {y : Object'.Object Y}
    → {f₁ f₂ : Arrow x y}
    → ArrowEqual' f₁ f₂
    → ArrowEqual f₁ f₂
  arrow-equal' (arrow-equal p)
    = p

  arrow-equal''
    : {x₁ x₂ : Object'.Object X}
    → {y₁ y₂ : Object'.Object Y}
    → (p : x₁ ≡ x₂)
    → (q : y₁ ≡ y₂)
    → {f₁₂ f₂₂ : Arrow x₂ y₂}
    → ArrowEqual f₁₂ f₂₂
    → ArrowEqual (arrow p q f₁₂) (arrow p q f₂₂)
  arrow-equal'' refl refl
    = id

  arrow-refl'
    : {x : Object'.Object X}
    → {y : Object'.Object Y}
    → {f : Arrow x y}
    → ArrowEqual' f f
  arrow-refl'
    = arrow-equal arrow-refl

  arrow-refl''
    : {x₁ x₂ : Object'.Object X}
    → {y₁ y₂ : Object'.Object Y}
    → (p : x₁ ≡ x₂)
    → (q : y₁ ≡ y₂)
    → {f₂ : Arrow x₂ y₂}
    → ArrowEqual' (arrow p q f₂) f₂
  arrow-refl'' refl refl
    = arrow-refl'

  arrow-sym'
    : {x₁ x₂ : Object'.Object X}
    → {y₁ y₂ : Object'.Object Y}
    → {f₁ : Arrow x₁ y₁}
    → {f₂ : Arrow x₂ y₂}
    → ArrowEqual' f₁ f₂
    → ArrowEqual' f₂ f₁
  arrow-sym' (arrow-equal p)
    = arrow-equal (arrow-sym p)

  arrow-trans'
    : {x₁ x₂ x₃ : Object'.Object X}
    → {y₁ y₂ y₃ : Object'.Object Y}
    → {f₁ : Arrow x₁ y₁}
    → {f₂ : Arrow x₂ y₂}
    → {f₃ : Arrow x₃ y₃}
    → ArrowEqual' f₁ f₂
    → ArrowEqual' f₂ f₃
    → ArrowEqual' f₁ f₃
  arrow-trans' (arrow-equal p₁) (arrow-equal p₂)
    = arrow-equal (arrow-trans p₁ p₂)

  arrow-codomain
    : {x₁ x₂ : Object'.Object X}
    → {y₁ y₂ : Object'.Object Y}
    → {f₁ : Arrow x₁ y₁}
    → {f₂ : Arrow x₂ y₂}
    → ArrowEqual' f₁ f₂
    → y₁ ≡ y₂
  arrow-codomain (arrow-equal _)
    = refl

-- ### Simplify

record Simplify
  {X Y : Object'}
  (F : Arrow' X Y)
  : Set
  where

  field

    simplify
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → Arrow'.Arrow F x y
      → Arrow'.Arrow F x y

    simplify-equal
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → (f : Arrow'.Arrow F x y)
      → Arrow'.ArrowEqual F (simplify f) f

-- ### Identity

record Identity
  {X : Object'}
  (F : Arrow' X X)
  : Set
  where

  no-eta-equality

  field

    identity
      : (x : Object'.Object X)
      → Arrow'.Arrow F x x

  identity-equal
    : {x₁ x₂ : Object'.Object X}
    → x₁ ≡ x₂
    → Arrow'.ArrowEqual' F (identity x₁) (identity x₂)
  identity-equal refl
    = Arrow'.arrow-refl' F

-- ### Compose

record Compose
  {X Y Z : Object'}
  (F : Arrow' Y Z)
  (G : Arrow' X Y)
  (H : Arrow' X Z)
  : Set
  where

  no-eta-equality

  field

    compose
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → {z : Object'.Object Z}
      → Arrow'.Arrow F y z
      → Arrow'.Arrow G x y
      → Arrow'.Arrow H x z

-- ### ComposeEqual

record ComposeEqual
  {X Y Z : Object'}
  {F : Arrow' Y Z}
  {G : Arrow' X Y}
  {H : Arrow' X Z}
  (j : Compose F G H)
  : Set
  where

  field

    compose-equal
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → {z : Object'.Object Z}
      → {f₁ f₂ : Arrow'.Arrow F y z}
      → {g₁ g₂ : Arrow'.Arrow G x y}
      → Arrow'.ArrowEqual F f₁ f₂
      → Arrow'.ArrowEqual G g₁ g₂
      → Arrow'.ArrowEqual H
        (Compose.compose j f₁ g₁)
        (Compose.compose j f₂ g₂)

  compose-equal₁
    : {x : Object'.Object X}
    → {y : Object'.Object Y}
    → {z : Object'.Object Z}
    → {f₁ f₂ : Arrow'.Arrow F y z}
    → {g : Arrow'.Arrow G x y}
    → Arrow'.ArrowEqual F f₁ f₂
    → Arrow'.ArrowEqual H
      (Compose.compose j f₁ g)
      (Compose.compose j f₂ g)
  compose-equal₁ p
    = compose-equal p (Arrow'.arrow-refl G)

  compose-equal₂
    : {x : Object'.Object X}
    → {y : Object'.Object Y}
    → {z : Object'.Object Z}
    → {f : Arrow'.Arrow F y z}
    → {g₁ g₂ : Arrow'.Arrow G x y}
    → Arrow'.ArrowEqual G g₁ g₂
    → Arrow'.ArrowEqual H
      (Compose.compose j f g₁)
      (Compose.compose j f g₂)
  compose-equal₂ p
    = compose-equal (Arrow'.arrow-refl F) p

  compose-equal'
    : {x₁ x₂ : Object'.Object X}
    → {y₁ y₂ : Object'.Object Y}
    → {z₁ z₂ : Object'.Object Z}
    → {f₁ : Arrow'.Arrow F y₁ z₁}
    → {f₂ : Arrow'.Arrow F y₂ z₂}
    → {g₁ : Arrow'.Arrow G x₁ y₁}
    → {g₂ : Arrow'.Arrow G x₂ y₂}
    → Arrow'.ArrowEqual' F f₁ f₂
    → Arrow'.ArrowEqual' G g₁ g₂
    → Arrow'.ArrowEqual' H
      (Compose.compose j f₁ g₁)
      (Compose.compose j f₂ g₂)
  compose-equal' (Arrow'.arrow-equal p) (Arrow'.arrow-equal q)
    = Arrow'.arrow-equal (compose-equal p q)

-- ### Precompose

record Precompose
  {X Y : Object'}
  {F : Arrow' X Y}
  {G : Arrow' X X}
  (i : Identity G)
  (j : Compose F G F)
  : Set
  where

  field

    precompose
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → (f : Arrow'.Arrow F x y)
      → Arrow'.ArrowEqual F
        (Compose.compose j f
          (Identity.identity i x)) f

-- ### Postcompose

record Postcompose
  {X Y : Object'}
  {F : Arrow' Y Y}
  {G : Arrow' X Y}
  (i : Identity F)
  (j : Compose F G G)
  : Set
  where

  field

    postcompose
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → (g : Arrow'.Arrow G x y)
      → Arrow'.ArrowEqual G
        (Compose.compose j
          (Identity.identity i y) g) g

-- ### Associative

record Associative
  {W X Y Z : Object'}
  {F : Arrow' Y Z}
  {G : Arrow' X Y}
  {H : Arrow' W X}
  {I : Arrow' X Z}
  {J : Arrow' W Y}
  {K : Arrow' W Z}
  (j : Compose F G I)
  (k : Compose G H J)
  (l : Compose I H K)
  (m : Compose F J K)
  : Set
  where

  field

    associative
      : {w : Object'.Object W}
      → {x : Object'.Object X}
      → {y : Object'.Object Y}
      → {z : Object'.Object Z}
      → (f : Arrow'.Arrow F y z)
      → (g : Arrow'.Arrow G x y)
      → (h : Arrow'.Arrow H w x)
      → Arrow'.ArrowEqual K
        (Compose.compose l
          (Compose.compose j f g) h)
        (Compose.compose m f
          (Compose.compose k g h))

-- ## Chain

-- ### ChainObject

-- #### Base

record ChainObject₀
  : Set₁
  where

-- #### Types

ChainObject
  : ℕ
  → Set₁

record ChainObject'
  (n : ℕ)
  : Set₁

-- #### Definitions

ChainObject zero
  = ChainObject₀
ChainObject (suc n)
  = ChainObject' n

record ChainObject' n where

  inductive
  no-eta-equality

  field

    head
      : Object'

  open Object' head public

  field

    tail
      : Object
      → ChainObject n

module ChainObject
  = ChainObject'

-- #### Construction

chain-object₁
  : Object'
  → ChainObject (suc zero)
chain-object₁ X
  = record
  { head
    = X
  }

-- ### ChainArrow

-- #### Base

record ChainArrow₀
  (X Y : ChainObject₀)
  : Set₁
  where

-- #### Types

ChainArrow
  : {n : ℕ}
  → ChainObject n
  → ChainObject n
  → Set₁

record ChainArrow'
  {n : ℕ}
  (X Y : ChainObject (suc n))
  : Set₁

-- #### Definitions

ChainArrow {n = zero}
  = ChainArrow₀
ChainArrow {n = suc _}
  = ChainArrow'

record ChainArrow' X Y where

  inductive
  no-eta-equality

  field

    head
      : Arrow'
        (ChainObject.head X)
        (ChainObject.head Y)

  open Arrow' head public

  field

    tail
      : (x : ChainObject.Object X)
      → (y : ChainObject.Object Y)
      → ChainArrow
        (ChainObject.tail X x)
        (ChainObject.tail Y y)

module ChainArrow
  = ChainArrow'

-- #### Construction

chain-arrow₁
  : {X Y : Object'}
  → Arrow' X Y
  → ChainArrow
    (chain-object₁ X)
    (chain-object₁ Y)
chain-arrow₁ F
  = record
  { head
    = F
  }

-- ### ChainIdentity

-- #### Base

record ChainIdentity₀
  {X : ChainObject₀}
  (F : ChainArrow₀ X X)
  : Set
  where

-- #### Types

ChainIdentity
  : {n : ℕ}
  → {X : ChainObject n}
  → ChainArrow X X
  → Set

record ChainIdentity'
  {n : ℕ}
  {X : ChainObject (suc n)}
  (F : ChainArrow X X)
  : Set

-- #### Definitions

ChainIdentity {n = zero}
  = ChainIdentity₀
ChainIdentity {n = suc _}
  = ChainIdentity'

record ChainIdentity' {_ X} F where

  inductive

  field

    head
      : Identity
        (ChainArrow.head F)

  open Identity head public

  field

    tail
      : (x : ChainObject.Object X)
      → ChainIdentity
        (ChainArrow.tail F x x)

module ChainIdentity
  = ChainIdentity'

-- #### Construction

chain-identity₁
  : {X : Object'}
  → {F : Arrow' X X}
  → Identity F
  → ChainIdentity
    (chain-arrow₁ F)
chain-identity₁ i
  = record
  { head
    = i
  }

-- ### ChainCompose

-- #### Base

record ChainCompose₀
  {X Y Z : ChainObject₀}
  (F : ChainArrow₀ Y Z)
  (G : ChainArrow₀ X Y)
  (H : ChainArrow₀ X Z)
  : Set
  where

-- #### Types

ChainCompose
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → ChainArrow Y Z
  → ChainArrow X Y
  → ChainArrow X Z
  → Set

record ChainCompose'
  {n : ℕ}
  {X Y Z : ChainObject (suc n)}
  (F : ChainArrow Y Z)
  (G : ChainArrow X Y)
  (H : ChainArrow X Z)
  : Set

-- #### Definitions

ChainCompose {n = zero}
  = ChainCompose₀
ChainCompose {n = suc _}
  = ChainCompose'

record ChainCompose' {_ X Y Z} F G H where

  inductive

  field

    head
      : Compose
        (ChainArrow.head F)
        (ChainArrow.head G)
        (ChainArrow.head H)

  open Compose head public

  field

    tail
      : (x : ChainObject.Object X)
      → (y : ChainObject.Object Y)
      → (z : ChainObject.Object Z)
      → ChainCompose
        (ChainArrow.tail F y z)
        (ChainArrow.tail G x y)
        (ChainArrow.tail H x z)

module ChainCompose
  = ChainCompose'

-- #### Construction

chain-compose₁
  : {X Y Z : Object'}
  → {F : Arrow' Y Z}
  → {G : Arrow' X Y}
  → {H : Arrow' X Z}
  → Compose F G H
  → ChainCompose
    (chain-arrow₁ F)
    (chain-arrow₁ G)
    (chain-arrow₁ H)
chain-compose₁ j
  = record
  { head
    = j
  }

-- ## Dependent

-- ### DependentObject

-- #### Types

DependentObject
  : {n : ℕ}
  → ChainObject n
  → Set₁

record DependentObject'
  {n : ℕ}
  (X : ChainObject (suc n))
  : Set₁

-- #### Definitions

DependentObject {n = zero} _
  = Object'
DependentObject {n = suc _} X
  = DependentObject' X

record DependentObject' X where

  inductive
  no-eta-equality

  field

    tail
      : (x : ChainObject.Object X)
      → DependentObject
        (ChainObject.tail X x)

module DependentObject
  = DependentObject'

-- ### DependentArrow

-- #### Types

DependentArrow
  : {n : ℕ}
  → {X Y : ChainObject n}
  → DependentObject X
  → DependentObject Y
  → Set₁

record DependentArrow'
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  (X' : DependentObject X)
  (Y' : DependentObject Y)
  : Set₁

-- #### Definitions

DependentArrow {n = zero}
  = Arrow'
DependentArrow {n = suc _}
  = DependentArrow'

record DependentArrow' {_ X Y} X' Y' where

  inductive
  no-eta-equality

  field

    tail
      : (x : ChainObject.Object X)
      → (y : ChainObject.Object Y)
      → DependentArrow
        (DependentObject.tail X' x)
        (DependentObject.tail Y' y)

module DependentArrow
  = DependentArrow'

-- ### DependentSimplify

-- #### Types

DependentSimplify
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → DependentArrow X' Y'
  → Set

record DependentSimplify'
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  {X' : DependentObject X}
  {Y' : DependentObject Y}
  (F : DependentArrow X' Y')
  : Set

-- #### Definitions

DependentSimplify {n = zero}
  = Simplify
DependentSimplify {n = suc _}
  = DependentSimplify'

record DependentSimplify' {_ X Y} F where

  inductive

  field

    tail
      : (x : ChainObject.Object X)
      → (y : ChainObject.Object Y)
      → DependentSimplify
        (DependentArrow.tail F x y)

module DependentSimplify
  = DependentSimplify'

-- ### DependentIdentity

-- #### Types

DependentIdentity
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → DependentArrow X' X'
  → Set

record DependentIdentity'
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' : DependentObject X}
  (F : DependentArrow X' X')
  : Set

-- #### Definitions

DependentIdentity {n = zero}
  = Identity
DependentIdentity {n = suc _}
  = DependentIdentity'

record DependentIdentity' {_ X} F where

  inductive
  no-eta-equality

  field

    tail
      : (x : ChainObject.Object X)
      → DependentIdentity
        (DependentArrow.tail F x x)

module DependentIdentity
  = DependentIdentity'

-- ### DependentCompose

-- #### Types

DependentCompose
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {Z' : DependentObject Z}
  → DependentArrow Y' Z'
  → DependentArrow X' Y'
  → DependentArrow X' Z'
  → Set

record DependentCompose'
  {n : ℕ}
  {X Y Z : ChainObject (suc n)}
  {X' : DependentObject X}
  {Y' : DependentObject Y}
  {Z' : DependentObject Z}
  (F : DependentArrow Y' Z')
  (G : DependentArrow X' Y')
  (H : DependentArrow X' Z')
  : Set

-- #### Definitions

DependentCompose {n = zero}
  = Compose
DependentCompose {n = suc _}
  = DependentCompose'

record DependentCompose' {_ X Y Z} F G H where

  inductive
  no-eta-equality

  field

    tail
      : (x : ChainObject.Object X)
      → (y : ChainObject.Object Y)
      → (z : ChainObject.Object Z)
      → DependentCompose
        (DependentArrow.tail F y z)
        (DependentArrow.tail G x y)
        (DependentArrow.tail H x z)

module DependentCompose
  = DependentCompose'

-- ### DependentComposeEqual

-- #### Types

DependentComposeEqual
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {Z' : DependentObject Z}
  → {F : DependentArrow Y' Z'}
  → {G : DependentArrow X' Y'}
  → {H : DependentArrow X' Z'}
  → DependentCompose F G H
  → Set

record DependentComposeEqual'
  {n : ℕ}
  {X Y Z : ChainObject (suc n)}
  {X' : DependentObject X}
  {Y' : DependentObject Y}
  {Z' : DependentObject Z}
  {F : DependentArrow Y' Z'}
  {G : DependentArrow X' Y'}
  {H : DependentArrow X' Z'}
  (j : DependentCompose F G H)
  : Set

-- #### Definitions

DependentComposeEqual {n = zero}
  = ComposeEqual
DependentComposeEqual {n = suc _}
  = DependentComposeEqual'

record DependentComposeEqual' {_ X Y Z} j where

  inductive

  field

    tail
      : (x : ChainObject.Object X)
      → (y : ChainObject.Object Y)
      → (z : ChainObject.Object Z)
      → DependentComposeEqual
        (DependentCompose.tail j x y z)

module DependentComposeEqual
  = DependentComposeEqual'

-- ### DependentPrecompose

-- #### Types

DependentPrecompose
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : DependentArrow X' Y'}
  → {G : DependentArrow X' X'}
  → DependentIdentity G
  → DependentCompose F G F
  → Set

record DependentPrecompose''
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  {X' : DependentObject X}
  {Y' : DependentObject Y}
  {F : DependentArrow X' Y'}
  {G : DependentArrow X' X'}
  (i : DependentIdentity G)
  (j : DependentCompose F G F)
  : Set

-- #### Definitions

DependentPrecompose {n = zero}
  = Precompose
DependentPrecompose {n = suc _}
  = DependentPrecompose''

record DependentPrecompose'' {_ X Y} i j where

  inductive

  field

    tail
      : (x : ChainObject.Object X)
      → (y : ChainObject.Object Y)
      → DependentPrecompose
        (DependentIdentity.tail i x)
        (DependentCompose.tail j x x y)

module DependentPrecompose
  = DependentPrecompose''

-- ### DependentPostcompose

-- #### Types

DependentPostcompose
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : DependentArrow Y' Y'}
  → {G : DependentArrow X' Y'}
  → DependentIdentity F
  → DependentCompose F G G
  → Set

record DependentPostcompose'
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  {X' : DependentObject X}
  {Y' : DependentObject Y}
  {F : DependentArrow Y' Y'}
  {G : DependentArrow X' Y'}
  (i : DependentIdentity F)
  (j : DependentCompose F G G)
  : Set

-- #### Definitions

DependentPostcompose {n = zero}
  = Postcompose
DependentPostcompose {n = suc _}
  = DependentPostcompose'

record DependentPostcompose' {_ X Y} i j where

  inductive

  field

    tail
      : (x : ChainObject.Object X)
      → (y : ChainObject.Object Y)
      → DependentPostcompose
        (DependentIdentity.tail i y)
        (DependentCompose.tail j x y y)

module DependentPostcompose
  = DependentPostcompose'

-- ### DependentAssociative

-- #### Types

DependentAssociative
  : {n : ℕ}
  → {W X Y Z : ChainObject n}
  → {W' : DependentObject W}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {Z' : DependentObject Z}
  → {F : DependentArrow Y' Z'}
  → {G : DependentArrow X' Y'}
  → {H : DependentArrow W' X'}
  → {I : DependentArrow X' Z'}
  → {J : DependentArrow W' Y'}
  → {K : DependentArrow W' Z'}
  → DependentCompose F G I
  → DependentCompose G H J
  → DependentCompose I H K
  → DependentCompose F J K
  → Set

record DependentAssociative'
  {n : ℕ}
  {W X Y Z : ChainObject (suc n)}
  {W' : DependentObject W}
  {X' : DependentObject X}
  {Y' : DependentObject Y}
  {Z' : DependentObject Z}
  {F : DependentArrow Y' Z'}
  {G : DependentArrow X' Y'}
  {H : DependentArrow W' X'}
  {I : DependentArrow X' Z'}
  {J : DependentArrow W' Y'}
  {K : DependentArrow W' Z'}
  (j : DependentCompose F G I)
  (k : DependentCompose G H J)
  (l : DependentCompose I H K)
  (m : DependentCompose F J K)
  : Set

-- #### Definitions

DependentAssociative {n = zero}
  = Associative
DependentAssociative {n = suc _}
  = DependentAssociative'

record DependentAssociative' {_ W X Y Z} j k l m where

  inductive

  field

    tail
      : (w : ChainObject.Object W)
      → (x : ChainObject.Object X)
      → (y : ChainObject.Object Y)
      → (z : ChainObject.Object Z)
      → DependentAssociative
        (DependentCompose.tail j x y z)
        (DependentCompose.tail k w x y)
        (DependentCompose.tail l w x z)
        (DependentCompose.tail m w y z)

module DependentAssociative
  = DependentAssociative'

-- ## Dependent₁

-- ### DependentObject₁

-- #### Definition

DependentObject₁
  : Object'
  → Set₁
DependentObject₁ X
  = DependentObject
    (chain-object₁ X)

-- #### Module

module DependentObject₁
  {X : Object'}
  (X' : DependentObject₁ X)
  where

  open DependentObject X' public

  open module Object'' x
    = Object' (tail x) public

-- ### DependentArrow₁

-- #### Definition

DependentArrow₁
  : {X Y : Object'}
  → DependentObject₁ X
  → DependentObject₁ Y
  → Set₁
DependentArrow₁
  = DependentArrow

-- #### Module

module DependentArrow₁
  {X Y : Object'}
  {X' : DependentObject₁ X}
  {Y' : DependentObject₁ Y}
  (F : DependentArrow₁ X' Y')
  where

  open DependentArrow F public

  open module Arrow'' {x y}
    = Arrow' (tail x y) public

-- ### DependentSimplify₁

-- #### Definition

DependentSimplify₁
  : {X Y : Object'}
  → {X' : DependentObject₁ X}
  → {Y' : DependentObject₁ Y}
  → DependentArrow X' Y'
  → Set
DependentSimplify₁
  = DependentSimplify

-- #### Module

module DependentSimplify₁
  {X Y : Object'}
  {X' : DependentObject₁ X}
  {Y' : DependentObject₁ Y}
  {F : DependentArrow₁ X' Y'}
  (s : DependentSimplify₁ F)
  where

  open DependentSimplify s public

  open module Simplify' {x y}
    = Simplify (tail x y) public

-- ### DependentIdentity₁

-- #### Definition

DependentIdentity₁
  : {X : Object'}
  → {X' : DependentObject₁ X}
  → DependentArrow₁ X' X'
  → Set
DependentIdentity₁
  = DependentIdentity

-- #### Module

module DependentIdentity₁
  {X : Object'}
  {X' : DependentObject₁ X}
  {F : DependentArrow₁ X' X'}
  (i : DependentIdentity₁ F)
  where

  open DependentIdentity i public

  open module Identity' {x}
    = Identity (tail x) public

-- ### DependentCompose₁

-- #### Definition

DependentCompose₁
  : {X Y Z : Object'}
  → {X' : DependentObject₁ X}
  → {Y' : DependentObject₁ Y}
  → {Z' : DependentObject₁ Z}
  → DependentArrow₁ Y' Z'
  → DependentArrow₁ X' Y'
  → DependentArrow₁ X' Z'
  → Set
DependentCompose₁
  = DependentCompose

-- #### Module

module DependentCompose₁
  {X Y Z : Object'}
  {X' : DependentObject₁ X}
  {Y' : DependentObject₁ Y}
  {Z' : DependentObject₁ Z}
  {F : DependentArrow₁ Y' Z'}
  {G : DependentArrow₁ X' Y'}
  {H : DependentArrow₁ X' Z'}
  (j : DependentCompose₁ F G H)
  where

  open DependentCompose j public
  
  open module Compose' {x y z}
    = Compose (tail x y z) public

-- ### DependentComposeEqual₁

-- #### Definition

DependentComposeEqual₁
  : {X Y Z : Object'}
  → {X' : DependentObject₁ X}
  → {Y' : DependentObject₁ Y}
  → {Z' : DependentObject₁ Z}
  → {F : DependentArrow₁ Y' Z'}
  → {G : DependentArrow₁ X' Y'}
  → {H : DependentArrow₁ X' Z'}
  → DependentCompose F G H
  → Set
DependentComposeEqual₁
  = DependentComposeEqual

-- #### Module

module DependentComposeEqual₁
  {X Y Z : Object'}
  {X' : DependentObject₁ X}
  {Y' : DependentObject₁ Y}
  {Z' : DependentObject₁ Z}
  {F : DependentArrow₁ Y' Z'}
  {G : DependentArrow₁ X' Y'}
  {H : DependentArrow₁ X' Z'}
  {j : DependentCompose₁ F G H}
  (p : DependentComposeEqual₁ j)
  where

  open DependentComposeEqual p public
  
  open module ComposeEqual' {x y z}
    = ComposeEqual (tail x y z) public

-- ### DependentPrecompose₁

-- #### Definition

DependentPrecompose₁
  : {X Y : Object'}
  → {X' : DependentObject₁ X}
  → {Y' : DependentObject₁ Y}
  → {F : DependentArrow₁ X' Y'}
  → {G : DependentArrow₁ X' X'}
  → DependentIdentity₁ G
  → DependentCompose₁ F G F
  → Set
DependentPrecompose₁
  = DependentPrecompose

-- #### Module

module DependentPrecompose₁
  {X Y : Object'}
  {X' : DependentObject₁ X}
  {Y' : DependentObject₁ Y}
  {F : DependentArrow₁ X' Y'}
  {G : DependentArrow₁ X' X'}
  {i : DependentIdentity₁ G}
  {j : DependentCompose₁ F G F}
  (p : DependentPrecompose₁ i j)
  where

  open DependentPrecompose p public

  open module Precompose'' {x y}
    = Precompose (tail x y) public

-- ### DependentPostcompose₁

-- #### Definition

DependentPostcompose₁
  : {X Y : Object'}
  → {X' : DependentObject₁ X}
  → {Y' : DependentObject₁ Y}
  → {F : DependentArrow₁ Y' Y'}
  → {G : DependentArrow₁ X' Y'}
  → DependentIdentity₁ F
  → DependentCompose₁ F G G
  → Set
DependentPostcompose₁
  = DependentPostcompose

-- #### Module

module DependentPostcompose₁
  {X Y : Object'}
  {X' : DependentObject₁ X}
  {Y' : DependentObject₁ Y}
  {F : DependentArrow₁ Y' Y'}
  {G : DependentArrow₁ X' Y'}
  {i : DependentIdentity₁ F}
  {j : DependentCompose₁ F G G}
  (p : DependentPostcompose₁ i j)
  where

  open DependentPostcompose p public
  
  open module Postcompose' {x y}
    = Postcompose (tail x y) public

-- ### DependentAssociative₁

-- #### Definition

DependentAssociative₁
  : {W X Y Z : Object'}
  → {W' : DependentObject₁ W}
  → {X' : DependentObject₁ X}
  → {Y' : DependentObject₁ Y}
  → {Z' : DependentObject₁ Z}
  → {F : DependentArrow₁ Y' Z'}
  → {G : DependentArrow₁ X' Y'}
  → {H : DependentArrow₁ W' X'}
  → {I : DependentArrow₁ X' Z'}
  → {J : DependentArrow₁ W' Y'}
  → {K : DependentArrow₁ W' Z'}
  → DependentCompose₁ F G I
  → DependentCompose₁ G H J
  → DependentCompose₁ I H K
  → DependentCompose₁ F J K
  → Set
DependentAssociative₁
  = DependentAssociative

-- #### Module

module DependentAssociative₁
  {W X Y Z : Object'}
  {W' : DependentObject₁ W}
  {X' : DependentObject₁ X}
  {Y' : DependentObject₁ Y}
  {Z' : DependentObject₁ Z}
  {F : DependentArrow₁ Y' Z'}
  {G : DependentArrow₁ X' Y'}
  {H : DependentArrow₁ W' X'}
  {I : DependentArrow₁ X' Z'}
  {J : DependentArrow₁ W' Y'}
  {K : DependentArrow₁ W' Z'}
  {j : DependentCompose₁ F G I}
  {k : DependentCompose₁ G H J}
  {l : DependentCompose₁ I H K}
  {m : DependentCompose₁ F J K}
  (p : DependentAssociative₁ j k l m)
  where

  open DependentAssociative p public

  open module Associative' {w x y z}
    = Associative (tail w x y z) public

