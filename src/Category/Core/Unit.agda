module Category.Core.Unit where

open import Category.Core
  using (Arrow'; Associative; ChainObject; Compose; ComposeEqual;
    DependentArrow; DependentAssociative; DependentCompose;
    DependentComposeEqual; DependentIdentity; DependentObject;
    DependentPostcompose; DependentPrecompose; DependentSimplify; Identity;
    Object'; Postcompose; Precompose; Simplify)
open import Data.Equal
  using (_≡_; refl)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### Arrow'

-- #### Function

module ArrowUnit
  (X Y : Object')
  where

  record Arrow
    (x : Object'.Object X)
    (y : Object'.Object Y)
    : Set
    where

    constructor

      tt

  record ArrowEqual
    {x : Object'.Object X}
    {y : Object'.Object Y}
    (f₁ f₂ : Arrow x y)
    : Set
    where

    constructor

      tt

arrow-unit
  : (X Y : Object')
  → Arrow' X Y
arrow-unit X Y
  = record {ArrowUnit X Y}

-- #### Equality

arrow-equal-unit
  : {X Y : Object'}
  → {x₁ x₂ : Object'.Object X}
  → {y₁ y₂ : Object'.Object Y}
  → x₁ ≡ x₂
  → y₁ ≡ y₂
  → Arrow'.ArrowEqual'
    (arrow-unit X Y) {x₁ = x₁} {x₂ = x₂} {y₁ = y₁} {y₂ = y₂}
    ArrowUnit.tt
    ArrowUnit.tt
arrow-equal-unit refl refl
  = Arrow'.arrow-equal ArrowUnit.tt

-- ### Simplify

simplify-unit
  : (X Y : Object')
  → Simplify
    (arrow-unit X Y)
simplify-unit _ _
  = record {}

-- ### Identity

identity-unit
  : (X : Object')
  → Identity
    (arrow-unit X X)
identity-unit _
  = record {}

-- ### Compose

compose-unit
  : (X Y Z : Object')
  → Compose
    (arrow-unit Y Z)
    (arrow-unit X Y)
    (arrow-unit X Z)
compose-unit _ _ _
  = record {}

-- ### ComposeEqual

compose-equal-unit
  : (X Y Z : Object')
  → ComposeEqual
    (compose-unit X Y Z)
compose-equal-unit _ _ _
  = record {}

-- ### Precompose

precompose-unit
  : (X Y : Object')
  → Precompose
    (identity-unit X)
    (compose-unit X X Y)
precompose-unit _ _
  = record {}

-- ### Postcompose

postcompose-unit
  : (X Y : Object')
  → Postcompose
    (identity-unit Y)
    (compose-unit X Y Y)
postcompose-unit _ _
  = record {}

-- ### Associative

associative-unit
  : (W X Y Z : Object')
  → Associative
    (compose-unit X Y Z)
    (compose-unit W X Y)
    (compose-unit W X Z)
    (compose-unit W Y Z)
associative-unit _ _ _ _
  = record {}

-- ## Dependent

-- ### DependentArrow

dependent-arrow-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → (X' : DependentObject X)
  → (Y' : DependentObject Y)
  → DependentArrow X' Y'
dependent-arrow-unit {n = zero} X' Y'
  = arrow-unit X' Y'
dependent-arrow-unit {n = suc _} X' Y'
  = record
  { tail
    = λ x y → dependent-arrow-unit
      (DependentObject.tail X' x)
      (DependentObject.tail Y' y)
  }

-- ### DependentSimplify

dependent-simplify-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → (X' : DependentObject X)
  → (Y' : DependentObject Y)
  → DependentSimplify
    (dependent-arrow-unit X' Y')
dependent-simplify-unit {n = zero} X' Y'
  = simplify-unit X' Y'
dependent-simplify-unit {n = suc _} X' Y'
  = record
  { tail
    = λ x y → dependent-simplify-unit
      (DependentObject.tail X' x)
      (DependentObject.tail Y' y)
  }

-- ### DependentIdentity

dependent-identity-unit
  : {n : ℕ}
  → {X : ChainObject n}
  → (X' : DependentObject X)
  → DependentIdentity
    (dependent-arrow-unit X' X')
dependent-identity-unit {n = zero} X'
  = identity-unit X'
dependent-identity-unit {n = suc _} X'
  = record
  { tail
    = λ x → dependent-identity-unit
      (DependentObject.tail X' x)
  }

-- ### DependentCompose

dependent-compose-unit
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → (X' : DependentObject X)
  → (Y' : DependentObject Y)
  → (Z' : DependentObject Z)
  → DependentCompose
    (dependent-arrow-unit Y' Z')
    (dependent-arrow-unit X' Y')
    (dependent-arrow-unit X' Z')
dependent-compose-unit {n = zero} X' Y' Z'
  = compose-unit X' Y' Z'
dependent-compose-unit {n = suc _} X' Y' Z'
  = record
  { tail
    = λ x y z → dependent-compose-unit
      (DependentObject.tail X' x)
      (DependentObject.tail Y' y)
      (DependentObject.tail Z' z)
  }

-- ### DependentComposeEqual

dependent-compose-equal-unit
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → (X' : DependentObject X)
  → (Y' : DependentObject Y)
  → (Z' : DependentObject Z)
  → DependentComposeEqual
    (dependent-compose-unit X' Y' Z')
dependent-compose-equal-unit {n = zero} X' Y' Z'
  = compose-equal-unit X' Y' Z'
dependent-compose-equal-unit {n = suc _} X' Y' Z'
  = record
  { tail
    = λ x y z → dependent-compose-equal-unit
      (DependentObject.tail X' x)
      (DependentObject.tail Y' y)
      (DependentObject.tail Z' z)
  }

-- ### DependentPrecompose

dependent-precompose-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → (X' : DependentObject X)
  → (Y' : DependentObject Y)
  → DependentPrecompose
    (dependent-identity-unit X')
    (dependent-compose-unit X' X' Y')
dependent-precompose-unit {n = zero} X' Y'
  = precompose-unit X' Y'
dependent-precompose-unit {n = suc _} X' Y'
  = record
  { tail
    = λ x y → dependent-precompose-unit
      (DependentObject.tail X' x)
      (DependentObject.tail Y' y)
  }

-- ### DependentPostcompose

dependent-postcompose-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → (X' : DependentObject X)
  → (Y' : DependentObject Y)
  → DependentPostcompose
    (dependent-identity-unit Y')
    (dependent-compose-unit X' Y' Y')
dependent-postcompose-unit {n = zero} X' Y'
  = postcompose-unit X' Y'
dependent-postcompose-unit {n = suc _} X' Y'
  = record
  { tail
    = λ x y → dependent-postcompose-unit
      (DependentObject.tail X' x)
      (DependentObject.tail Y' y)
  }

-- ### DependentAssociative

dependent-associative-unit
  : {n : ℕ}
  → {W X Y Z : ChainObject n}
  → (W' : DependentObject W)
  → (X' : DependentObject X)
  → (Y' : DependentObject Y)
  → (Z' : DependentObject Z)
  → DependentAssociative
    (dependent-compose-unit X' Y' Z')
    (dependent-compose-unit W' X' Y')
    (dependent-compose-unit W' X' Z')
    (dependent-compose-unit W' Y' Z')
dependent-associative-unit {n = zero} W' X' Y' Z'
  = associative-unit W' X' Y' Z'
dependent-associative-unit {n = suc _} W' X' Y' Z'
  = record
  { tail
    = λ w x y z → dependent-associative-unit
      (DependentObject.tail W' w)
      (DependentObject.tail X' x)
      (DependentObject.tail Y' y)
      (DependentObject.tail Z' z)
  }

