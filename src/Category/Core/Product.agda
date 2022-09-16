module Category.Core.Product where

open import Category.Core
  using (Arrow'; Associative; ChainObject; Compose; ComposeEqual;
    DependentArrow; DependentAssociative; DependentCompose;
    DependentComposeEqual; DependentIdentity; DependentObject;
    DependentPostcompose; DependentPrecompose; DependentSimplify; Identity;
    Object'; Postcompose; Precompose; Simplify)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (_×_; _,_)

-- ## Base

-- ### Object'

object-product
  : Object'
  → Object'
  → Object'
object-product X₁' X₂'
  = record
  { Object
    = Object'.Object X₁'
    × Object'.Object X₂'
  }

-- ### Arrow'

-- #### Function

module _
  {X₁ X₂ Y₁ Y₂ : Object'}
  where

  module ArrowProduct
    (F₁ : Arrow' X₁ Y₁)
    (F₂ : Arrow' X₂ Y₂)
    where

    Arrow
      : Object'.Object (object-product X₁ X₂)
      → Object'.Object (object-product Y₁ Y₂)
      → Set
    Arrow (x₁ , x₂) (y₁ , y₂)
      = Arrow'.Arrow F₁ x₁ y₁
      × Arrow'.Arrow F₂ x₂ y₂

    ArrowEqual
      : {x : Object'.Object (object-product X₁ X₂)}
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → Arrow x y
      → Arrow x y
      → Set
    ArrowEqual (f₁₁ , f₁₂) (f₂₁ , f₂₂)
      = Arrow'.ArrowEqual F₁ f₁₁ f₂₁
      × Arrow'.ArrowEqual F₂ f₁₂ f₂₂

    arrow-refl
      : {x : Object'.Object (object-product X₁ X₂)}
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → {f : Arrow x y}
      → ArrowEqual f f
    arrow-refl
      = Arrow'.arrow-refl F₁
      , Arrow'.arrow-refl F₂

    arrow-sym
      : {x : Object'.Object (object-product X₁ X₂)}
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → {f₁ f₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₁
    arrow-sym (p₁ , p₂)
      = Arrow'.arrow-sym F₁ p₁
      , Arrow'.arrow-sym F₂ p₂

    arrow-trans
      : {x : Object'.Object (object-product X₁ X₂)}
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → {f₁ f₂ f₃ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₃
      → ArrowEqual f₁ f₃
    arrow-trans (p₁₁ , p₁₂) (p₂₁ , p₂₂)
      = Arrow'.arrow-trans F₁ p₁₁ p₂₁
      , Arrow'.arrow-trans F₂ p₁₂ p₂₂
    
  arrow-product
    : Arrow' X₁ Y₁
    → Arrow' X₂ Y₂
    → Arrow'
      (object-product X₁ X₂)
      (object-product Y₁ Y₂)
  arrow-product F₁ F₂
    = record {ArrowProduct F₁ F₂}

-- #### Equality

arrow-equal-product
  : {X₁ X₂ Y₁ Y₂ : Object'}
  → {F₁ : Arrow' X₁ Y₁}
  → {F₂ : Arrow' X₂ Y₂}
  → {x₁₁ x₂₁ : Object'.Object X₁}
  → {x₁₂ x₂₂ : Object'.Object X₂}
  → {y₁₁ y₂₁ : Object'.Object Y₁}
  → {y₁₂ y₂₂ : Object'.Object Y₂}
  → {f₁₁ : Arrow'.Arrow F₁ x₁₁ y₁₁}
  → {f₁₂ : Arrow'.Arrow F₂ x₁₂ y₁₂}
  → {f₂₁ : Arrow'.Arrow F₁ x₂₁ y₂₁}
  → {f₂₂ : Arrow'.Arrow F₂ x₂₂ y₂₂}
  → Arrow'.ArrowEqual' F₁ f₁₁ f₂₁
  → Arrow'.ArrowEqual' F₂ f₁₂ f₂₂
  → Arrow'.ArrowEqual'
    (arrow-product F₁ F₂)
    (f₁₁ , f₁₂)
    (f₂₁ , f₂₂)
arrow-equal-product (Arrow'.arrow-equal p₁) (Arrow'.arrow-equal p₂)
  = Arrow'.arrow-equal (p₁ , p₂)

-- ### Simplify

module _
  {X₁ X₂ Y₁ Y₂ : Object'}
  {F₁ : Arrow' X₁ Y₁}
  {F₂ : Arrow' X₂ Y₂}
  where

  module SimplifyProduct
    (s₁ : Simplify F₁)
    (s₂ : Simplify F₂)
    where

    simplify
      : {x : Object'.Object (object-product X₁ X₂)}
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → Arrow'.Arrow (arrow-product F₁ F₂) x y
      → Arrow'.Arrow (arrow-product F₁ F₂) x y
    simplify (f₁ , f₂)
      = Simplify.simplify s₁ f₁
      , Simplify.simplify s₂ f₂

    simplify-equal
      : {x : Object'.Object (object-product X₁ X₂)}
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → (f : Arrow'.Arrow (arrow-product F₁ F₂) x y)
      → Arrow'.ArrowEqual (arrow-product F₁ F₂) (simplify f) f
    simplify-equal (f₁ , f₂)
      = Simplify.simplify-equal s₁ f₁
      , Simplify.simplify-equal s₂ f₂

  simplify-product
    : Simplify F₁
    → Simplify F₂
    → Simplify
      (arrow-product F₁ F₂)
  simplify-product s₁ s₂
    = record {SimplifyProduct s₁ s₂}

-- ### Identity

module _
  {X₁ X₂ : Object'}
  {F₁ : Arrow' X₁ X₁}
  {F₂ : Arrow' X₂ X₂}
  where

  module IdentityProduct
    (i₁ : Identity F₁)
    (i₂ : Identity F₂)
    where

    identity
      : (x : Object'.Object (object-product X₁ X₂))
      → Arrow'.Arrow (arrow-product F₁ F₂) x x
    identity (x₁ , x₂)
      = Identity.identity i₁ x₁
      , Identity.identity i₂ x₂

  identity-product
    : Identity F₁
    → Identity F₂
    → Identity
      (arrow-product F₁ F₂)
  identity-product i₁ i₂
    = record {IdentityProduct i₁ i₂}

-- ### Compose

module _
  {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Object'}
  {F₁ : Arrow' Y₁ Z₁}
  {F₂ : Arrow' Y₂ Z₂}
  {G₁ : Arrow' X₁ Y₁}
  {G₂ : Arrow' X₂ Y₂}
  {H₁ : Arrow' X₁ Z₁}
  {H₂ : Arrow' X₂ Z₂}
  where

  module ComposeProduct
    (j₁ : Compose F₁ G₁ H₁)
    (j₂ : Compose F₂ G₂ H₂)
    where

    compose
      : {x : Object'.Object (object-product X₁ X₂)}
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → {z : Object'.Object (object-product Z₁ Z₂)}
      → Arrow'.Arrow (arrow-product F₁ F₂) y z
      → Arrow'.Arrow (arrow-product G₁ G₂) x y
      → Arrow'.Arrow (arrow-product H₁ H₂) x z
    compose (f₁ , f₂) (g₁ , g₂)
      = Compose.compose j₁ f₁ g₁
      , Compose.compose j₂ f₂ g₂

  compose-product
    : Compose F₁ G₁ H₁
    → Compose F₂ G₂ H₂
    → Compose
      (arrow-product F₁ F₂)
      (arrow-product G₁ G₂)
      (arrow-product H₁ H₂)
  compose-product j₁ j₂
    = record {ComposeProduct j₁ j₂}

-- ### ComposeEqual

module _
  {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Object'}
  {F₁ : Arrow' Y₁ Z₁}
  {F₂ : Arrow' Y₂ Z₂}
  {G₁ : Arrow' X₁ Y₁}
  {G₂ : Arrow' X₂ Y₂}
  {H₁ : Arrow' X₁ Z₁}
  {H₂ : Arrow' X₂ Z₂}
  {j₁ : Compose F₁ G₁ H₁}
  {j₂ : Compose F₂ G₂ H₂}
  where

  module ComposeEqualProduct
    (p₁ : ComposeEqual j₁)
    (p₂ : ComposeEqual j₂)
    where

    compose-equal
      : {x : Object'.Object (object-product X₁ X₂)}
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → {z : Object'.Object (object-product Z₁ Z₂)}
      → {f₁ f₂ : Arrow'.Arrow (arrow-product F₁ F₂) y z}
      → {g₁ g₂ : Arrow'.Arrow (arrow-product G₁ G₂) x y}
      → Arrow'.ArrowEqual (arrow-product F₁ F₂) f₁ f₂
      → Arrow'.ArrowEqual (arrow-product G₁ G₂) g₁ g₂
      → Arrow'.ArrowEqual (arrow-product H₁ H₂)
        (Compose.compose (compose-product j₁ j₂) f₁ g₁)
        (Compose.compose (compose-product j₁ j₂) f₂ g₂)
    compose-equal (q₁ , q₂) (r₁ , r₂)
      = ComposeEqual.compose-equal p₁ q₁ r₁
      , ComposeEqual.compose-equal p₂ q₂ r₂

  compose-equal-product
    : ComposeEqual j₁
    → ComposeEqual j₂
    → ComposeEqual
      (compose-product j₁ j₂)
  compose-equal-product p₁ p₂
    = record {ComposeEqualProduct p₁ p₂}

-- ### Precompose

module _
  {X₁ X₂ Y₁ Y₂ : Object'}
  {F₁ : Arrow' X₁ Y₁}
  {F₂ : Arrow' X₂ Y₂}
  {G₁ : Arrow' X₁ X₁}
  {G₂ : Arrow' X₂ X₂}
  {i₁ : Identity G₁}
  {i₂ : Identity G₂}
  {j₁ : Compose F₁ G₁ F₁}
  {j₂ : Compose F₂ G₂ F₂}
  where

  module PrecomposeProduct
    (p₁ : Precompose i₁ j₁)
    (p₂ : Precompose i₂ j₂)
    where

    precompose
      : {x : Object'.Object (object-product X₁ X₂)}
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → (f : Arrow'.Arrow (arrow-product F₁ F₂) x y)
      → Arrow'.ArrowEqual (arrow-product F₁ F₂)
        (Compose.compose (compose-product j₁ j₂) f
          (Identity.identity (identity-product i₁ i₂) x)) f
    precompose (f₁ , f₂)
      = Precompose.precompose p₁ f₁
      , Precompose.precompose p₂ f₂

  precompose-product
    : Precompose i₁ j₁
    → Precompose i₂ j₂
    → Precompose
      (identity-product i₁ i₂)
      (compose-product j₁ j₂)
  precompose-product p₁ p₂
    = record {PrecomposeProduct p₁ p₂}

-- ### Postcompose

module _
  {X₁ X₂ Y₁ Y₂ : Object'}
  {F₁ : Arrow' Y₁ Y₁}
  {F₂ : Arrow' Y₂ Y₂}
  {G₁ : Arrow' X₁ Y₁}
  {G₂ : Arrow' X₂ Y₂}
  {i₁ : Identity F₁}
  {i₂ : Identity F₂}
  {j₁ : Compose F₁ G₁ G₁}
  {j₂ : Compose F₂ G₂ G₂}
  where

  module PostcomposeProduct
    (p₁ : Postcompose i₁ j₁)
    (p₂ : Postcompose i₂ j₂)
    where

    postcompose
      : {x : Object'.Object (object-product X₁ X₂)}
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → (g : Arrow'.Arrow (arrow-product G₁ G₂) x y)
      → Arrow'.ArrowEqual (arrow-product G₁ G₂)
        (Compose.compose (compose-product j₁ j₂)
          (Identity.identity (identity-product i₁ i₂) y) g) g
    postcompose (g₁ , g₂)
      = Postcompose.postcompose p₁ g₁
      , Postcompose.postcompose p₂ g₂

  postcompose-product
    : Postcompose i₁ j₁
    → Postcompose i₂ j₂
    → Postcompose
      (identity-product i₁ i₂)
      (compose-product j₁ j₂)
  postcompose-product p₁ p₂
    = record {PostcomposeProduct p₁ p₂}

-- ### Associative

module _
  {W₁ W₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Object'}
  {F₁ : Arrow' Y₁ Z₁}
  {F₂ : Arrow' Y₂ Z₂}
  {G₁ : Arrow' X₁ Y₁}
  {G₂ : Arrow' X₂ Y₂}
  {H₁ : Arrow' W₁ X₁}
  {H₂ : Arrow' W₂ X₂}
  {I₁ : Arrow' X₁ Z₁}
  {I₂ : Arrow' X₂ Z₂}
  {J₁ : Arrow' W₁ Y₁}
  {J₂ : Arrow' W₂ Y₂}
  {K₁ : Arrow' W₁ Z₁}
  {K₂ : Arrow' W₂ Z₂}
  {j₁ : Compose F₁ G₁ I₁}
  {j₂ : Compose F₂ G₂ I₂}
  {k₁ : Compose G₁ H₁ J₁}
  {k₂ : Compose G₂ H₂ J₂}
  {l₁ : Compose I₁ H₁ K₁}
  {l₂ : Compose I₂ H₂ K₂}
  {m₁ : Compose F₁ J₁ K₁}
  {m₂ : Compose F₂ J₂ K₂}
  where

  module AssociativeProduct
    (p₁ : Associative j₁ k₁ l₁ m₁)
    (p₂ : Associative j₂ k₂ l₂ m₂)
    where

    associative
      : {w : Object'.Object (object-product W₁ W₂)}
      → {x : Object'.Object (object-product X₁ X₂)}
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → {z : Object'.Object (object-product Z₁ Z₂)}
      → (f : Arrow'.Arrow (arrow-product F₁ F₂) y z)
      → (g : Arrow'.Arrow (arrow-product G₁ G₂) x y)
      → (h : Arrow'.Arrow (arrow-product H₁ H₂) w x)
      → Arrow'.ArrowEqual (arrow-product K₁ K₂)
        (Compose.compose (compose-product l₁ l₂)
          (Compose.compose (compose-product j₁ j₂) f g) h)
        (Compose.compose (compose-product m₁ m₂) f
          (Compose.compose (compose-product k₁ k₂) g h))
    associative (f₁ , f₂) (g₁ , g₂) (h₁ , h₂)
      = Associative.associative p₁ f₁ g₁ h₁
      , Associative.associative p₂ f₂ g₂ h₂

  associative-product
    : Associative j₁ k₁ l₁ m₁
    → Associative j₂ k₂ l₂ m₂
    → Associative
      (compose-product j₁ j₂)
      (compose-product k₁ k₂)
      (compose-product l₁ l₂)
      (compose-product m₁ m₂)
  associative-product p₁ p₂
    = record {AssociativeProduct p₁ p₂}

-- ## Dependent

-- ### DependentObject

dependent-object-product
  : {n : ℕ}
  → {X : ChainObject n}
  → DependentObject X
  → DependentObject X
  → DependentObject X
dependent-object-product {n = zero} X₁' X₂'
  = object-product X₁' X₂'
dependent-object-product {n = suc _} X₁' X₂'
  = record
  { tail
    = λ x → dependent-object-product
      (DependentObject.tail X₁' x)
      (DependentObject.tail X₂' x)
  }

-- ### DependentArrow

dependent-arrow-product
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {Y₁' Y₂' : DependentObject Y}
  → DependentArrow X₁' Y₁'
  → DependentArrow X₂' Y₂'
  → DependentArrow
    (dependent-object-product X₁' X₂')
    (dependent-object-product Y₁' Y₂')
dependent-arrow-product {n = zero} F₁ F₂
  = arrow-product F₁ F₂
dependent-arrow-product {n = suc _} F₁ F₂
  = record
  { tail
    = λ x y → dependent-arrow-product
      (DependentArrow.tail F₁ x y)
      (DependentArrow.tail F₂ x y)
  }

-- ### DependentSimplify

dependent-simplify-product
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {Y₁' Y₂' : DependentObject Y}
  → {F₁ : DependentArrow X₁' Y₁'}
  → {F₂ : DependentArrow X₂' Y₂'}
  → DependentSimplify F₁
  → DependentSimplify F₂
  → DependentSimplify
    (dependent-arrow-product F₁ F₂)
dependent-simplify-product {n = zero} s₁ s₂
  = simplify-product s₁ s₂
dependent-simplify-product {n = suc _} s₁ s₂
  = record
  { tail
    = λ x y → dependent-simplify-product
      (DependentSimplify.tail s₁ x y)
      (DependentSimplify.tail s₂ x y)
  }

-- ### DependentIdentity

dependent-identity-product
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {F₁ : DependentArrow X₁' X₁'}
  → {F₂ : DependentArrow X₂' X₂'}
  → DependentIdentity F₁
  → DependentIdentity F₂
  → DependentIdentity
    (dependent-arrow-product F₁ F₂)
dependent-identity-product {n = zero} i₁ i₂
  = identity-product i₁ i₂
dependent-identity-product {n = suc _} i₁ i₂
  = record
  { tail
    = λ x → dependent-identity-product
      (DependentIdentity.tail i₁ x)
      (DependentIdentity.tail i₂ x)
  }

-- ### DependentCompose

dependent-compose-product
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {Y₁' Y₂' : DependentObject Y}
  → {Z₁' Z₂' : DependentObject Z}
  → {F₁ : DependentArrow Y₁' Z₁'}
  → {F₂ : DependentArrow Y₂' Z₂'}
  → {G₁ : DependentArrow X₁' Y₁'}
  → {G₂ : DependentArrow X₂' Y₂'}
  → {H₁ : DependentArrow X₁' Z₁'}
  → {H₂ : DependentArrow X₂' Z₂'}
  → DependentCompose F₁ G₁ H₁
  → DependentCompose F₂ G₂ H₂
  → DependentCompose
    (dependent-arrow-product F₁ F₂)
    (dependent-arrow-product G₁ G₂)
    (dependent-arrow-product H₁ H₂)
dependent-compose-product {n = zero} j₁ j₂
  = compose-product j₁ j₂
dependent-compose-product {n = suc _} j₁ j₂
  = record
  { tail
    = λ x y z → dependent-compose-product
      (DependentCompose.tail j₁ x y z)
      (DependentCompose.tail j₂ x y z)
  }

-- ### DependentComposeEqual

dependent-compose-equal-product
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {Y₁' Y₂' : DependentObject Y}
  → {Z₁' Z₂' : DependentObject Z}
  → {F₁ : DependentArrow Y₁' Z₁'}
  → {F₂ : DependentArrow Y₂' Z₂'}
  → {G₁ : DependentArrow X₁' Y₁'}
  → {G₂ : DependentArrow X₂' Y₂'}
  → {H₁ : DependentArrow X₁' Z₁'}
  → {H₂ : DependentArrow X₂' Z₂'}
  → {j₁ : DependentCompose F₁ G₁ H₁}
  → {j₂ : DependentCompose F₂ G₂ H₂}
  → DependentComposeEqual j₁
  → DependentComposeEqual j₂
  → DependentComposeEqual
    (dependent-compose-product j₁ j₂)
dependent-compose-equal-product {n = zero} p₁ p₂
  = compose-equal-product p₁ p₂
dependent-compose-equal-product {n = suc _} p₁ p₂
  = record
  { tail
    = λ x y z → dependent-compose-equal-product
      (DependentComposeEqual.tail p₁ x y z)
      (DependentComposeEqual.tail p₂ x y z)
  }

-- ### DependentPrecompose

dependent-precompose-product
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {Y₁' Y₂' : DependentObject Y}
  → {F₁ : DependentArrow X₁' Y₁'}
  → {F₂ : DependentArrow X₂' Y₂'}
  → {G₁ : DependentArrow X₁' X₁'}
  → {G₂ : DependentArrow X₂' X₂'}
  → {i₁ : DependentIdentity G₁}
  → {i₂ : DependentIdentity G₂}
  → {j₁ : DependentCompose F₁ G₁ F₁}
  → {j₂ : DependentCompose F₂ G₂ F₂}
  → DependentPrecompose i₁ j₁
  → DependentPrecompose i₂ j₂
  → DependentPrecompose
    (dependent-identity-product i₁ i₂)
    (dependent-compose-product j₁ j₂)
dependent-precompose-product {n = zero} p₁ p₂
  = precompose-product p₁ p₂
dependent-precompose-product {n = suc _} p₁ p₂
  = record
  { tail
    = λ x y → dependent-precompose-product
      (DependentPrecompose.tail p₁ x y)
      (DependentPrecompose.tail p₂ x y)
  }

-- ### DependentPostcompose

dependent-postcompose-product
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {Y₁' Y₂' : DependentObject Y}
  → {F₁ : DependentArrow Y₁' Y₁'}
  → {F₂ : DependentArrow Y₂' Y₂'}
  → {G₁ : DependentArrow X₁' Y₁'}
  → {G₂ : DependentArrow X₂' Y₂'}
  → {i₁ : DependentIdentity F₁}
  → {i₂ : DependentIdentity F₂}
  → {j₁ : DependentCompose F₁ G₁ G₁}
  → {j₂ : DependentCompose F₂ G₂ G₂}
  → DependentPostcompose i₁ j₁
  → DependentPostcompose i₂ j₂
  → DependentPostcompose
    (dependent-identity-product i₁ i₂)
    (dependent-compose-product j₁ j₂)
dependent-postcompose-product {n = zero} p₁ p₂
  = postcompose-product p₁ p₂
dependent-postcompose-product {n = suc _} p₁ p₂
  = record
  { tail
    = λ x y → dependent-postcompose-product
      (DependentPostcompose.tail p₁ x y)
      (DependentPostcompose.tail p₂ x y)
  }

-- ### DependentAssociative

dependent-associative-product
  : {n : ℕ}
  → {W X Y Z : ChainObject n}
  → {W₁' W₂' : DependentObject W}
  → {X₁' X₂' : DependentObject X}
  → {Y₁' Y₂' : DependentObject Y}
  → {Z₁' Z₂' : DependentObject Z}
  → {F₁ : DependentArrow Y₁' Z₁'}
  → {F₂ : DependentArrow Y₂' Z₂'}
  → {G₁ : DependentArrow X₁' Y₁'}
  → {G₂ : DependentArrow X₂' Y₂'}
  → {H₁ : DependentArrow W₁' X₁'}
  → {H₂ : DependentArrow W₂' X₂'}
  → {I₁ : DependentArrow X₁' Z₁'}
  → {I₂ : DependentArrow X₂' Z₂'}
  → {J₁ : DependentArrow W₁' Y₁'}
  → {J₂ : DependentArrow W₂' Y₂'}
  → {K₁ : DependentArrow W₁' Z₁'}
  → {K₂ : DependentArrow W₂' Z₂'}
  → {j₁ : DependentCompose F₁ G₁ I₁}
  → {j₂ : DependentCompose F₂ G₂ I₂}
  → {k₁ : DependentCompose G₁ H₁ J₁}
  → {k₂ : DependentCompose G₂ H₂ J₂}
  → {l₁ : DependentCompose I₁ H₁ K₁}
  → {l₂ : DependentCompose I₂ H₂ K₂}
  → {m₁ : DependentCompose F₁ J₁ K₁}
  → {m₂ : DependentCompose F₂ J₂ K₂}
  → DependentAssociative j₁ k₁ l₁ m₁
  → DependentAssociative j₂ k₂ l₂ m₂
  → DependentAssociative
    (dependent-compose-product j₁ j₂)
    (dependent-compose-product k₁ k₂)
    (dependent-compose-product l₁ l₂)
    (dependent-compose-product m₁ m₂)
dependent-associative-product {n = zero} p₁ p₂
  = associative-product p₁ p₂
dependent-associative-product {n = suc _} p₁ p₂
  = record
  { tail
    = λ w x y z → dependent-associative-product
      (DependentAssociative.tail p₁ w x y z)
      (DependentAssociative.tail p₂ w x y z)
  }

