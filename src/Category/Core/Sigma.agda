module Category.Core.Sigma where

open import Category.Core
  using (Arrow'; Associative; ChainObject; Compose; ComposeEqual;
    DependentArrow; DependentArrow₁; DependentAssociative;
    DependentAssociative₁; DependentCompose; DependentCompose₁;
    DependentComposeEqual; DependentComposeEqual₁; DependentIdentity;
    DependentIdentity₁; DependentObject; DependentObject₁; DependentPostcompose;
    DependentPostcompose₁; DependentPrecompose; DependentPrecompose₁; Identity;
    Object'; Postcompose; Precompose)
open import Category.Core.Snoc
  using (chain-object-snoc)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ; _,_; π₁; π₂)

-- ## Base

-- ### Object'

object-sigma
  : {X₁ : Object'}
  → DependentObject₁ X₁
  → Object'
object-sigma {X₁ = X₁} X₂
  = record
  { Object
    = x₁ ∈ Object'.Object X₁
    × DependentObject₁.Object X₂ x₁
  }

-- ### Arrow'

module _
  {X₁ Y₁ : Object'}
  {X₂ : DependentObject₁ X₁}
  {Y₂ : DependentObject₁ Y₁}
  where

  module ArrowSigma
    (F₁ : Arrow' X₁ Y₁)
    (F₂ : DependentArrow₁ X₂ Y₂)
    where

    data Arrow
      (x : Object'.Object (object-sigma X₂))
      (y : Object'.Object (object-sigma Y₂))
      : Set
      where

      arrow₁
        : Arrow'.Arrow F₁ (π₁ x) (π₁ y)
        → Arrow x y

      arrow₂
        : Arrow'.Arrow F₁ (π₁ x) (π₁ y)
        → DependentArrow₁.Arrow F₂ (π₂ x) (π₂ y)
        → Arrow x y

    data ArrowEqual
      {x : Object'.Object (object-sigma X₂)}
      {y : Object'.Object (object-sigma Y₂)}
      : Arrow x y
      → Arrow x y
      → Set
      where

      arrow₁
        : {f₁₁ f₂₁ : Arrow'.Arrow F₁ (π₁ x) (π₁ y)}
        → Arrow'.ArrowEqual F₁ f₁₁ f₂₁
        → ArrowEqual (arrow₁ f₁₁) (arrow₁ f₂₁)

      arrow₂
        : {f₁₁ f₂₁ : Arrow'.Arrow F₁ (π₁ x) (π₁ y)}
        → {f₁₂ f₂₂ : DependentArrow₁.Arrow F₂ (π₂ x) (π₂ y)}
        → Arrow'.ArrowEqual F₁ f₁₁ f₂₁
        → DependentArrow₁.ArrowEqual F₂ f₁₂ f₂₂
        → ArrowEqual (arrow₂ f₁₁ f₁₂) (arrow₂ f₂₁ f₂₂)

    arrow-refl
      : {x : Object'.Object (object-sigma X₂)}
      → {y : Object'.Object (object-sigma Y₂)}
      → {f : Arrow x y}
      → ArrowEqual f f
    arrow-refl {f = arrow₁ _}
      = arrow₁
        (Arrow'.arrow-refl F₁)
    arrow-refl {f = arrow₂ _ _}
      = arrow₂
        (Arrow'.arrow-refl F₁)
        (DependentArrow₁.arrow-refl F₂)

    arrow-sym
      : {x : Object'.Object (object-sigma X₂)}
      → {y : Object'.Object (object-sigma Y₂)}
      → {f₁ f₂ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₁
    arrow-sym (arrow₁ p₁)
      = arrow₁
        (Arrow'.arrow-sym F₁ p₁)
    arrow-sym (arrow₂ p₁ p₂)
      = arrow₂
        (Arrow'.arrow-sym F₁ p₁)
        (DependentArrow₁.arrow-sym F₂ p₂)

    arrow-trans
      : {x : Object'.Object (object-sigma X₂)}
      → {y : Object'.Object (object-sigma Y₂)}
      → {f₁ f₂ f₃ : Arrow x y}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₃
      → ArrowEqual f₁ f₃
    arrow-trans (arrow₁ p₁₁) (arrow₁ p₂₁)
      = arrow₁
        (Arrow'.arrow-trans F₁ p₁₁ p₂₁)
    arrow-trans (arrow₂ p₁₁ p₁₂) (arrow₂ p₂₁ p₂₂)
      = arrow₂
        (Arrow'.arrow-trans F₁ p₁₁ p₂₁)
        (DependentArrow₁.arrow-trans F₂ p₁₂ p₂₂)
    
  arrow-sigma
    : Arrow' X₁ Y₁
    → DependentArrow₁ X₂ Y₂
    → Arrow'
      (object-sigma X₂)
      (object-sigma Y₂)
  arrow-sigma F₁ F₂
    = record {ArrowSigma F₁ F₂}

-- ### Identity

module _
  {X₁ : Object'}
  {X₂ : DependentObject₁ X₁}
  {F₁ : Arrow' X₁ X₁}
  {F₂ : DependentArrow₁ X₂ X₂}
  where

  module IdentitySigma
    (i₁ : Identity F₁)
    (i₂ : DependentIdentity₁ F₂)
    where

    identity
      : (x : Object'.Object (object-sigma X₂))
      → Arrow'.Arrow (arrow-sigma F₁ F₂) x x
    identity (x₁ , x₂)
      = ArrowSigma.arrow₂
        (Identity.identity i₁ x₁)
        (DependentIdentity₁.identity i₂ x₂)

  identity-sigma
    : Identity F₁
    → DependentIdentity₁ F₂
    → Identity
      (arrow-sigma F₁ F₂)
  identity-sigma i₁ i₂
    = record {IdentitySigma i₁ i₂}

-- ### Compose

module _
  {X₁ Y₁ Z₁ : Object'}
  {X₂ : DependentObject₁ X₁}
  {Y₂ : DependentObject₁ Y₁}
  {Z₂ : DependentObject₁ Z₁}
  {F₁ : Arrow' Y₁ Z₁}
  {G₁ : Arrow' X₁ Y₁}
  {H₁ : Arrow' X₁ Z₁}
  {F₂ : DependentArrow₁ Y₂ Z₂}
  {G₂ : DependentArrow₁ X₂ Y₂}
  {H₂ : DependentArrow₁ X₂ Z₂}
  where

  module ComposeSigma
    (j₁ : Compose F₁ G₁ H₁)
    (j₂ : DependentCompose₁ F₂ G₂ H₂)
    where

    compose
      : {x : Object'.Object (object-sigma X₂)}
      → {y : Object'.Object (object-sigma Y₂)}
      → {z : Object'.Object (object-sigma Z₂)}
      → Arrow'.Arrow (arrow-sigma F₁ F₂) y z
      → Arrow'.Arrow (arrow-sigma G₁ G₂) x y
      → Arrow'.Arrow (arrow-sigma H₁ H₂) x z
    compose (ArrowSigma.arrow₁ f₁) (ArrowSigma.arrow₁ g₁)
      = ArrowSigma.arrow₁
        (Compose.compose j₁ f₁ g₁)
    compose (ArrowSigma.arrow₁ f₁) (ArrowSigma.arrow₂ g₁ _)
      = ArrowSigma.arrow₁
        (Compose.compose j₁ f₁ g₁)
    compose (ArrowSigma.arrow₂ f₁ _) (ArrowSigma.arrow₁ g₁)
      = ArrowSigma.arrow₁
        (Compose.compose j₁ f₁ g₁)
    compose (ArrowSigma.arrow₂ f₁ f₂) (ArrowSigma.arrow₂ g₁ g₂)
      = ArrowSigma.arrow₂
        (Compose.compose j₁ f₁ g₁)
        (DependentCompose₁.compose j₂ f₂ g₂)

  compose-sigma
    : Compose F₁ G₁ H₁
    → DependentCompose₁ F₂ G₂ H₂
    → Compose
      (arrow-sigma F₁ F₂)
      (arrow-sigma G₁ G₂)
      (arrow-sigma H₁ H₂)
  compose-sigma j₁ j₂
    = record {ComposeSigma j₁ j₂}

-- ### ComposeEqual

module _
  {X₁ Y₁ Z₁ : Object'}
  {X₂ : DependentObject₁ X₁}
  {Y₂ : DependentObject₁ Y₁}
  {Z₂ : DependentObject₁ Z₁}
  {F₁ : Arrow' Y₁ Z₁}
  {G₁ : Arrow' X₁ Y₁}
  {H₁ : Arrow' X₁ Z₁}
  {F₂ : DependentArrow₁ Y₂ Z₂}
  {G₂ : DependentArrow₁ X₂ Y₂}
  {H₂ : DependentArrow₁ X₂ Z₂}
  {j₁ : Compose F₁ G₁ H₁}
  {j₂ : DependentCompose₁ F₂ G₂ H₂}
  where

  module ComposeEqualSigma
    (p₁ : ComposeEqual j₁)
    (p₂ : DependentComposeEqual₁ j₂)
    where

    compose-equal
      : {x : Object'.Object (object-sigma X₂)}
      → {y : Object'.Object (object-sigma Y₂)}
      → {z : Object'.Object (object-sigma Z₂)}
      → {f₁ f₂ : Arrow'.Arrow (arrow-sigma F₁ F₂) y z}
      → {g₁ g₂ : Arrow'.Arrow (arrow-sigma G₁ G₂) x y}
      → Arrow'.ArrowEqual (arrow-sigma F₁ F₂) f₁ f₂
      → Arrow'.ArrowEqual (arrow-sigma G₁ G₂) g₁ g₂
      → Arrow'.ArrowEqual (arrow-sigma H₁ H₂)
        (Compose.compose (compose-sigma j₁ j₂) f₁ g₁)
        (Compose.compose (compose-sigma j₁ j₂) f₂ g₂)
    compose-equal (ArrowSigma.arrow₁ q₁) (ArrowSigma.arrow₁ r₁)
      = ArrowSigma.arrow₁
        (ComposeEqual.compose-equal p₁ q₁ r₁)
    compose-equal (ArrowSigma.arrow₁ q₁) (ArrowSigma.arrow₂ r₁ _)
      = ArrowSigma.arrow₁
        (ComposeEqual.compose-equal p₁ q₁ r₁)
    compose-equal (ArrowSigma.arrow₂ q₁ _) (ArrowSigma.arrow₁ r₁)
      = ArrowSigma.arrow₁
        (ComposeEqual.compose-equal p₁ q₁ r₁)
    compose-equal (ArrowSigma.arrow₂ q₁ q₂) (ArrowSigma.arrow₂ r₁ r₂)
      = ArrowSigma.arrow₂
        (ComposeEqual.compose-equal p₁ q₁ r₁)
        (DependentComposeEqual₁.compose-equal p₂ q₂ r₂)

  compose-equal-sigma
    : ComposeEqual j₁
    → DependentComposeEqual₁ j₂
    → ComposeEqual
      (compose-sigma j₁ j₂)
  compose-equal-sigma p₁ p₂
    = record {ComposeEqualSigma p₁ p₂}

-- ### Precompose

module _
  {X₁ Y₁ : Object'}
  {X₂ : DependentObject₁ X₁}
  {Y₂ : DependentObject₁ Y₁}
  {F₁ : Arrow' X₁ Y₁}
  {G₁ : Arrow' X₁ X₁}
  {F₂ : DependentArrow₁ X₂ Y₂}
  {G₂ : DependentArrow₁ X₂ X₂}
  {i₁ : Identity G₁}
  {i₂ : DependentIdentity₁ G₂}
  {j₁ : Compose F₁ G₁ F₁}
  {j₂ : DependentCompose₁ F₂ G₂ F₂}
  where

  module PrecomposeSigma
    (p₁ : Precompose i₁ j₁)
    (p₂ : DependentPrecompose₁ i₂ j₂)
    where

    precompose
      : {x : Object'.Object (object-sigma X₂)}
      → {y : Object'.Object (object-sigma Y₂)}
      → (f : Arrow'.Arrow (arrow-sigma F₁ F₂) x y)
      → Arrow'.ArrowEqual (arrow-sigma F₁ F₂)
        (Compose.compose (compose-sigma j₁ j₂) f
          (Identity.identity (identity-sigma i₁ i₂) x)) f
    precompose (ArrowSigma.arrow₁ f₁)
      = ArrowSigma.arrow₁
        (Precompose.precompose p₁ f₁)
    precompose (ArrowSigma.arrow₂ f₁ f₂)
      = ArrowSigma.arrow₂
        (Precompose.precompose p₁ f₁)
        (DependentPrecompose₁.precompose p₂ f₂)

  precompose-sigma
    : Precompose i₁ j₁
    → DependentPrecompose₁ i₂ j₂
    → Precompose
      (identity-sigma i₁ i₂)
      (compose-sigma j₁ j₂)
  precompose-sigma p₁ p₂
    = record {PrecomposeSigma p₁ p₂}

-- ### Postcompose

module _
  {X₁ Y₁ : Object'}
  {X₂ : DependentObject₁ X₁}
  {Y₂ : DependentObject₁ Y₁}
  {F₁ : Arrow' Y₁ Y₁}
  {G₁ : Arrow' X₁ Y₁}
  {F₂ : DependentArrow₁ Y₂ Y₂}
  {G₂ : DependentArrow₁ X₂ Y₂}
  {i₁ : Identity F₁}
  {i₂ : DependentIdentity₁ F₂}
  {j₁ : Compose F₁ G₁ G₁}
  {j₂ : DependentCompose₁ F₂ G₂ G₂}
  where
  
  module PostcomposeSigma
    (p₁ : Postcompose i₁ j₁)
    (p₂ : DependentPostcompose₁ i₂ j₂)
    where

    postcompose
      : {x : Object'.Object (object-sigma X₂)}
      → {y : Object'.Object (object-sigma Y₂)}
      → (g : Arrow'.Arrow (arrow-sigma G₁ G₂) x y)
      → Arrow'.ArrowEqual (arrow-sigma G₁ G₂)
        (Compose.compose (compose-sigma j₁ j₂)
          (Identity.identity (identity-sigma i₁ i₂) y) g) g
    postcompose (ArrowSigma.arrow₁ f₁)
      = ArrowSigma.arrow₁
        (Postcompose.postcompose p₁ f₁)
    postcompose (ArrowSigma.arrow₂ f₁ f₂)
      = ArrowSigma.arrow₂
        (Postcompose.postcompose p₁ f₁)
        (DependentPostcompose₁.postcompose p₂ f₂)

  postcompose-sigma
    : Postcompose i₁ j₁
    → DependentPostcompose₁ i₂ j₂
    → Postcompose
      (identity-sigma i₁ i₂)
      (compose-sigma j₁ j₂)
  postcompose-sigma p₁ p₂
    = record {PostcomposeSigma p₁ p₂}

-- ### Associative

module _
  {W₁ X₁ Y₁ Z₁ : Object'}
  {W₂ : DependentObject₁ W₁}
  {X₂ : DependentObject₁ X₁}
  {Y₂ : DependentObject₁ Y₁}
  {Z₂ : DependentObject₁ Z₁}
  {F₁ : Arrow' Y₁ Z₁}
  {G₁ : Arrow' X₁ Y₁}
  {H₁ : Arrow' W₁ X₁}
  {I₁ : Arrow' X₁ Z₁}
  {J₁ : Arrow' W₁ Y₁}
  {K₁ : Arrow' W₁ Z₁}
  {F₂ : DependentArrow₁ Y₂ Z₂}
  {G₂ : DependentArrow₁ X₂ Y₂}
  {H₂ : DependentArrow₁ W₂ X₂}
  {I₂ : DependentArrow₁ X₂ Z₂}
  {J₂ : DependentArrow₁ W₂ Y₂}
  {K₂ : DependentArrow₁ W₂ Z₂}
  {j₁ : Compose F₁ G₁ I₁}
  {k₁ : Compose G₁ H₁ J₁}
  {l₁ : Compose I₁ H₁ K₁}
  {m₁ : Compose F₁ J₁ K₁}
  {j₂ : DependentCompose₁ F₂ G₂ I₂}
  {k₂ : DependentCompose₁ G₂ H₂ J₂}
  {l₂ : DependentCompose₁ I₂ H₂ K₂}
  {m₂ : DependentCompose₁ F₂ J₂ K₂}
  where

  module AssociativeSigma
    (p₁ : Associative j₁ k₁ l₁ m₁)
    (p₂ : DependentAssociative₁ j₂ k₂ l₂ m₂)
    where

    associative
      : {w : Object'.Object (object-sigma W₂)}
      → {x : Object'.Object (object-sigma X₂)}
      → {y : Object'.Object (object-sigma Y₂)}
      → {z : Object'.Object (object-sigma Z₂)}
      → (f : Arrow'.Arrow (arrow-sigma F₁ F₂) y z)
      → (g : Arrow'.Arrow (arrow-sigma G₁ G₂) x y)
      → (h : Arrow'.Arrow (arrow-sigma H₁ H₂) w x)
      → Arrow'.ArrowEqual (arrow-sigma K₁ K₂)
        (Compose.compose (compose-sigma l₁ l₂)
          (Compose.compose (compose-sigma j₁ j₂) f g) h)
        (Compose.compose (compose-sigma m₁ m₂) f
          (Compose.compose (compose-sigma k₁ k₂) g h))
    associative
      (ArrowSigma.arrow₁ f₁)
      (ArrowSigma.arrow₁ g₁)
      (ArrowSigma.arrow₁ h₁)
      = ArrowSigma.arrow₁
        (Associative.associative p₁ f₁ g₁ h₁)
    associative
      (ArrowSigma.arrow₁ f₁)
      (ArrowSigma.arrow₁ g₁)
      (ArrowSigma.arrow₂ h₁ _)
      = ArrowSigma.arrow₁
        (Associative.associative p₁ f₁ g₁ h₁)
    associative
      (ArrowSigma.arrow₁ f₁)
      (ArrowSigma.arrow₂ g₁ _)
      (ArrowSigma.arrow₁ h₁)
      = ArrowSigma.arrow₁
        (Associative.associative p₁ f₁ g₁ h₁)
    associative
      (ArrowSigma.arrow₁ f₁)
      (ArrowSigma.arrow₂ g₁ _)
      (ArrowSigma.arrow₂ h₁ _)
      = ArrowSigma.arrow₁
        (Associative.associative p₁ f₁ g₁ h₁)
    associative
      (ArrowSigma.arrow₂ f₁ _)
      (ArrowSigma.arrow₁ g₁)
      (ArrowSigma.arrow₁ h₁)
      = ArrowSigma.arrow₁
        (Associative.associative p₁ f₁ g₁ h₁)
    associative
      (ArrowSigma.arrow₂ f₁ _)
      (ArrowSigma.arrow₁ g₁)
      (ArrowSigma.arrow₂ h₁ _)
      = ArrowSigma.arrow₁
        (Associative.associative p₁ f₁ g₁ h₁)
    associative
      (ArrowSigma.arrow₂ f₁ _)
      (ArrowSigma.arrow₂ g₁ _)
      (ArrowSigma.arrow₁ h₁)
      = ArrowSigma.arrow₁
        (Associative.associative p₁ f₁ g₁ h₁)
    associative
      (ArrowSigma.arrow₂ f₁ f₂)
      (ArrowSigma.arrow₂ g₁ g₂)
      (ArrowSigma.arrow₂ h₁ h₂)
      = ArrowSigma.arrow₂
        (Associative.associative p₁ f₁ g₁ h₁)
        (DependentAssociative₁.associative p₂ f₂ g₂ h₂)

  associative-sigma
    : Associative j₁ k₁ l₁ m₁
    → DependentAssociative₁ j₂ k₂ l₂ m₂
    → Associative
      (compose-sigma j₁ j₂)
      (compose-sigma k₁ k₂)
      (compose-sigma l₁ l₂)
      (compose-sigma m₁ m₂)
  associative-sigma p₁ p₂
    = record {AssociativeSigma p₁ p₂}

-- ## Dependent

-- ### DependentObject

dependent-object-sigma
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' : DependentObject X}
  → DependentObject (chain-object-snoc X₁')
  → DependentObject X
dependent-object-sigma {n = zero} X₂'
  = object-sigma X₂'
dependent-object-sigma {n = suc _} X₂'
  = record
  { tail
    = λ x → dependent-object-sigma
      (DependentObject.tail X₂' x)
  }

-- ### DependentArrow

dependent-arrow-sigma
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' : DependentObject X}
  → {Y₁' : DependentObject Y}
  → {X₂' : DependentObject (chain-object-snoc X₁')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁')}
  → DependentArrow X₁' Y₁'
  → DependentArrow X₂' Y₂'
  → DependentArrow
    (dependent-object-sigma X₂')
    (dependent-object-sigma Y₂')
dependent-arrow-sigma {n = zero} F₁ F₂
  = arrow-sigma F₁ F₂
dependent-arrow-sigma {n = suc _} F₁ F₂
  = record
  { tail
    = λ x y → dependent-arrow-sigma
      (DependentArrow.tail F₁ x y)
      (DependentArrow.tail F₂ x y)
  }

-- ### DependentIdentity

dependent-identity-sigma
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' : DependentObject X}
  → {X₂' : DependentObject (chain-object-snoc X₁')}
  → {F₁ : DependentArrow X₁' X₁'}
  → {F₂ : DependentArrow X₂' X₂'}
  → DependentIdentity F₁
  → DependentIdentity F₂
  → DependentIdentity
    (dependent-arrow-sigma F₁ F₂)
dependent-identity-sigma {n = zero} i₁ i₂
  = identity-sigma i₁ i₂
dependent-identity-sigma {n = suc _} i₁ i₂
  = record
  { tail
    = λ x → dependent-identity-sigma
      (DependentIdentity.tail i₁ x)
      (DependentIdentity.tail i₂ x)
  }

-- ### DependentCompose

dependent-compose-sigma
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X₁' : DependentObject X}
  → {Y₁' : DependentObject Y}
  → {Z₁' : DependentObject Z}
  → {X₂' : DependentObject (chain-object-snoc X₁')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁')}
  → {Z₂' : DependentObject (chain-object-snoc Z₁')}
  → {F₁ : DependentArrow Y₁' Z₁'}
  → {G₁ : DependentArrow X₁' Y₁'}
  → {H₁ : DependentArrow X₁' Z₁'}
  → {F₂ : DependentArrow Y₂' Z₂'}
  → {G₂ : DependentArrow X₂' Y₂'}
  → {H₂ : DependentArrow X₂' Z₂'}
  → DependentCompose F₁ G₁ H₁
  → DependentCompose F₂ G₂ H₂
  → DependentCompose
    (dependent-arrow-sigma F₁ F₂)
    (dependent-arrow-sigma G₁ G₂)
    (dependent-arrow-sigma H₁ H₂)
dependent-compose-sigma {n = zero} j₁ j₂
  = compose-sigma j₁ j₂
dependent-compose-sigma {n = suc _} j₁ j₂
  = record
  { tail
    = λ x y z → dependent-compose-sigma
      (DependentCompose.tail j₁ x y z)
      (DependentCompose.tail j₂ x y z)
  }

-- ### DependentComposeEqual

dependent-compose-equal-sigma
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X₁' : DependentObject X}
  → {Y₁' : DependentObject Y}
  → {Z₁' : DependentObject Z}
  → {X₂' : DependentObject (chain-object-snoc X₁')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁')}
  → {Z₂' : DependentObject (chain-object-snoc Z₁')}
  → {F₁ : DependentArrow Y₁' Z₁'}
  → {G₁ : DependentArrow X₁' Y₁'}
  → {H₁ : DependentArrow X₁' Z₁'}
  → {F₂ : DependentArrow Y₂' Z₂'}
  → {G₂ : DependentArrow X₂' Y₂'}
  → {H₂ : DependentArrow X₂' Z₂'}
  → {j₁ : DependentCompose F₁ G₁ H₁}
  → {j₂ : DependentCompose F₂ G₂ H₂}
  → DependentComposeEqual j₁
  → DependentComposeEqual j₂
  → DependentComposeEqual
    (dependent-compose-sigma j₁ j₂)
dependent-compose-equal-sigma {n = zero} p₁ p₂
  = compose-equal-sigma p₁ p₂
dependent-compose-equal-sigma {n = suc _} p₁ p₂
  = record
  { tail
    = λ x y z → dependent-compose-equal-sigma
      (DependentComposeEqual.tail p₁ x y z)
      (DependentComposeEqual.tail p₂ x y z)
  }

-- ### DependentPrecompose

dependent-precompose-sigma
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' : DependentObject X}
  → {Y₁' : DependentObject Y}
  → {X₂' : DependentObject (chain-object-snoc X₁')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁')}
  → {F₁ : DependentArrow X₁' Y₁'}
  → {G₁ : DependentArrow X₁' X₁'}
  → {F₂ : DependentArrow X₂' Y₂'}
  → {G₂ : DependentArrow X₂' X₂'}
  → {i₁ : DependentIdentity G₁}
  → {i₂ : DependentIdentity G₂}
  → {j₁ : DependentCompose F₁ G₁ F₁}
  → {j₂ : DependentCompose F₂ G₂ F₂}
  → DependentPrecompose i₁ j₁
  → DependentPrecompose i₂ j₂
  → DependentPrecompose
    (dependent-identity-sigma i₁ i₂)
    (dependent-compose-sigma j₁ j₂)
dependent-precompose-sigma {n = zero} p₁ p₂
  = precompose-sigma p₁ p₂
dependent-precompose-sigma {n = suc _} p₁ p₂
  = record
  { tail
    = λ x y → dependent-precompose-sigma
      (DependentPrecompose.tail p₁ x y)
      (DependentPrecompose.tail p₂ x y)
  }

-- ### DependentPostcompose

dependent-postcompose-sigma
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' : DependentObject X}
  → {Y₁' : DependentObject Y}
  → {X₂' : DependentObject (chain-object-snoc X₁')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁')}
  → {F₁ : DependentArrow Y₁' Y₁'}
  → {G₁ : DependentArrow X₁' Y₁'}
  → {F₂ : DependentArrow Y₂' Y₂'}
  → {G₂ : DependentArrow X₂' Y₂'}
  → {i₁ : DependentIdentity F₁}
  → {i₂ : DependentIdentity F₂}
  → {j₁ : DependentCompose F₁ G₁ G₁}
  → {j₂ : DependentCompose F₂ G₂ G₂}
  → DependentPostcompose i₁ j₁
  → DependentPostcompose i₂ j₂
  → DependentPostcompose
    (dependent-identity-sigma i₁ i₂)
    (dependent-compose-sigma j₁ j₂)
dependent-postcompose-sigma {n = zero} p₁ p₂
  = postcompose-sigma p₁ p₂
dependent-postcompose-sigma {n = suc _} p₁ p₂
  = record
  { tail
    = λ x y → dependent-postcompose-sigma
      (DependentPostcompose.tail p₁ x y)
      (DependentPostcompose.tail p₂ x y)
  }

-- ### DependentAssociative

dependent-associative-sigma
  : {n : ℕ}
  → {W X Y Z : ChainObject n}
  → {W₁' : DependentObject W}
  → {X₁' : DependentObject X}
  → {Y₁' : DependentObject Y}
  → {Z₁' : DependentObject Z}
  → {W₂' : DependentObject (chain-object-snoc W₁')}
  → {X₂' : DependentObject (chain-object-snoc X₁')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁')}
  → {Z₂' : DependentObject (chain-object-snoc Z₁')}
  → {F₁ : DependentArrow Y₁' Z₁'}
  → {G₁ : DependentArrow X₁' Y₁'}
  → {H₁ : DependentArrow W₁' X₁'}
  → {I₁ : DependentArrow X₁' Z₁'}
  → {J₁ : DependentArrow W₁' Y₁'}
  → {K₁ : DependentArrow W₁' Z₁'}
  → {F₂ : DependentArrow Y₂' Z₂'}
  → {G₂ : DependentArrow X₂' Y₂'}
  → {H₂ : DependentArrow W₂' X₂'}
  → {I₂ : DependentArrow X₂' Z₂'}
  → {J₂ : DependentArrow W₂' Y₂'}
  → {K₂ : DependentArrow W₂' Z₂'}
  → {j₁ : DependentCompose F₁ G₁ I₁}
  → {k₁ : DependentCompose G₁ H₁ J₁}
  → {l₁ : DependentCompose I₁ H₁ K₁}
  → {m₁ : DependentCompose F₁ J₁ K₁}
  → {j₂ : DependentCompose F₂ G₂ I₂}
  → {k₂ : DependentCompose G₂ H₂ J₂}
  → {l₂ : DependentCompose I₂ H₂ K₂}
  → {m₂ : DependentCompose F₂ J₂ K₂}
  → DependentAssociative j₁ k₁ l₁ m₁
  → DependentAssociative j₂ k₂ l₂ m₂
  → DependentAssociative
    (dependent-compose-sigma j₁ j₂)
    (dependent-compose-sigma k₁ k₂)
    (dependent-compose-sigma l₁ l₂)
    (dependent-compose-sigma m₁ m₂)
dependent-associative-sigma {n = zero} p₁ p₂
  = associative-sigma p₁ p₂
dependent-associative-sigma {n = suc _} p₁ p₂
  = record
  { tail
    = λ w x y z → dependent-associative-sigma
      (DependentAssociative.tail p₁ w x y z)
      (DependentAssociative.tail p₂ w x y z)
  }

