module Category.Core.Sigma.Sum where

open import Category.Core
  using (Arrow'; Associative; ChainObject; Compose; ComposeEqual;
    DependentArrow; DependentArrow₁; DependentAssociative;
    DependentAssociative₁; DependentCompose; DependentCompose₁;
    DependentComposeEqual; DependentComposeEqual₁; DependentIdentity;
    DependentIdentity₁; DependentObject; DependentObject₁; DependentPostcompose;
    DependentPostcompose₁; DependentPrecompose; DependentPrecompose₁;
    DependentSimplify; DependentSimplify₁; Identity; Object'; Postcompose;
    Precompose; Simplify)
open import Category.Core.Sigma
  using (object-sigma)
open import Category.Core.Snoc
  using (chain-object-snoc)
open import Category.Split.Core
  using (SplitBase; DependentSplitBase)
open import Data.Equal
  using (_≡_; refl)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (_,_)
open import Data.Sum
  using (_⊔_; ι₁; ι₂)

-- ## Base

-- ### Object' 

object-sigma-sum
  : Object'
  → {X₁' : Object'}
  → DependentObject₁ X₁'
  → Object'
object-sigma-sum X₁ X₂
  = record
  { Object
    = Object'.Object X₁
    ⊔ Object'.Object (object-sigma X₂)
  }

object-sigma-sum₁
  : {X₁ X₁' : Object'}
  → (X₂ : DependentObject₁ X₁')
  → SplitBase X₁ X₁'
  → Object'.Object (object-sigma-sum X₁ X₂)
  → Object'.Object X₁
object-sigma-sum₁ _ _ (ι₁ x₁)
  = x₁
object-sigma-sum₁ _ a₁ (ι₂ (x₁ , _))
  = SplitBase.unbase a₁ x₁

-- ### Arrow'

-- #### Function

module _
  {X₁ Y₁ X₁' Y₁' : Object'}
  {X₂ : DependentObject₁ X₁'}
  {Y₂ : DependentObject₁ Y₁'}
  where

  module ArrowSigmaSum
    (F₁ : Arrow' X₁ Y₁)
    (F₂ : DependentArrow₁ X₂ Y₂)
    (a₁ : SplitBase X₁ X₁')
    (b₁ : SplitBase Y₁ Y₁')
    where

    data Arrow
      : Object'.Object (object-sigma-sum X₁ X₂)
      → Object'.Object (object-sigma-sum Y₁ Y₂)
      → Set
      where

      arrow₁
        : {x : Object'.Object (object-sigma-sum X₁ X₂)}
        → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
        → Arrow'.Arrow F₁
          (object-sigma-sum₁ X₂ a₁ x)
          (object-sigma-sum₁ Y₂ b₁ y)
        → Arrow x y

      arrow₂
        : {x₁ : Object'.Object X₁'}
        → {y₁ : Object'.Object Y₁'}
        → {x₂ : DependentObject₁.Object X₂ x₁}
        → {y₂ : DependentObject₁.Object Y₂ y₁}
        → Arrow'.Arrow F₁
          (SplitBase.unbase a₁ x₁)
          (SplitBase.unbase b₁ y₁)
        → DependentArrow₁.Arrow F₂ x₂ y₂
        → Arrow (ι₂ (x₁ , x₂)) (ι₂ (y₁ , y₂))

    data ArrowEqual
      : {x : Object'.Object (object-sigma-sum X₁ X₂)}
      → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
      → Arrow x y
      → Arrow x y
      → Set
      where

      arrow₁
        : {x : Object'.Object (object-sigma-sum X₁ X₂)}
        → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
        → {f₁₁ f₂₁ : Arrow'.Arrow F₁
          (object-sigma-sum₁ X₂ a₁ x)
          (object-sigma-sum₁ Y₂ b₁ y)}
        → Arrow'.ArrowEqual F₁ f₁₁ f₂₁
        → ArrowEqual {x = x} {y = y} (arrow₁ f₁₁) (arrow₁ f₂₁)

      arrow₂
        : {x₁ : Object'.Object X₁'}
        → {y₁ : Object'.Object Y₁'}
        → {x₂ : DependentObject₁.Object X₂ x₁}
        → {y₂ : DependentObject₁.Object Y₂ y₁}
        → {f₁₁ f₂₁ : Arrow'.Arrow F₁
          (SplitBase.unbase a₁ x₁)
          (SplitBase.unbase b₁ y₁)}
        → {f₁₂ f₂₂ : DependentArrow₁.Arrow F₂ x₂ y₂}
        → Arrow'.ArrowEqual F₁ f₁₁ f₂₁
        → DependentArrow₁.ArrowEqual F₂ f₁₂ f₂₂
        → ArrowEqual (arrow₂ f₁₁ f₁₂) (arrow₂ f₂₁ f₂₂)

    arrow-refl
      : {x : Object'.Object (object-sigma-sum X₁ X₂)}
      → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
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
      : {x : Object'.Object (object-sigma-sum X₁ X₂)}
      → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
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
      : {x : Object'.Object (object-sigma-sum X₁ X₂)}
      → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
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
    
  arrow-sigma-sum
    : Arrow' X₁ Y₁
    → DependentArrow₁ X₂ Y₂
    → SplitBase X₁ X₁'
    → SplitBase Y₁ Y₁'
    → Arrow'
      (object-sigma-sum X₁ X₂)
      (object-sigma-sum Y₁ Y₂)
  arrow-sigma-sum F₁ F₂ a₁ b₁
    = record {ArrowSigmaSum F₁ F₂ a₁ b₁}

-- #### Equality

module _
  {X₁ Y₁ X₁' Y₁' : Object'}
  {X₂ : DependentObject₁ X₁'}
  {Y₂ : DependentObject₁ Y₁'}
  {F₁ : Arrow' X₁ Y₁}
  where

  arrow-equal-sigma-sum₁
    : (F₂ : DependentArrow₁ X₂ Y₂)
    → (a₁ : SplitBase X₁ X₁')
    → (b₁ : SplitBase Y₁ Y₁')
    → {x₁ x₂ : Object'.Object (object-sigma-sum X₁ X₂)}
    → {y₁ y₂ : Object'.Object (object-sigma-sum Y₁ Y₂)}
    → {f₁₁ : Arrow'.Arrow F₁
      (object-sigma-sum₁ X₂ a₁ x₁)
      (object-sigma-sum₁ Y₂ b₁ y₁)}
    → {f₂₁ : Arrow'.Arrow F₁
      (object-sigma-sum₁ X₂ a₁ x₂)
      (object-sigma-sum₁ Y₂ b₁ y₂)}
    → x₁ ≡ x₂
    → y₁ ≡ y₂
    → Arrow'.ArrowEqual' F₁ f₁₁ f₂₁
    → Arrow'.ArrowEqual'
      (arrow-sigma-sum F₁ F₂ a₁ b₁) {x₁ = x₁} {x₂ = x₂} {y₁ = y₁} {y₂ = y₂}
      (ArrowSigmaSum.arrow₁ f₁₁)
      (ArrowSigmaSum.arrow₁ f₂₁)
  arrow-equal-sigma-sum₁ _ _ _ refl refl (Arrow'.arrow-equal p₁)
    = Arrow'.arrow-equal
    $ ArrowSigmaSum.arrow₁ p₁

  arrow-equal-sigma-sum₂
    : {F₂ : DependentArrow₁ X₂ Y₂}
    → (a₁ : SplitBase X₁ X₁')
    → (b₁ : SplitBase Y₁ Y₁')
    → {x₁ : Object'.Object X₁'}
    → {y₁ : Object'.Object Y₁'}
    → {x₁₂ : DependentObject₁.Object X₂ x₁}
    → {x₂₂ : DependentObject₁.Object X₂ x₁}
    → {y₁₂ : DependentObject₁.Object Y₂ y₁}
    → {y₂₂ : DependentObject₁.Object Y₂ y₁}
    → {f₁₁ f₂₁ : Arrow'.Arrow F₁
      (SplitBase.unbase a₁ x₁)
      (SplitBase.unbase b₁ y₁)}
    → {f₁₂ : DependentArrow₁.Arrow F₂ x₁₂ y₁₂}
    → {f₂₂ : DependentArrow₁.Arrow F₂ x₂₂ y₂₂}
    → Arrow'.ArrowEqual F₁ f₁₁ f₂₁
    → DependentArrow₁.ArrowEqual' F₂ f₁₂ f₂₂
    → Arrow'.ArrowEqual'
      (arrow-sigma-sum F₁ F₂ a₁ b₁)
      (ArrowSigmaSum.arrow₂ f₁₁ f₁₂)
      (ArrowSigmaSum.arrow₂ f₂₁ f₂₂)
  arrow-equal-sigma-sum₂ _ _ p₁ (Arrow'.arrow-equal p₂)
    = Arrow'.arrow-equal
    $ ArrowSigmaSum.arrow₂ p₁ p₂

-- ### Simplify

module _
  {X₁ Y₁ X₁' Y₁' : Object'}
  {X₂ : DependentObject₁ X₁'}
  {Y₂ : DependentObject₁ Y₁'}
  {F₁ : Arrow' X₁ Y₁}
  {F₂ : DependentArrow₁ X₂ Y₂}
  where

  module SimplifySigmaSum
    (s₁ : Simplify F₁)
    (s₂ : DependentSimplify₁ F₂)
    (a₁ : SplitBase X₁ X₁')
    (b₁ : SplitBase Y₁ Y₁')
    where

    simplify
      : {x : Object'.Object (object-sigma-sum X₁ X₂)}
      → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
      → Arrow'.Arrow (arrow-sigma-sum F₁ F₂ a₁ b₁) x y
      → Arrow'.Arrow (arrow-sigma-sum F₁ F₂ a₁ b₁) x y
    simplify (ArrowSigmaSum.arrow₁ f₁)
      = ArrowSigmaSum.arrow₁
        (Simplify.simplify s₁ f₁)
    simplify (ArrowSigmaSum.arrow₂ f₁ f₂)
      = ArrowSigmaSum.arrow₂
        (Simplify.simplify s₁ f₁)
        (DependentSimplify₁.simplify s₂ f₂)

    simplify-equal
      : {x : Object'.Object (object-sigma-sum X₁ X₂)}
      → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
      → (f : Arrow'.Arrow (arrow-sigma-sum F₁ F₂ a₁ b₁) x y)
      → Arrow'.ArrowEqual (arrow-sigma-sum F₁ F₂ a₁ b₁) (simplify f) f
    simplify-equal (ArrowSigmaSum.arrow₁ f₁)
      = ArrowSigmaSum.arrow₁
        (Simplify.simplify-equal s₁ f₁)
    simplify-equal (ArrowSigmaSum.arrow₂ f₁ f₂)
      = ArrowSigmaSum.arrow₂
        (Simplify.simplify-equal s₁ f₁)
        (DependentSimplify₁.simplify-equal s₂ f₂)

  simplify-sigma-sum
    : Simplify F₁
    → DependentSimplify₁ F₂
    → (a₁ : SplitBase X₁ X₁')
    → (b₁ : SplitBase Y₁ Y₁')
    → Simplify
      (arrow-sigma-sum F₁ F₂ a₁ b₁)
  simplify-sigma-sum s₁ s₂ a₁ b₁
    = record {SimplifySigmaSum s₁ s₂ a₁ b₁}

-- ### Identity

module _
  {X₁ X₁' : Object'}
  {X₂ : DependentObject₁ X₁'}
  {F₁ : Arrow' X₁ X₁}
  {F₂ : DependentArrow₁ X₂ X₂}
  where

  module IdentitySigmaSum
    (i₁ : Identity F₁)
    (i₂ : DependentIdentity₁ F₂)
    (a₁ : SplitBase X₁ X₁')
    where

    identity
      : (x : Object'.Object (object-sigma-sum X₁ X₂))
      → Arrow'.Arrow (arrow-sigma-sum F₁ F₂ a₁ a₁) x x
    identity (ι₁ x₁)
      = ArrowSigmaSum.arrow₁
        (Identity.identity i₁ x₁)
    identity (ι₂ (x₁ , x₂))
      = ArrowSigmaSum.arrow₂
        (Identity.identity i₁ (SplitBase.unbase a₁ x₁))
        (DependentIdentity₁.identity i₂ x₂)

  identity-sigma-sum
    : Identity F₁
    → DependentIdentity₁ F₂
    → (a₁ : SplitBase X₁ X₁')
    → Identity
      (arrow-sigma-sum F₁ F₂ a₁ a₁)
  identity-sigma-sum i₁ i₂ a₁
    = record {IdentitySigmaSum i₁ i₂ a₁}

-- ### Compose

module _
  {X₁ Y₁ Z₁ X₁' Y₁' Z₁' : Object'}
  {X₂ : DependentObject₁ X₁'}
  {Y₂ : DependentObject₁ Y₁'}
  {Z₂ : DependentObject₁ Z₁'}
  {F₁ : Arrow' Y₁ Z₁}
  {G₁ : Arrow' X₁ Y₁}
  {H₁ : Arrow' X₁ Z₁}
  {F₂ : DependentArrow₁ Y₂ Z₂}
  {G₂ : DependentArrow₁ X₂ Y₂}
  {H₂ : DependentArrow₁ X₂ Z₂}
  where

  module ComposeSigmaSum
    (j₁ : Compose F₁ G₁ H₁)
    (j₂ : DependentCompose₁ F₂ G₂ H₂)
    (a₁ : SplitBase X₁ X₁')
    (b₁ : SplitBase Y₁ Y₁')
    (c₁ : SplitBase Z₁ Z₁')
    where

    compose
      : {x : Object'.Object (object-sigma-sum X₁ X₂)}
      → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
      → {z : Object'.Object (object-sigma-sum Z₁ Z₂)}
      → Arrow'.Arrow (arrow-sigma-sum F₁ F₂ b₁ c₁) y z
      → Arrow'.Arrow (arrow-sigma-sum G₁ G₂ a₁ b₁) x y
      → Arrow'.Arrow (arrow-sigma-sum H₁ H₂ a₁ c₁) x z
    compose (ArrowSigmaSum.arrow₁ f₁) (ArrowSigmaSum.arrow₁ g₁)
      = ArrowSigmaSum.arrow₁
        (Compose.compose j₁ f₁ g₁)
    compose (ArrowSigmaSum.arrow₁ f₁) (ArrowSigmaSum.arrow₂ g₁ _)
      = ArrowSigmaSum.arrow₁
        (Compose.compose j₁ f₁ g₁)
    compose (ArrowSigmaSum.arrow₂ f₁ _) (ArrowSigmaSum.arrow₁ g₁)
      = ArrowSigmaSum.arrow₁
        (Compose.compose j₁ f₁ g₁)
    compose (ArrowSigmaSum.arrow₂ f₁ f₂) (ArrowSigmaSum.arrow₂ g₁ g₂)
      = ArrowSigmaSum.arrow₂
        (Compose.compose j₁ f₁ g₁)
        (DependentCompose₁.compose j₂ f₂ g₂)

  compose-sigma-sum
    : Compose F₁ G₁ H₁
    → DependentCompose₁ F₂ G₂ H₂
    → (a₁ : SplitBase X₁ X₁')
    → (b₁ : SplitBase Y₁ Y₁')
    → (c₁ : SplitBase Z₁ Z₁')
    → Compose
      (arrow-sigma-sum F₁ F₂ b₁ c₁)
      (arrow-sigma-sum G₁ G₂ a₁ b₁)
      (arrow-sigma-sum H₁ H₂ a₁ c₁)
  compose-sigma-sum j₁ j₂ a₁ b₁ c₁
    = record {ComposeSigmaSum j₁ j₂ a₁ b₁ c₁}

-- ### ComposeEqual

module _
  {X₁ Y₁ Z₁ X₁' Y₁' Z₁' : Object'}
  {X₂ : DependentObject₁ X₁'}
  {Y₂ : DependentObject₁ Y₁'}
  {Z₂ : DependentObject₁ Z₁'}
  {F₁ : Arrow' Y₁ Z₁}
  {G₁ : Arrow' X₁ Y₁}
  {H₁ : Arrow' X₁ Z₁}
  {F₂ : DependentArrow₁ Y₂ Z₂}
  {G₂ : DependentArrow₁ X₂ Y₂}
  {H₂ : DependentArrow₁ X₂ Z₂}
  {j₁ : Compose F₁ G₁ H₁}
  {j₂ : DependentCompose₁ F₂ G₂ H₂}
  where

  module ComposeEqualSigmaSum
    (p₁ : ComposeEqual j₁)
    (p₂ : DependentComposeEqual₁ j₂)
    (a₁ : SplitBase X₁ X₁')
    (b₁ : SplitBase Y₁ Y₁')
    (c₁ : SplitBase Z₁ Z₁')
    where

    compose-equal
      : {x : Object'.Object (object-sigma-sum X₁ X₂)}
      → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
      → {z : Object'.Object (object-sigma-sum Z₁ Z₂)}
      → {f₁ f₂ : Arrow'.Arrow (arrow-sigma-sum F₁ F₂ b₁ c₁) y z}
      → {g₁ g₂ : Arrow'.Arrow (arrow-sigma-sum G₁ G₂ a₁ b₁) x y}
      → Arrow'.ArrowEqual (arrow-sigma-sum F₁ F₂ b₁ c₁) f₁ f₂
      → Arrow'.ArrowEqual (arrow-sigma-sum G₁ G₂ a₁ b₁) g₁ g₂
      → Arrow'.ArrowEqual (arrow-sigma-sum H₁ H₂ a₁ c₁)
        (Compose.compose (compose-sigma-sum j₁ j₂ a₁ b₁ c₁) f₁ g₁)
        (Compose.compose (compose-sigma-sum j₁ j₂ a₁ b₁ c₁) f₂ g₂)
    compose-equal (ArrowSigmaSum.arrow₁ q₁) (ArrowSigmaSum.arrow₁ r₁)
      = ArrowSigmaSum.arrow₁
        (ComposeEqual.compose-equal p₁ q₁ r₁)
    compose-equal (ArrowSigmaSum.arrow₁ q₁) (ArrowSigmaSum.arrow₂ r₁ _)
      = ArrowSigmaSum.arrow₁
        (ComposeEqual.compose-equal p₁ q₁ r₁)
    compose-equal (ArrowSigmaSum.arrow₂ q₁ _) (ArrowSigmaSum.arrow₁ r₁)
      = ArrowSigmaSum.arrow₁
        (ComposeEqual.compose-equal p₁ q₁ r₁)
    compose-equal (ArrowSigmaSum.arrow₂ q₁ q₂) (ArrowSigmaSum.arrow₂ r₁ r₂)
      = ArrowSigmaSum.arrow₂
        (ComposeEqual.compose-equal p₁ q₁ r₁)
        (DependentComposeEqual₁.compose-equal p₂ q₂ r₂)

  compose-equal-sigma-sum
    : ComposeEqual j₁
    → DependentComposeEqual₁ j₂
    → (a₁ : SplitBase X₁ X₁')
    → (b₁ : SplitBase Y₁ Y₁')
    → (c₁ : SplitBase Z₁ Z₁')
    → ComposeEqual
      (compose-sigma-sum j₁ j₂ a₁ b₁ c₁)
  compose-equal-sigma-sum p₁ p₂ a₁ b₁ c₁
    = record {ComposeEqualSigmaSum p₁ p₂ a₁ b₁ c₁}

-- ### Precompose

module _
  {X₁ Y₁ X₁' Y₁' : Object'}
  {X₂ : DependentObject₁ X₁'}
  {Y₂ : DependentObject₁ Y₁'}
  {F₁ : Arrow' X₁ Y₁}
  {G₁ : Arrow' X₁ X₁}
  {F₂ : DependentArrow₁ X₂ Y₂}
  {G₂ : DependentArrow₁ X₂ X₂}
  {i₁ : Identity G₁}
  {i₂ : DependentIdentity₁ G₂}
  {j₁ : Compose F₁ G₁ F₁}
  {j₂ : DependentCompose₁ F₂ G₂ F₂}
  where

  module PrecomposeSigmaSum
    (p₁ : Precompose i₁ j₁)
    (p₂ : DependentPrecompose₁ i₂ j₂)
    (a₁ : SplitBase X₁ X₁')
    (b₁ : SplitBase Y₁ Y₁')
    where

    precompose
      : {x : Object'.Object (object-sigma-sum X₁ X₂)}
      → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
      → (f : Arrow'.Arrow (arrow-sigma-sum F₁ F₂ a₁ b₁) x y)
      → Arrow'.ArrowEqual (arrow-sigma-sum F₁ F₂ a₁ b₁)
        (Compose.compose (compose-sigma-sum j₁ j₂ a₁ a₁ b₁) f
          (Identity.identity (identity-sigma-sum i₁ i₂ a₁) x)) f
    precompose {x = ι₁ _} (ArrowSigmaSum.arrow₁ f₁)
      = ArrowSigmaSum.arrow₁
        (Precompose.precompose p₁ f₁)
    precompose {x = ι₂ _} (ArrowSigmaSum.arrow₁ f₁)
      = ArrowSigmaSum.arrow₁
        (Precompose.precompose p₁ f₁)
    precompose (ArrowSigmaSum.arrow₂ f₁ f₂)
      = ArrowSigmaSum.arrow₂
        (Precompose.precompose p₁ f₁)
        (DependentPrecompose₁.precompose p₂ f₂)

  precompose-sigma-sum
    : Precompose i₁ j₁
    → DependentPrecompose₁ i₂ j₂
    → (a₁ : SplitBase X₁ X₁')
    → (b₁ : SplitBase Y₁ Y₁')
    → Precompose
      (identity-sigma-sum i₁ i₂ a₁)
      (compose-sigma-sum j₁ j₂ a₁ a₁ b₁)
  precompose-sigma-sum p₁ p₂ a₁ b₁
    = record {PrecomposeSigmaSum p₁ p₂ a₁ b₁}

-- ### Postcompose

module _
  {X₁ Y₁ X₁' Y₁' : Object'}
  {X₂ : DependentObject₁ X₁'}
  {Y₂ : DependentObject₁ Y₁'}
  {F₁ : Arrow' Y₁ Y₁}
  {G₁ : Arrow' X₁ Y₁}
  {F₂ : DependentArrow₁ Y₂ Y₂}
  {G₂ : DependentArrow₁ X₂ Y₂}
  {i₁ : Identity F₁}
  {i₂ : DependentIdentity₁ F₂}
  {j₁ : Compose F₁ G₁ G₁}
  {j₂ : DependentCompose₁ F₂ G₂ G₂}
  where

  module PostcomposeSigmaSum
    (p₁ : Postcompose i₁ j₁)
    (p₂ : DependentPostcompose₁ i₂ j₂)
    (a₁ : SplitBase X₁ X₁')
    (b₁ : SplitBase Y₁ Y₁')
    where

    postcompose
      : {x : Object'.Object (object-sigma-sum X₁ X₂)}
      → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
      → (g : Arrow'.Arrow (arrow-sigma-sum G₁ G₂ a₁ b₁) x y)
      → Arrow'.ArrowEqual (arrow-sigma-sum G₁ G₂ a₁ b₁)
        (Compose.compose (compose-sigma-sum j₁ j₂ a₁ b₁ b₁)
          (Identity.identity (identity-sigma-sum i₁ i₂ b₁) y) g) g
    postcompose {y = ι₁ _} (ArrowSigmaSum.arrow₁ g₁)
      = ArrowSigmaSum.arrow₁
        (Postcompose.postcompose p₁ g₁)
    postcompose {y = ι₂ _} (ArrowSigmaSum.arrow₁ g₁)
      = ArrowSigmaSum.arrow₁
        (Postcompose.postcompose p₁ g₁)
    postcompose (ArrowSigmaSum.arrow₂ g₁ g₂)
      = ArrowSigmaSum.arrow₂
        (Postcompose.postcompose p₁ g₁)
        (DependentPostcompose₁.postcompose p₂ g₂)

  postcompose-sigma-sum
    : Postcompose i₁ j₁
    → DependentPostcompose₁ i₂ j₂
    → (a₁ : SplitBase X₁ X₁')
    → (b₁ : SplitBase Y₁ Y₁')
    → Postcompose
      (identity-sigma-sum i₁ i₂ b₁)
      (compose-sigma-sum j₁ j₂ a₁ b₁ b₁)
  postcompose-sigma-sum p₁ p₂ a₁ b₁
    = record {PostcomposeSigmaSum p₁ p₂ a₁ b₁}

-- ### Associative

module _
  {W₁ X₁ Y₁ Z₁ W₁' X₁' Y₁' Z₁' : Object'}
  {W₂ : DependentObject₁ W₁'}
  {X₂ : DependentObject₁ X₁'}
  {Y₂ : DependentObject₁ Y₁'}
  {Z₂ : DependentObject₁ Z₁'}
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

  module AssociativeSigmaSum
    (p₁ : Associative j₁ k₁ l₁ m₁)
    (p₂ : DependentAssociative₁ j₂ k₂ l₂ m₂)
    (a₁ : SplitBase W₁ W₁')
    (b₁ : SplitBase X₁ X₁')
    (c₁ : SplitBase Y₁ Y₁')
    (d₁ : SplitBase Z₁ Z₁')
    where

    associative
      : {w : Object'.Object (object-sigma-sum W₁ W₂)}
      → {x : Object'.Object (object-sigma-sum X₁ X₂)}
      → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
      → {z : Object'.Object (object-sigma-sum Z₁ Z₂)}
      → (f : Arrow'.Arrow (arrow-sigma-sum F₁ F₂ c₁ d₁) y z)
      → (g : Arrow'.Arrow (arrow-sigma-sum G₁ G₂ b₁ c₁) x y)
      → (h : Arrow'.Arrow (arrow-sigma-sum H₁ H₂ a₁ b₁) w x)
      → Arrow'.ArrowEqual (arrow-sigma-sum K₁ K₂ a₁ d₁)
        (Compose.compose (compose-sigma-sum l₁ l₂ a₁ b₁ d₁)
          (Compose.compose (compose-sigma-sum j₁ j₂ b₁ c₁ d₁) f g) h)
        (Compose.compose (compose-sigma-sum m₁ m₂ a₁ c₁ d₁) f
          (Compose.compose (compose-sigma-sum k₁ k₂ a₁ b₁ c₁) g h))
    associative
      (ArrowSigmaSum.arrow₁ f₁)
      (ArrowSigmaSum.arrow₁ g₁)
      (ArrowSigmaSum.arrow₁ h₁)
      = ArrowSigmaSum.arrow₁
        (Associative.associative p₁ f₁ g₁ h₁)
    associative
      (ArrowSigmaSum.arrow₁ f₁)
      (ArrowSigmaSum.arrow₁ g₁)
      (ArrowSigmaSum.arrow₂ h₁ _)
      = ArrowSigmaSum.arrow₁
        (Associative.associative p₁ f₁ g₁ h₁)
    associative
      (ArrowSigmaSum.arrow₁ f₁)
      (ArrowSigmaSum.arrow₂ g₁ _)
      (ArrowSigmaSum.arrow₁ h₁)
      = ArrowSigmaSum.arrow₁
        (Associative.associative p₁ f₁ g₁ h₁)
    associative
      (ArrowSigmaSum.arrow₁ f₁)
      (ArrowSigmaSum.arrow₂ g₁ _)
      (ArrowSigmaSum.arrow₂ h₁ _)
      = ArrowSigmaSum.arrow₁
        (Associative.associative p₁ f₁ g₁ h₁)
    associative
      (ArrowSigmaSum.arrow₂ f₁ _)
      (ArrowSigmaSum.arrow₁ g₁)
      (ArrowSigmaSum.arrow₁ h₁)
      = ArrowSigmaSum.arrow₁
        (Associative.associative p₁ f₁ g₁ h₁)
    associative
      (ArrowSigmaSum.arrow₂ f₁ _)
      (ArrowSigmaSum.arrow₁ g₁)
      (ArrowSigmaSum.arrow₂ h₁ _)
      = ArrowSigmaSum.arrow₁
        (Associative.associative p₁ f₁ g₁ h₁)
    associative
      (ArrowSigmaSum.arrow₂ f₁ _)
      (ArrowSigmaSum.arrow₂ g₁ _)
      (ArrowSigmaSum.arrow₁ h₁)
      = ArrowSigmaSum.arrow₁
        (Associative.associative p₁ f₁ g₁ h₁)
    associative
      (ArrowSigmaSum.arrow₂ f₁ f₂)
      (ArrowSigmaSum.arrow₂ g₁ g₂)
      (ArrowSigmaSum.arrow₂ h₁ h₂)
      = ArrowSigmaSum.arrow₂
        (Associative.associative p₁ f₁ g₁ h₁)
        (DependentAssociative₁.associative p₂ f₂ g₂ h₂)

  associative-sigma-sum
    : Associative j₁ k₁ l₁ m₁
    → DependentAssociative₁ j₂ k₂ l₂ m₂
    → (a₁ : SplitBase W₁ W₁')
    → (b₁ : SplitBase X₁ X₁')
    → (c₁ : SplitBase Y₁ Y₁')
    → (d₁ : SplitBase Z₁ Z₁')
    → Associative
      (compose-sigma-sum j₁ j₂ b₁ c₁ d₁)
      (compose-sigma-sum k₁ k₂ a₁ b₁ c₁)
      (compose-sigma-sum l₁ l₂ a₁ b₁ d₁)
      (compose-sigma-sum m₁ m₂ a₁ c₁ d₁)
  associative-sigma-sum p₁ p₂ a₁ b₁ c₁ d₁
    = record {AssociativeSigmaSum p₁ p₂ a₁ b₁ c₁ d₁}

-- ## Dependent

-- ### DependentObject

dependent-object-sigma-sum
  : {n : ℕ}
  → {X : ChainObject n}
  → DependentObject X
  → {X₁'' : DependentObject X}
  → DependentObject (chain-object-snoc X₁'')
  → DependentObject X
dependent-object-sigma-sum {n = zero} X₁' X₂'
  = object-sigma-sum X₁' X₂'
dependent-object-sigma-sum {n = suc _} X₁' X₂'
  = record
  { tail
    = λ x → dependent-object-sigma-sum
      (DependentObject.tail X₁' x)
      (DependentObject.tail X₂' x)
  }

-- ### DependentArrow

dependent-arrow-sigma-sum
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₁'' : DependentObject X}
  → {Y₁' Y₁'' : DependentObject Y}
  → {X₂' : DependentObject (chain-object-snoc X₁'')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁'')}
  → DependentArrow X₁' Y₁'
  → DependentArrow X₂' Y₂'
  → DependentSplitBase X₁' X₁''
  → DependentSplitBase Y₁' Y₁''
  → DependentArrow
    (dependent-object-sigma-sum X₁' X₂')
    (dependent-object-sigma-sum Y₁' Y₂')
dependent-arrow-sigma-sum {n = zero} F₁ F₂ a₁ b₁
  = arrow-sigma-sum F₁ F₂ a₁ b₁
dependent-arrow-sigma-sum {n = suc _} F₁ F₂ a₁ b₁
  = record
  { tail
    = λ x y → dependent-arrow-sigma-sum
      (DependentArrow.tail F₁ x y)
      (DependentArrow.tail F₂ x y)
      (DependentSplitBase.tail a₁ x)
      (DependentSplitBase.tail b₁ y)
  }

-- ### DependentSimplify

dependent-simplify-sigma-sum
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₁'' : DependentObject X}
  → {Y₁' Y₁'' : DependentObject Y}
  → {X₂' : DependentObject (chain-object-snoc X₁'')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁'')}
  → {F₁ : DependentArrow X₁' Y₁'}
  → {F₂ : DependentArrow X₂' Y₂'}
  → DependentSimplify F₁
  → DependentSimplify F₂
  → (a₁ : DependentSplitBase X₁' X₁'')
  → (b₁ : DependentSplitBase Y₁' Y₁'')
  → DependentSimplify
    (dependent-arrow-sigma-sum F₁ F₂ a₁ b₁)
dependent-simplify-sigma-sum {n = zero} s₁ s₂ a₁ b₁
  = simplify-sigma-sum s₁ s₂ a₁ b₁
dependent-simplify-sigma-sum {n = suc _} s₁ s₂ a₁ b₁
  = record
  { tail
    = λ x y → dependent-simplify-sigma-sum
      (DependentSimplify.tail s₁ x y)
      (DependentSimplify.tail s₂ x y)
      (DependentSplitBase.tail a₁ x)
      (DependentSplitBase.tail b₁ y)
  }

-- ### DependentIdentity

dependent-identity-sigma-sum
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' : DependentObject X}
  → {X₁'' : DependentObject X}
  → {X₂' : DependentObject (chain-object-snoc X₁'')}
  → {F₁ : DependentArrow X₁' X₁'}
  → {F₂ : DependentArrow X₂' X₂'}
  → DependentIdentity F₁
  → DependentIdentity F₂
  → (a₁ : DependentSplitBase X₁' X₁'')
  → DependentIdentity
    (dependent-arrow-sigma-sum F₁ F₂ a₁ a₁)
dependent-identity-sigma-sum {n = zero} i₁ i₂ a₁
  = identity-sigma-sum i₁ i₂ a₁
dependent-identity-sigma-sum {n = suc _} i₁ i₂ a₁
  = record
  { tail
    = λ x → dependent-identity-sigma-sum
      (DependentIdentity.tail i₁ x)
      (DependentIdentity.tail i₂ x)
      (DependentSplitBase.tail a₁ x)
  }

-- ### DependentCompose

dependent-compose-sigma-sum
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X₁' : DependentObject X}
  → {Y₁' : DependentObject Y}
  → {Z₁' : DependentObject Z}
  → {X₁'' : DependentObject X}
  → {Y₁'' : DependentObject Y}
  → {Z₁'' : DependentObject Z}
  → {X₂' : DependentObject (chain-object-snoc X₁'')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁'')}
  → {Z₂' : DependentObject (chain-object-snoc Z₁'')}
  → {F₁ : DependentArrow Y₁' Z₁'}
  → {G₁ : DependentArrow X₁' Y₁'}
  → {H₁ : DependentArrow X₁' Z₁'}
  → {F₂ : DependentArrow Y₂' Z₂'}
  → {G₂ : DependentArrow X₂' Y₂'}
  → {H₂ : DependentArrow X₂' Z₂'}
  → DependentCompose F₁ G₁ H₁
  → DependentCompose F₂ G₂ H₂
  → (a₁ : DependentSplitBase X₁' X₁'')
  → (b₁ : DependentSplitBase Y₁' Y₁'')
  → (c₁ : DependentSplitBase Z₁' Z₁'')
  → DependentCompose
    (dependent-arrow-sigma-sum F₁ F₂ b₁ c₁)
    (dependent-arrow-sigma-sum G₁ G₂ a₁ b₁)
    (dependent-arrow-sigma-sum H₁ H₂ a₁ c₁)
dependent-compose-sigma-sum {n = zero} j₁ j₂ a₁ b₁ c₁
  = compose-sigma-sum j₁ j₂ a₁ b₁ c₁
dependent-compose-sigma-sum {n = suc _} j₁ j₂ a₁ b₁ c₁
  = record
  { tail
    = λ x y z → dependent-compose-sigma-sum
      (DependentCompose.tail j₁ x y z)
      (DependentCompose.tail j₂ x y z)
      (DependentSplitBase.tail a₁ x)
      (DependentSplitBase.tail b₁ y)
      (DependentSplitBase.tail c₁ z)
  }

-- ### DependentComposeEqual

dependent-compose-equal-sigma-sum
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X₁' : DependentObject X}
  → {Y₁' : DependentObject Y}
  → {Z₁' : DependentObject Z}
  → {X₁'' : DependentObject X}
  → {Y₁'' : DependentObject Y}
  → {Z₁'' : DependentObject Z}
  → {X₂' : DependentObject (chain-object-snoc X₁'')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁'')}
  → {Z₂' : DependentObject (chain-object-snoc Z₁'')}
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
  → (a₁ : DependentSplitBase X₁' X₁'')
  → (b₁ : DependentSplitBase Y₁' Y₁'')
  → (c₁ : DependentSplitBase Z₁' Z₁'')
  → DependentComposeEqual
    (dependent-compose-sigma-sum j₁ j₂ a₁ b₁ c₁)
dependent-compose-equal-sigma-sum {n = zero} p₁ p₂ a₁ b₁ c₁
  = compose-equal-sigma-sum p₁ p₂ a₁ b₁ c₁
dependent-compose-equal-sigma-sum {n = suc _} p₁ p₂ a₁ b₁ c₁
  = record
  { tail
    = λ x y z → dependent-compose-equal-sigma-sum
      (DependentComposeEqual.tail p₁ x y z)
      (DependentComposeEqual.tail p₂ x y z)
      (DependentSplitBase.tail a₁ x)
      (DependentSplitBase.tail b₁ y)
      (DependentSplitBase.tail c₁ z)
  }

-- ### DependentPrecompose

dependent-precompose-sigma-sum
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₁'' : DependentObject X}
  → {Y₁' Y₁'' : DependentObject Y}
  → {X₂' : DependentObject (chain-object-snoc X₁'')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁'')}
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
  → (a₁ : DependentSplitBase X₁' X₁'')
  → (b₁ : DependentSplitBase Y₁' Y₁'')
  → DependentPrecompose
    (dependent-identity-sigma-sum i₁ i₂ a₁)
    (dependent-compose-sigma-sum j₁ j₂ a₁ a₁ b₁)
dependent-precompose-sigma-sum {n = zero} p₁ p₂ a₁ b₁
  = precompose-sigma-sum p₁ p₂ a₁ b₁
dependent-precompose-sigma-sum {n = suc _} p₁ p₂ a₁ b₁
  = record
  { tail
    = λ x y → dependent-precompose-sigma-sum
      (DependentPrecompose.tail p₁ x y)
      (DependentPrecompose.tail p₂ x y)
      (DependentSplitBase.tail a₁ x)
      (DependentSplitBase.tail b₁ y)
  }

-- ### DependentPostcompose

dependent-postcompose-sigma-sum
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₁'' : DependentObject X}
  → {Y₁' Y₁'' : DependentObject Y}
  → {X₂' : DependentObject (chain-object-snoc X₁'')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁'')}
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
  → (a₁ : DependentSplitBase X₁' X₁'')
  → (b₁ : DependentSplitBase Y₁' Y₁'')
  → DependentPostcompose
    (dependent-identity-sigma-sum i₁ i₂ b₁)
    (dependent-compose-sigma-sum j₁ j₂ a₁ b₁ b₁)
dependent-postcompose-sigma-sum {n = zero} p₁ p₂ a₁ b₁
  = postcompose-sigma-sum p₁ p₂ a₁ b₁
dependent-postcompose-sigma-sum {n = suc _} p₁ p₂ a₁ b₁
  = record
  { tail
    = λ x y → dependent-postcompose-sigma-sum
      (DependentPostcompose.tail p₁ x y)
      (DependentPostcompose.tail p₂ x y)
      (DependentSplitBase.tail a₁ x)
      (DependentSplitBase.tail b₁ y)
  }

-- ### DependentAssociative

dependent-associative-sigma-sum
  : {n : ℕ}
  → {W X Y Z : ChainObject n}
  → {W₁' W₁'' : DependentObject W}
  → {X₁' X₁'' : DependentObject X}
  → {Y₁' Y₁'' : DependentObject Y}
  → {Z₁' Z₁'' : DependentObject Z}
  → {W₂' : DependentObject (chain-object-snoc W₁'')}
  → {X₂' : DependentObject (chain-object-snoc X₁'')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁'')}
  → {Z₂' : DependentObject (chain-object-snoc Z₁'')}
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
  → (a₁ : DependentSplitBase W₁' W₁'')
  → (b₁ : DependentSplitBase X₁' X₁'')
  → (c₁ : DependentSplitBase Y₁' Y₁'')
  → (d₁ : DependentSplitBase Z₁' Z₁'')
  → DependentAssociative
    (dependent-compose-sigma-sum j₁ j₂ b₁ c₁ d₁)
    (dependent-compose-sigma-sum k₁ k₂ a₁ b₁ c₁)
    (dependent-compose-sigma-sum l₁ l₂ a₁ b₁ d₁)
    (dependent-compose-sigma-sum m₁ m₂ a₁ c₁ d₁)
dependent-associative-sigma-sum {n = zero} p₁ p₂ a₁ b₁ c₁ d₁
  = associative-sigma-sum p₁ p₂ a₁ b₁ c₁ d₁
dependent-associative-sigma-sum {n = suc _} p₁ p₂ a₁ b₁ c₁ d₁
  = record
  { tail
    = λ w x y z → dependent-associative-sigma-sum
      (DependentAssociative.tail p₁ w x y z)
      (DependentAssociative.tail p₂ w x y z)
      (DependentSplitBase.tail a₁ w)
      (DependentSplitBase.tail b₁ x)
      (DependentSplitBase.tail c₁ y)
      (DependentSplitBase.tail d₁ z)
  }

