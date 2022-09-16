module Category.Split.Core.Sigma where

open import Category.Core
  using (Arrow'; ChainObject; Compose; DependentArrow; DependentArrow₁;
    DependentCompose; DependentCompose₁; DependentIdentity; DependentIdentity₁;
    DependentObject; DependentObject₁; Identity; Object')
open import Category.Core.Sigma
  using (module ArrowSigma; arrow-sigma; compose-sigma; dependent-arrow-sigma;
    dependent-compose-sigma; dependent-identity-sigma; dependent-object-sigma;
    identity-sigma; object-sigma)
open import Category.Core.Sigma.Sum
  using (module ArrowSigmaSum; arrow-sigma-sum; compose-sigma-sum;
    dependent-arrow-sigma-sum; dependent-compose-sigma-sum;
    dependent-identity-sigma-sum; dependent-object-sigma-sum;
    identity-sigma-sum; object-sigma-sum)
open import Category.Core.Snoc
  using (chain-object-snoc)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitBase₁; DependentSplitCompose;
    DependentSplitCompose₁; DependentSplitIdentity; DependentSplitIdentity₁;
    DependentSplitMap; DependentSplitMap₁; SplitBase; SplitCompose;
    SplitIdentity; SplitMap)
open import Data.Equal
  using (_≡_; refl)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (_,_)
open import Data.Sum
  using (ι₁; ι₂)

-- ## Base

-- ### SplitBase

module SplitBaseSigma
  (X₁ : Object')
  {X₁' : Object'}
  {X₂ X₂' : DependentObject₁ X₁'}
  (a₂ : DependentSplitBase₁ X₂ X₂')
  where

  base
    : Object'.Object (object-sigma-sum X₁ X₂)
    → Maybe (Object'.Object (object-sigma X₂'))
  base (ι₁ _)
    = nothing
  base (ι₂ (x₁ , x₂))
    with DependentSplitBase₁.base a₂ x₂
  ... | nothing
    = nothing
  ... | just x₂'
    = just (x₁ , x₂')

  unbase
    : Object'.Object (object-sigma X₂')
    → Object'.Object (object-sigma-sum X₁ X₂)
  unbase (x₁ , x₂)
    = ι₂ (x₁ , DependentSplitBase₁.unbase a₂ x₂)

  base-unbase
    : (x : Object'.Object (object-sigma X₂'))
    → base (unbase x) ≡ just x
  base-unbase (_ , x₂)
    with DependentSplitBase₁.base a₂ (DependentSplitBase₁.unbase a₂ x₂)
    | DependentSplitBase₁.base-unbase a₂ x₂
  ... | _ | refl
    = refl

split-base-sigma
  : (X₁ : Object')
  → {X₁' : Object'}
  → {X₂ X₂' : DependentObject₁ X₁'}
  → DependentSplitBase₁ X₂ X₂'
  → SplitBase
    (object-sigma-sum X₁ X₂)
    (object-sigma X₂')
split-base-sigma X₁ a₂
  = record {SplitBaseSigma X₁ a₂}

-- ### SplitMap

module _
  {X₁ Y₁ X₁' Y₁' : Object'}
  {X₂ X₂' : DependentObject₁ X₁'}
  {Y₂ Y₂' : DependentObject₁ Y₁'}
  {F₁ : Arrow' X₁ Y₁}
  {F₁' : Arrow' X₁' Y₁'}
  {F₂ : DependentArrow₁ X₂ Y₂}
  {F₂' : DependentArrow₁ X₂' Y₂'}
  {a₁ : SplitBase X₁ X₁'}
  {b₁ : SplitBase Y₁ Y₁'}
  {a₂ : DependentSplitBase₁ X₂ X₂'}
  {b₂ : DependentSplitBase₁ Y₂ Y₂'}
  where

  module SplitMapSigma
    (m₁ : SplitMap F₁ F₁' a₁ b₁)
    (m₂ : DependentSplitMap₁ F₂ F₂' a₂ b₂)
    where

    map
      : {x : Object'.Object (object-sigma-sum X₁ X₂)}
      → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
      → {x' : Object'.Object (object-sigma X₂')}
      → {y' : Object'.Object (object-sigma Y₂')}
      → SplitBase.base (split-base-sigma X₁ a₂) x ≡ just x'
      → SplitBase.base (split-base-sigma Y₁ b₂) y ≡ just y'
      → Arrow'.Arrow (arrow-sigma-sum F₁ F₂ a₁ b₁) x y
      → Arrow'.Arrow (arrow-sigma F₁' F₂') x' y'
    map {x = ι₂ (_ , x₂)} {y = ι₂ (_ , y₂)} _ _ _
      with DependentSplitBase₁.base a₂ x₂
      | inspect (DependentSplitBase₁.base a₂) x₂
      | DependentSplitBase₁.base b₂ y₂
      | inspect (DependentSplitBase₁.base b₂) y₂
    map {x = ι₂ (x₁ , _)} {y = ι₂ (y₁ , _)} refl refl
      (ArrowSigmaSum.arrow₁ f₁)
      | just _ | _ | just _ | _
      = ArrowSigma.arrow₁
        (SplitMap.map m₁ p₁ q₁ f₁)
      where
        p₁ = SplitBase.base-unbase a₁ x₁
        q₁ = SplitBase.base-unbase b₁ y₁

    map {x = ι₂ (x₁ , _)} {y = ι₂ (y₁ , _)} refl refl
      (ArrowSigmaSum.arrow₂ f₁ f₂)
      | just _ | [ p₂ ] | just _ | [ q₂ ]
      = ArrowSigma.arrow₂
        (SplitMap.map m₁ p₁ q₁ f₁)
        (DependentSplitMap₁.map m₂ p₂ q₂ f₂)
      where
        p₁ = SplitBase.base-unbase a₁ x₁
        q₁ = SplitBase.base-unbase b₁ y₁

    map-equal
      : {x : Object'.Object (object-sigma-sum X₁ X₂)}
      → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
      → {x' : Object'.Object (object-sigma X₂')}
      → {y' : Object'.Object (object-sigma Y₂')}
      → {f₁ f₂ : Arrow'.Arrow (arrow-sigma-sum F₁ F₂ a₁ b₁) x y}
      → (p : SplitBase.base (split-base-sigma X₁ a₂) x ≡ just x')
      → (q : SplitBase.base (split-base-sigma Y₁ b₂) y ≡ just y')
      → Arrow'.ArrowEqual (arrow-sigma-sum F₁ F₂ a₁ b₁) f₁ f₂
      → Arrow'.ArrowEqual (arrow-sigma F₁' F₂') (map p q f₁) (map p q f₂)
    map-equal {x = ι₂ (_ , x₂)} {y = ι₂ (_ , y₂)} _ _ _
      with DependentSplitBase₁.base a₂ x₂
      | inspect (DependentSplitBase₁.base a₂) x₂
      | DependentSplitBase₁.base b₂ y₂
      | inspect (DependentSplitBase₁.base b₂) y₂
    map-equal {x = ι₂ (x₁ , _)} {y = ι₂ (y₁ , _)} refl refl
      (ArrowSigmaSum.arrow₁ r₁)
      | just _ | _ | just _ | _
      = ArrowSigma.arrow₁
        (SplitMap.map-equal m₁ p₁ q₁ r₁)
      where
        p₁ = SplitBase.base-unbase a₁ x₁
        q₁ = SplitBase.base-unbase b₁ y₁

    map-equal {x = ι₂ (x₁ , _)} {y = ι₂ (y₁ , _)} refl refl
      (ArrowSigmaSum.arrow₂ r₁ r₂)
      | just _ | [ p₂ ] | just _ | [ q₂ ]
      = ArrowSigma.arrow₂
        (SplitMap.map-equal m₁ p₁ q₁ r₁)
        (DependentSplitMap₁.map-equal m₂ p₂ q₂ r₂)
      where
        p₁ = SplitBase.base-unbase a₁ x₁
        q₁ = SplitBase.base-unbase b₁ y₁

    unmap
      : {x : Object'.Object (object-sigma X₂')}
      → {y : Object'.Object (object-sigma Y₂')}
      → Arrow'.Arrow (arrow-sigma F₁' F₂') x y
      → Arrow'.Arrow (arrow-sigma-sum F₁ F₂ a₁ b₁)
        (SplitBase.unbase (split-base-sigma X₁ a₂) x)
        (SplitBase.unbase (split-base-sigma Y₁ b₂) y)
    unmap (ArrowSigma.arrow₁ f₁)
      = ArrowSigmaSum.arrow₁
        (SplitMap.unmap m₁ f₁)
    unmap (ArrowSigma.arrow₂ f₁ f₂)
      = ArrowSigmaSum.arrow₂
        (SplitMap.unmap m₁ f₁)
        (DependentSplitMap₁.unmap m₂ f₂)

    unmap-equal
      : {x : Object'.Object (object-sigma X₂')}
      → {y : Object'.Object (object-sigma Y₂')}
      → {f₁ f₂ : Arrow'.Arrow (arrow-sigma F₁' F₂') x y}
      → Arrow'.ArrowEqual (arrow-sigma F₁' F₂') f₁ f₂
      → Arrow'.ArrowEqual (arrow-sigma-sum F₁ F₂ a₁ b₁) (unmap f₁) (unmap f₂)
    unmap-equal (ArrowSigma.arrow₁ p₁)
      = ArrowSigmaSum.arrow₁
        (SplitMap.unmap-equal m₁ p₁)
    unmap-equal (ArrowSigma.arrow₂ p₁ p₂)
      = ArrowSigmaSum.arrow₂
        (SplitMap.unmap-equal m₁ p₁)
        (DependentSplitMap₁.unmap-equal m₂ p₂)

    map-unmap
      : {x : Object'.Object (object-sigma X₂')}
      → {y : Object'.Object (object-sigma Y₂')}
      → (p : SplitBase.base (split-base-sigma X₁ a₂)
        (SplitBase.unbase (split-base-sigma X₁ a₂) x)
        ≡ just x)
      → (q : SplitBase.base (split-base-sigma Y₁ b₂)
        (SplitBase.unbase (split-base-sigma Y₁ b₂) y)
        ≡ just y)
      → (f : Arrow'.Arrow (arrow-sigma F₁' F₂') x y)
      → Arrow'.ArrowEqual (arrow-sigma F₁' F₂') (map p q (unmap f)) f
    map-unmap {x = (_ , x₂)} {y = (_ , y₂)} _ _ _
      with DependentSplitBase₁.base a₂ (DependentSplitBase₁.unbase a₂ x₂)
      | inspect (DependentSplitBase₁.base a₂) (DependentSplitBase₁.unbase a₂ x₂)
      | DependentSplitBase₁.base-unbase a₂ x₂
      | DependentSplitBase₁.base b₂ (DependentSplitBase₁.unbase b₂ y₂)
      | inspect (DependentSplitBase₁.base b₂) (DependentSplitBase₁.unbase b₂ y₂)
      | DependentSplitBase₁.base-unbase b₂ y₂
    map-unmap {x = (x₁ , _)} {y = (y₁ , _)} refl refl (ArrowSigma.arrow₁ f₁)
      | _ | _ | refl | _ | _ | refl
      = ArrowSigma.arrow₁
        (SplitMap.map-unmap m₁ p₁ q₁ f₁)
      where
        p₁ = SplitBase.base-unbase a₁ x₁
        q₁ = SplitBase.base-unbase b₁ y₁

    map-unmap {x = (x₁ , _)} {y = (y₁ , _)} refl refl (ArrowSigma.arrow₂ f₁ f₂)
      | _ | [ p₂ ] | refl | _ | [ q₂ ] | refl
      = ArrowSigma.arrow₂
        (SplitMap.map-unmap m₁ p₁ q₁ f₁)
        (DependentSplitMap₁.map-unmap m₂ p₂ q₂ f₂)
      where
        p₁ = SplitBase.base-unbase a₁ x₁
        q₁ = SplitBase.base-unbase b₁ y₁

  split-map-sigma
    : SplitMap F₁ F₁' a₁ b₁
    → DependentSplitMap₁ F₂ F₂' a₂ b₂
    → SplitMap
      (arrow-sigma-sum F₁ F₂ a₁ b₁)
      (arrow-sigma F₁' F₂')
      (split-base-sigma X₁ a₂)
      (split-base-sigma Y₁ b₂)
  split-map-sigma m₁ m₂
    = record {SplitMapSigma m₁ m₂}

-- ### SplitIdentity

module _
  {X₁ X₁' : Object'}
  {X₂ X₂' : DependentObject₁ X₁'}
  {F₁ : Arrow' X₁ X₁}
  {F₁' : Arrow' X₁' X₁'}
  {F₂ : DependentArrow₁ X₂ X₂}
  {F₂' : DependentArrow₁ X₂' X₂'}
  {i₁ : Identity F₁}
  {i₁' : Identity F₁'}
  {i₂ : DependentIdentity₁ F₂}
  {i₂' : DependentIdentity₁ F₂'}
  {a₁ : SplitBase X₁ X₁'}
  {a₂ : DependentSplitBase₁ X₂ X₂'}
  {m₁ : SplitMap F₁ F₁' a₁ a₁}
  {m₂ : DependentSplitMap₁ F₂ F₂' a₂ a₂}
  where

  module SplitIdentitySigma
    (p₁ : SplitIdentity i₁ i₁' m₁)
    (p₂ : DependentSplitIdentity₁ i₂ i₂' m₂)
    where

    map
      : (x : Object'.Object (object-sigma-sum X₁ X₂))
      → {x' : Object'.Object (object-sigma X₂')}
      → (q : SplitBase.base (split-base-sigma X₁ a₂) x ≡ just x')
      → Arrow'.ArrowEqual (arrow-sigma F₁' F₂')
        (SplitMap.map (split-map-sigma m₁ m₂) q q
          (Identity.identity (identity-sigma-sum i₁ i₂ a₁) x))
        (Identity.identity (identity-sigma i₁' i₂') x')
    map (ι₂ (_ , x₂)) _
      with DependentSplitBase₁.base a₂ x₂
      | inspect (DependentSplitBase₁.base a₂) x₂
    map (ι₂ (x₁' , x₂)) refl | just _ | [ q₂ ]
      = ArrowSigma.arrow₂
        (SplitIdentity.map p₁ x₁ q₁)
        (DependentSplitIdentity₁.map p₂ x₂ q₂)
      where
        x₁ = SplitBase.unbase a₁ x₁'
        q₁ = SplitBase.base-unbase a₁ x₁'

    unmap
      : (x : Object'.Object (object-sigma X₂'))
      → Arrow'.ArrowEqual (arrow-sigma-sum F₁ F₂ a₁ a₁)
        (SplitMap.unmap (split-map-sigma m₁ m₂)
          (Identity.identity (identity-sigma i₁' i₂') x))
        (Identity.identity (identity-sigma-sum i₁ i₂ a₁)
          (SplitBase.unbase (split-base-sigma X₁ a₂) x))
    unmap (x₁ , x₂)
      = ArrowSigmaSum.arrow₂
        (SplitIdentity.unmap p₁ x₁)
        (DependentSplitIdentity₁.unmap p₂ x₂)

    normalize-arrow
      : (x : Object'.Object (object-sigma-sum X₁ X₂))
      → {x' : Object'.Object (object-sigma X₂')}
      → SplitBase.base (split-base-sigma X₁ a₂) x ≡ just x'
      → Arrow'.Arrow (arrow-sigma-sum F₁ F₂ a₁ a₁) x
        (SplitBase.unbase (split-base-sigma X₁ a₂) x')
    normalize-arrow (ι₂ (_ , x₂)) _
      with DependentSplitBase₁.base a₂ x₂
      | inspect (DependentSplitBase₁.base a₂) x₂
    normalize-arrow (ι₂ (x₁' , x₂)) refl | just _ | [ q₂ ]
      = ArrowSigmaSum.arrow₂ 
        (Identity.identity i₁ x₁)
        (DependentSplitIdentity₁.normalize-arrow p₂ x₂ q₂)
      where
        x₁ = SplitBase.unbase a₁ x₁'

    normalize-valid
      : (x : Object'.Object (object-sigma-sum X₁ X₂))
      → {x' : Object'.Object (object-sigma X₂')}
      → (q : SplitBase.base (split-base-sigma X₁ a₂) x ≡ just x')
      → (r : SplitBase.base (split-base-sigma X₁ a₂)
        (SplitBase.unbase (split-base-sigma X₁ a₂) x')
        ≡ just x')
      → Arrow'.ArrowEqual (arrow-sigma F₁' F₂')
        (SplitMap.map (split-map-sigma m₁ m₂) q r (normalize-arrow x q))
        (Identity.identity (identity-sigma i₁' i₂') x')
    normalize-valid (ι₂ (_ , x₂)) {x' = (_ , x₂')} _ _
      with DependentSplitBase₁.base a₂ x₂
      | inspect (DependentSplitBase₁.base a₂) x₂
      | DependentSplitBase₁.base a₂
        (DependentSplitBase₁.unbase a₂ x₂')
      | inspect (DependentSplitBase₁.base a₂)
        (DependentSplitBase₁.unbase a₂ x₂')
      | DependentSplitBase₁.base-unbase a₂ x₂'
    normalize-valid (ι₂ (x₁' , x₂)) refl refl
      | just x₂' | [ q₂ ] | _ | [ r₂ ] | refl
      = ArrowSigma.arrow₂
        (SplitIdentity.map p₁ x₁ q₁)
        (DependentSplitIdentity₁.normalize-valid p₂ x₂ q₂ r₂)
      where
        x₁ = SplitBase.unbase a₁ x₁'
        q₁ = SplitBase.base-unbase a₁ x₁'

  split-identity-sigma
    : SplitIdentity i₁ i₁' m₁
    → DependentSplitIdentity₁ i₂ i₂' m₂
    → SplitIdentity
      (identity-sigma-sum i₁ i₂ a₁)
      (identity-sigma i₁' i₂')
      (split-map-sigma m₁ m₂)
  split-identity-sigma p₁ p₂
    = record {SplitIdentitySigma p₁ p₂}

-- ### SplitCompose

module _
  {X₁ Y₁ Z₁ X₁' Y₁' Z₁' : Object'}
  {X₂ X₂' : DependentObject₁ X₁'}
  {Y₂ Y₂' : DependentObject₁ Y₁'}
  {Z₂ Z₂' : DependentObject₁ Z₁'}
  {F₁ : Arrow' Y₁ Z₁}
  {G₁ : Arrow' X₁ Y₁}
  {H₁ : Arrow' X₁ Z₁}
  {F₁' : Arrow' Y₁' Z₁'}
  {G₁' : Arrow' X₁' Y₁'}
  {H₁' : Arrow' X₁' Z₁'}
  {F₂ : DependentArrow₁ Y₂ Z₂}
  {G₂ : DependentArrow₁ X₂ Y₂}
  {H₂ : DependentArrow₁ X₂ Z₂}
  {F₂' : DependentArrow₁ Y₂' Z₂'}
  {G₂' : DependentArrow₁ X₂' Y₂'}
  {H₂' : DependentArrow₁ X₂' Z₂'}
  {j₁ : Compose F₁ G₁ H₁}
  {j₁' : Compose F₁' G₁' H₁'}
  {j₂ : DependentCompose₁ F₂ G₂ H₂}
  {j₂' : DependentCompose₁ F₂' G₂' H₂'}
  {a₁ : SplitBase X₁ X₁'}
  {b₁ : SplitBase Y₁ Y₁'}
  {c₁ : SplitBase Z₁ Z₁'}
  {a₂ : DependentSplitBase₁ X₂ X₂'}
  {b₂ : DependentSplitBase₁ Y₂ Y₂'}
  {c₂ : DependentSplitBase₁ Z₂ Z₂'}
  {m₁ : SplitMap F₁ F₁' b₁ c₁}
  {n₁ : SplitMap G₁ G₁' a₁ b₁}
  {o₁ : SplitMap H₁ H₁' a₁ c₁}
  {m₂ : DependentSplitMap₁ F₂ F₂' b₂ c₂}
  {n₂ : DependentSplitMap₁ G₂ G₂' a₂ b₂}
  {o₂ : DependentSplitMap₁ H₂ H₂' a₂ c₂}
  where

  module SplitComposeSigma
    (p₁ : SplitCompose j₁ j₁' m₁ n₁ o₁)
    (p₂ : DependentSplitCompose₁ j₂ j₂' m₂ n₂ o₂)
    where

    map
      : {x : Object'.Object (object-sigma-sum X₁ X₂)}
      → {y : Object'.Object (object-sigma-sum Y₁ Y₂)}
      → {z : Object'.Object (object-sigma-sum Z₁ Z₂)}
      → {x' : Object'.Object (object-sigma X₂')}
      → {y' : Object'.Object (object-sigma Y₂')}
      → {z' : Object'.Object (object-sigma Z₂')}
      → (q : SplitBase.base (split-base-sigma X₁ a₂) x ≡ just x')
      → (r : SplitBase.base (split-base-sigma Y₁ b₂) y ≡ just y')
      → (s : SplitBase.base (split-base-sigma Z₁ c₂) z ≡ just z')
      → (f : Arrow'.Arrow (arrow-sigma-sum F₁ F₂ b₁ c₁) y z)
      → (g : Arrow'.Arrow (arrow-sigma-sum G₁ G₂ a₁ b₁) x y)
      → Arrow'.ArrowEqual (arrow-sigma H₁' H₂')
        (SplitMap.map (split-map-sigma o₁ o₂) q s
          (Compose.compose (compose-sigma-sum j₁ j₂ a₁ b₁ c₁) f g))
        (Compose.compose (compose-sigma j₁' j₂')
          (SplitMap.map (split-map-sigma m₁ m₂) r s f)
          (SplitMap.map (split-map-sigma n₁ n₂) q r g))
    map {x = ι₂ (_ , x₂)} {y = ι₂ (_ , y₂)} {z = ι₂ (_ , z₂)} _ _ _ _ _
      with DependentSplitBase₁.base a₂ x₂
      | inspect (DependentSplitBase₁.base a₂) x₂
      | DependentSplitBase₁.base b₂ y₂
      | inspect (DependentSplitBase₁.base b₂) y₂
      | DependentSplitBase₁.base c₂ z₂
      | inspect (DependentSplitBase₁.base c₂) z₂
    map {x = ι₂ (x₁ , _)} {y = ι₂ (y₁ , _)} {z = ι₂ (z₁ , _)} refl refl refl
      (ArrowSigmaSum.arrow₁ f₁)
      (ArrowSigmaSum.arrow₁ g₁)
      | just _ | _ | just _ | _ | just _ | _
      = ArrowSigma.arrow₁
        (SplitCompose.map p₁ q₁ r₁ s₁ f₁ g₁)
      where
        q₁ = SplitBase.base-unbase a₁ x₁
        r₁ = SplitBase.base-unbase b₁ y₁
        s₁ = SplitBase.base-unbase c₁ z₁

    map {x = ι₂ (x₁ , _)} {y = ι₂ (y₁ , _)} {z = ι₂ (z₁ , _)} refl refl refl
      (ArrowSigmaSum.arrow₁ f₁)
      (ArrowSigmaSum.arrow₂ g₁ _)
      | just _ | _ | just _ | _ | just _ | _
      = ArrowSigma.arrow₁
        (SplitCompose.map p₁ q₁ r₁ s₁ f₁ g₁)
      where
        q₁ = SplitBase.base-unbase a₁ x₁
        r₁ = SplitBase.base-unbase b₁ y₁
        s₁ = SplitBase.base-unbase c₁ z₁

    map {x = ι₂ (x₁ , _)} {y = ι₂ (y₁ , _)} {z = ι₂ (z₁ , _)} refl refl refl
      (ArrowSigmaSum.arrow₂ f₁ _)
      (ArrowSigmaSum.arrow₁ g₁)
      | just _ | _ | just _ | _ | just _ | _
      = ArrowSigma.arrow₁
        (SplitCompose.map p₁ q₁ r₁ s₁ f₁ g₁)
      where
        q₁ = SplitBase.base-unbase a₁ x₁
        r₁ = SplitBase.base-unbase b₁ y₁
        s₁ = SplitBase.base-unbase c₁ z₁

    map {x = ι₂ (x₁ , _)} {y = ι₂ (y₁ , _)} {z = ι₂ (z₁ , _)} refl refl refl
      (ArrowSigmaSum.arrow₂ f₁ f₂)
      (ArrowSigmaSum.arrow₂ g₁ g₂)
      | just _ | [ q₂ ] | just _ | [ r₂ ] | just _ | [ s₂ ]
      = ArrowSigma.arrow₂
        (SplitCompose.map p₁ q₁ r₁ s₁ f₁ g₁)
        (DependentSplitCompose₁.map p₂ q₂ r₂ s₂ f₂ g₂)
      where
        q₁ = SplitBase.base-unbase a₁ x₁
        r₁ = SplitBase.base-unbase b₁ y₁
        s₁ = SplitBase.base-unbase c₁ z₁

    unmap
      : {x : Object'.Object (object-sigma X₂')}
      → {y : Object'.Object (object-sigma Y₂')}
      → {z : Object'.Object (object-sigma Z₂')}
      → (f : Arrow'.Arrow (arrow-sigma F₁' F₂') y z)
      → (g : Arrow'.Arrow (arrow-sigma G₁' G₂') x y)
      → Arrow'.ArrowEqual (arrow-sigma-sum H₁ H₂ a₁ c₁)
        (SplitMap.unmap (split-map-sigma o₁ o₂)
          (Compose.compose (compose-sigma j₁' j₂') f g))
        (Compose.compose (compose-sigma-sum j₁ j₂ a₁ b₁ c₁)
          (SplitMap.unmap (split-map-sigma m₁ m₂) f)
          (SplitMap.unmap (split-map-sigma n₁ n₂) g))
    unmap (ArrowSigma.arrow₁ f₁) (ArrowSigma.arrow₁ g₁)
      = ArrowSigmaSum.arrow₁
        (SplitCompose.unmap p₁ f₁ g₁)
    unmap (ArrowSigma.arrow₁ f₁) (ArrowSigma.arrow₂ g₁ _)
      = ArrowSigmaSum.arrow₁
        (SplitCompose.unmap p₁ f₁ g₁)
    unmap (ArrowSigma.arrow₂ f₁ _) (ArrowSigma.arrow₁ g₁)
      = ArrowSigmaSum.arrow₁
        (SplitCompose.unmap p₁ f₁ g₁)
    unmap (ArrowSigma.arrow₂ f₁ f₂) (ArrowSigma.arrow₂ g₁ g₂)
      = ArrowSigmaSum.arrow₂
        (SplitCompose.unmap p₁ f₁ g₁)
        (DependentSplitCompose₁.unmap p₂ f₂ g₂)

  split-compose-sigma
    : SplitCompose j₁ j₁' m₁ n₁ o₁
    → DependentSplitCompose₁ j₂ j₂' m₂ n₂ o₂
    → SplitCompose
      (compose-sigma-sum j₁ j₂ a₁ b₁ c₁)
      (compose-sigma j₁' j₂')
      (split-map-sigma m₁ m₂)
      (split-map-sigma n₁ n₂)
      (split-map-sigma o₁ o₂)
  split-compose-sigma p₁ p₂
    = record {SplitComposeSigma p₁ p₂}

-- ## Dependent

-- ### DependentSplitBase

dependent-split-base-sigma
  : {n : ℕ}
  → {X : ChainObject n}
  → (X₁' : DependentObject X)
  → {X₁'' : DependentObject X}
  → {X₂' X₂'' : DependentObject (chain-object-snoc X₁'')}
  → DependentSplitBase X₂' X₂''
  → DependentSplitBase
    (dependent-object-sigma-sum X₁' X₂')
    (dependent-object-sigma X₂'')
dependent-split-base-sigma {n = zero} X₁' a₂
  = split-base-sigma X₁' a₂
dependent-split-base-sigma {n = suc _} X₁' a₂
  = record
  { tail
    = λ x → dependent-split-base-sigma
      (DependentObject.tail X₁' x)
      (DependentSplitBase.tail a₂ x)
  }

-- ### DependentSplitMap

dependent-split-map-sigma
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₁'' : DependentObject X}
  → {Y₁' Y₁'' : DependentObject Y}
  → {X₂' X₂'' : DependentObject (chain-object-snoc X₁'')}
  → {Y₂' Y₂'' : DependentObject (chain-object-snoc Y₁'')}
  → {F₁ : DependentArrow X₁' Y₁'}
  → {F₁' : DependentArrow X₁'' Y₁''}
  → {F₂ : DependentArrow X₂' Y₂'}
  → {F₂' : DependentArrow X₂'' Y₂''}
  → {a₁ : DependentSplitBase X₁' X₁''}
  → {b₁ : DependentSplitBase Y₁' Y₁''}
  → {a₂ : DependentSplitBase X₂' X₂''}
  → {b₂ : DependentSplitBase Y₂' Y₂''}
  → DependentSplitMap F₁ F₁' a₁ b₁
  → DependentSplitMap F₂ F₂' a₂ b₂
  → DependentSplitMap
    (dependent-arrow-sigma-sum F₁ F₂ a₁ b₁)
    (dependent-arrow-sigma F₁' F₂')
    (dependent-split-base-sigma X₁' a₂)
    (dependent-split-base-sigma Y₁' b₂)
dependent-split-map-sigma {n = zero} m₁ m₂
  = split-map-sigma m₁ m₂
dependent-split-map-sigma {n = suc _} m₁ m₂
  = record
  { tail
    = λ x y → dependent-split-map-sigma
      (DependentSplitMap.tail m₁ x y)
      (DependentSplitMap.tail m₂ x y)
  }

-- ### DependentSplitIdentity

dependent-split-identity-sigma
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' X₁'' : DependentObject X}
  → {X₂' X₂'' : DependentObject (chain-object-snoc X₁'')}
  → {F₁ : DependentArrow X₁' X₁'}
  → {F₁' : DependentArrow X₁'' X₁''}
  → {F₂ : DependentArrow X₂' X₂'}
  → {F₂' : DependentArrow X₂'' X₂''}
  → {i₁ : DependentIdentity F₁}
  → {i₁' : DependentIdentity F₁'}
  → {i₂ : DependentIdentity F₂}
  → {i₂' : DependentIdentity F₂'}
  → {a₁ : DependentSplitBase X₁' X₁''}
  → {a₂ : DependentSplitBase X₂' X₂''}
  → {m₁ : DependentSplitMap F₁ F₁' a₁ a₁}
  → {m₂ : DependentSplitMap F₂ F₂' a₂ a₂}
  → DependentSplitIdentity i₁ i₁' m₁
  → DependentSplitIdentity i₂ i₂' m₂
  → DependentSplitIdentity
    (dependent-identity-sigma-sum i₁ i₂ a₁)
    (dependent-identity-sigma i₁' i₂')
    (dependent-split-map-sigma m₁ m₂)
dependent-split-identity-sigma {n = zero} p₁ p₂
  = split-identity-sigma p₁ p₂
dependent-split-identity-sigma {n = suc _} p₁ p₂
  = record
  { tail
    = λ x → dependent-split-identity-sigma
      (DependentSplitIdentity.tail p₁ x)
      (DependentSplitIdentity.tail p₂ x)
  }

-- ### DependentSplitCompose

dependent-split-compose-sigma
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X₁' X₁'' : DependentObject X}
  → {Y₁' Y₁'' : DependentObject Y}
  → {Z₁' Z₁'' : DependentObject Z}
  → {X₂' X₂'' : DependentObject (chain-object-snoc X₁'')}
  → {Y₂' Y₂'' : DependentObject (chain-object-snoc Y₁'')}
  → {Z₂' Z₂'' : DependentObject (chain-object-snoc Z₁'')}
  → {F₁ : DependentArrow Y₁' Z₁'}
  → {G₁ : DependentArrow X₁' Y₁'}
  → {H₁ : DependentArrow X₁' Z₁'}
  → {F₁' : DependentArrow Y₁'' Z₁''}
  → {G₁' : DependentArrow X₁'' Y₁''}
  → {H₁' : DependentArrow X₁'' Z₁''}
  → {F₂ : DependentArrow Y₂' Z₂'}
  → {G₂ : DependentArrow X₂' Y₂'}
  → {H₂ : DependentArrow X₂' Z₂'}
  → {F₂' : DependentArrow Y₂'' Z₂''}
  → {G₂' : DependentArrow X₂'' Y₂''}
  → {H₂' : DependentArrow X₂'' Z₂''}
  → {j₁ : DependentCompose F₁ G₁ H₁}
  → {j₁' : DependentCompose F₁' G₁' H₁'}
  → {j₂ : DependentCompose F₂ G₂ H₂}
  → {j₂' : DependentCompose F₂' G₂' H₂'}
  → {a₁ : DependentSplitBase X₁' X₁''}
  → {b₁ : DependentSplitBase Y₁' Y₁''}
  → {c₁ : DependentSplitBase Z₁' Z₁''}
  → {a₂ : DependentSplitBase X₂' X₂''}
  → {b₂ : DependentSplitBase Y₂' Y₂''}
  → {c₂ : DependentSplitBase Z₂' Z₂''}
  → {m₁ : DependentSplitMap F₁ F₁' b₁ c₁}
  → {n₁ : DependentSplitMap G₁ G₁' a₁ b₁}
  → {o₁ : DependentSplitMap H₁ H₁' a₁ c₁}
  → {m₂ : DependentSplitMap F₂ F₂' b₂ c₂}
  → {n₂ : DependentSplitMap G₂ G₂' a₂ b₂}
  → {o₂ : DependentSplitMap H₂ H₂' a₂ c₂}
  → DependentSplitCompose j₁ j₁' m₁ n₁ o₁
  → DependentSplitCompose j₂ j₂' m₂ n₂ o₂
  → DependentSplitCompose
    (dependent-compose-sigma-sum j₁ j₂ a₁ b₁ c₁)
    (dependent-compose-sigma j₁' j₂')
    (dependent-split-map-sigma m₁ m₂)
    (dependent-split-map-sigma n₁ n₂)
    (dependent-split-map-sigma o₁ o₂)
dependent-split-compose-sigma {n = zero} p₁ p₂
  = split-compose-sigma p₁ p₂
dependent-split-compose-sigma {n = suc _} p₁ p₂
  = record
  { tail
    = λ x y z → dependent-split-compose-sigma
      (DependentSplitCompose.tail p₁ x y z)
      (DependentSplitCompose.tail p₂ x y z)
  }

