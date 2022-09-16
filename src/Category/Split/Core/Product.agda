module Category.Split.Core.Product where

open import Category.Core
  using (Arrow'; ChainObject; Compose; DependentArrow; DependentCompose;
    DependentIdentity; DependentObject; Identity; Object')
open import Category.Core.Product
  using (arrow-product; compose-product; dependent-arrow-product;
    dependent-compose-product; dependent-identity-product;
    dependent-object-product; identity-product; object-product)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitCompose; DependentSplitIdentity;
    DependentSplitMap; SplitBase; SplitCompose; SplitIdentity; SplitMap)
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

-- ## Base

-- ### SplitBase

module _
  {X₁ X₂ X₁' X₂' : Object'}
  where

  module SplitBaseProduct
    (a₁ : SplitBase X₁ X₁')
    (a₂ : SplitBase X₂ X₂')
    where

    base
      : Object'.Object (object-product X₁ X₂)
      → Maybe (Object'.Object (object-product X₁' X₂'))
    base (x₁ , x₂)
      with SplitBase.base a₁ x₁
      | SplitBase.base a₂ x₂
    ... | nothing | _
      = nothing
    ... | _ | nothing
      = nothing
    ... | just x₁' | just x₂'
      = just (x₁' , x₂')

    unbase
      : Object'.Object (object-product X₁' X₂')
      → Object'.Object (object-product X₁ X₂)
    unbase (x₁ , x₂)
      = SplitBase.unbase a₁ x₁
      , SplitBase.unbase a₂ x₂

    base-unbase
      : (x : Object'.Object (object-product X₁' X₂'))
      → base (unbase x) ≡ just x
    base-unbase (x₁ , x₂)
      with SplitBase.base a₁ (SplitBase.unbase a₁ x₁)
      | SplitBase.base-unbase a₁ x₁
      | SplitBase.base a₂ (SplitBase.unbase a₂ x₂)
      | SplitBase.base-unbase a₂ x₂
    ... | _ | refl | _ | refl
      = refl

  split-base-product
    : SplitBase X₁ X₁'
    → SplitBase X₂ X₂'
    → SplitBase
      (object-product X₁ X₂)
      (object-product X₁' X₂')
  split-base-product a₁ a₂
    = record {SplitBaseProduct a₁ a₂}

-- ### SplitMap

module _
  {X₁ X₂ Y₁ Y₂ X₁' X₂' Y₁' Y₂' : Object'}
  {F₁ : Arrow' X₁ Y₁}
  {F₂ : Arrow' X₂ Y₂}
  {F₁' : Arrow' X₁' Y₁'}
  {F₂' : Arrow' X₂' Y₂'}
  {a₁ : SplitBase X₁ X₁'}
  {a₂ : SplitBase X₂ X₂'}
  {b₁ : SplitBase Y₁ Y₁'}
  {b₂ : SplitBase Y₂ Y₂'}
  where

  module SplitMapProduct
    (m₁ : SplitMap F₁ F₁' a₁ b₁)
    (m₂ : SplitMap F₂ F₂' a₂ b₂)
    where

    map
      : {x : Object'.Object (object-product X₁ X₂)}
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → {x' : Object'.Object (object-product X₁' X₂')}
      → {y' : Object'.Object (object-product Y₁' Y₂')}
      → SplitBase.base (split-base-product a₁ a₂) x ≡ just x'
      → SplitBase.base (split-base-product b₁ b₂) y ≡ just y'
      → Arrow'.Arrow (arrow-product F₁ F₂) x y
      → Arrow'.Arrow (arrow-product F₁' F₂') x' y'
    map {x = (x₁ , x₂)} {y = (y₁ , y₂)} _ _ _
      with SplitBase.base a₁ x₁
      | inspect (SplitBase.base a₁) x₁
      | SplitBase.base a₂ x₂
      | inspect (SplitBase.base a₂) x₂
      | SplitBase.base b₁ y₁
      | inspect (SplitBase.base b₁) y₁
      | SplitBase.base b₂ y₂
      | inspect (SplitBase.base b₂) y₂
    map refl refl (f₁ , f₂)
      | just _ | [ p₁ ] | just _ | [ p₂ ]
      | just _ | [ q₁ ] | just _ | [ q₂ ]
      = SplitMap.map m₁ p₁ q₁ f₁
      , SplitMap.map m₂ p₂ q₂ f₂

    map-equal
      : {x : Object'.Object (object-product X₁ X₂)}
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → {x' : Object'.Object (object-product X₁' X₂')}
      → {y' : Object'.Object (object-product Y₁' Y₂')}
      → {f₁ f₂ : Arrow'.Arrow (arrow-product F₁ F₂) x y}
      → (p : SplitBase.base (split-base-product a₁ a₂) x ≡ just x')
      → (q : SplitBase.base (split-base-product b₁ b₂) y ≡ just y')
      → Arrow'.ArrowEqual (arrow-product F₁ F₂) f₁ f₂
      → Arrow'.ArrowEqual (arrow-product F₁' F₂') (map p q f₁) (map p q f₂)
    map-equal {x = (x₁ , x₂)} {y = (y₁ , y₂)} _ _ _
      with SplitBase.base a₁ x₁
      | inspect (SplitBase.base a₁) x₁
      | SplitBase.base a₂ x₂
      | inspect (SplitBase.base a₂) x₂
      | SplitBase.base b₁ y₁
      | inspect (SplitBase.base b₁) y₁
      | SplitBase.base b₂ y₂
      | inspect (SplitBase.base b₂) y₂
    map-equal refl refl (r₁ , r₂)
      | just _ | [ p₁ ] | just _ | [ p₂ ]
      | just _ | [ q₁ ] | just _ | [ q₂ ]
      = SplitMap.map-equal m₁ p₁ q₁ r₁
      , SplitMap.map-equal m₂ p₂ q₂ r₂

    unmap
      : {x : Object'.Object (object-product X₁' X₂')}
      → {y : Object'.Object (object-product Y₁' Y₂')}
      → Arrow'.Arrow (arrow-product F₁' F₂') x y
      → Arrow'.Arrow (arrow-product F₁ F₂)
        (SplitBase.unbase (split-base-product a₁ a₂) x)
        (SplitBase.unbase (split-base-product b₁ b₂) y)
    unmap (f₁ , f₂)
      = SplitMap.unmap m₁ f₁
      , SplitMap.unmap m₂ f₂

    unmap-equal
      : {x : Object'.Object (object-product X₁' X₂')}
      → {y : Object'.Object (object-product Y₁' Y₂')}
      → {f₁ f₂ : Arrow'.Arrow (arrow-product F₁' F₂') x y}
      → Arrow'.ArrowEqual (arrow-product F₁' F₂') f₁ f₂
      → Arrow'.ArrowEqual (arrow-product F₁ F₂) (unmap f₁) (unmap f₂)
    unmap-equal (p₁ , p₂)
      = SplitMap.unmap-equal m₁ p₁
      , SplitMap.unmap-equal m₂ p₂

    map-unmap
      : {x : Object'.Object (object-product X₁' X₂')}
      → {y : Object'.Object (object-product Y₁' Y₂')}
      → (p : SplitBase.base (split-base-product a₁ a₂)
        (SplitBase.unbase (split-base-product a₁ a₂) x)
        ≡ just x)
      → (q : SplitBase.base (split-base-product b₁ b₂)
        (SplitBase.unbase (split-base-product b₁ b₂) y)
        ≡ just y)
      → (f : Arrow'.Arrow (arrow-product F₁' F₂') x y)
      → Arrow'.ArrowEqual (arrow-product F₁' F₂') (map p q (unmap f)) f
    map-unmap {x = (x₁ , x₂)} {y = (y₁ , y₂)} _ _ _
      with SplitBase.base a₁ (SplitBase.unbase a₁ x₁)
      | inspect (SplitBase.base a₁) (SplitBase.unbase a₁ x₁)
      | SplitBase.base a₂ (SplitBase.unbase a₂ x₂)
      | inspect (SplitBase.base a₂) (SplitBase.unbase a₂ x₂)
      | SplitBase.base b₁ (SplitBase.unbase b₁ y₁)
      | inspect (SplitBase.base b₁) (SplitBase.unbase b₁ y₁)
      | SplitBase.base b₂ (SplitBase.unbase b₂ y₂)
      | inspect (SplitBase.base b₂) (SplitBase.unbase b₂ y₂)
    map-unmap refl refl (f₁ , f₂)
      | just _ | [ p₁ ] | just _ | [ p₂ ]
      | just _ | [ q₁ ] | just _ | [ q₂ ]
      = SplitMap.map-unmap m₁ p₁ q₁ f₁
      , SplitMap.map-unmap m₂ p₂ q₂ f₂

  split-map-product
    : SplitMap F₁ F₁' a₁ b₁
    → SplitMap F₂ F₂' a₂ b₂
    → SplitMap
      (arrow-product F₁ F₂)
      (arrow-product F₁' F₂')
      (split-base-product a₁ a₂)
      (split-base-product b₁ b₂)
  split-map-product m₁ m₂
    = record {SplitMapProduct m₁ m₂}

-- ### SplitIdentity

module _
  {X₁ X₂ X₁' X₂' : Object'}
  {F₁ : Arrow' X₁ X₁}
  {F₂ : Arrow' X₂ X₂}
  {F₁' : Arrow' X₁' X₁'}
  {F₂' : Arrow' X₂' X₂'}
  {i₁ : Identity F₁}
  {i₂ : Identity F₂}
  {i₁' : Identity F₁'}
  {i₂' : Identity F₂'}
  {a₁ : SplitBase X₁ X₁'}
  {a₂ : SplitBase X₂ X₂'}
  {m₁ : SplitMap F₁ F₁' a₁ a₁}
  {m₂ : SplitMap F₂ F₂' a₂ a₂}
  where

  module SplitIdentityProduct
    (p₁ : SplitIdentity i₁ i₁' m₁)
    (p₂ : SplitIdentity i₂ i₂' m₂)
    where

    map
      : (x : Object'.Object (object-product X₁ X₂))
      → {x' : Object'.Object (object-product X₁' X₂')}
      → (q : SplitBase.base (split-base-product a₁ a₂) x ≡ just x')
      → Arrow'.ArrowEqual (arrow-product F₁' F₂')
        (SplitMap.map (split-map-product m₁ m₂) q q
          (Identity.identity (identity-product i₁ i₂) x))
        (Identity.identity (identity-product i₁' i₂') x')
    map (x₁ , x₂) _
      with SplitBase.base a₁ x₁
      | inspect (SplitBase.base a₁) x₁
      | SplitBase.base a₂ x₂
      | inspect (SplitBase.base a₂) x₂
    map (x₁ , x₂) refl
      | just _ | [ q₁ ] | just _ | [ q₂ ]
      = SplitIdentity.map p₁ x₁ q₁
      , SplitIdentity.map p₂ x₂ q₂

    unmap
      : (x : Object'.Object (object-product X₁' X₂'))
      → Arrow'.ArrowEqual (arrow-product F₁ F₂)
        (SplitMap.unmap (split-map-product m₁ m₂)
          (Identity.identity (identity-product i₁' i₂') x))
        (Identity.identity (identity-product i₁ i₂)
          (SplitBase.unbase (split-base-product a₁ a₂) x))
    unmap (x₁ , x₂)
      = SplitIdentity.unmap p₁ x₁
      , SplitIdentity.unmap p₂ x₂

    normalize-arrow
      : (x : Object'.Object (object-product X₁ X₂))
      → {x' : Object'.Object (object-product X₁' X₂')}
      → SplitBase.base (split-base-product a₁ a₂) x ≡ just x'
      → Arrow'.Arrow (arrow-product F₁ F₂) x
        (SplitBase.unbase (split-base-product a₁ a₂) x')
    normalize-arrow (x₁ , x₂) _
      with SplitBase.base a₁ x₁
      | inspect (SplitBase.base a₁) x₁
      | SplitBase.base a₂ x₂
      | inspect (SplitBase.base a₂) x₂
    normalize-arrow (x₁ , x₂) refl
      | just _ | [ q₁ ] | just _ | [ q₂ ]
      = SplitIdentity.normalize-arrow p₁ x₁ q₁
      , SplitIdentity.normalize-arrow p₂ x₂ q₂

    normalize-valid
      : (x : Object'.Object (object-product X₁ X₂))
      → {x' : Object'.Object (object-product X₁' X₂')}
      → (q : SplitBase.base (split-base-product a₁ a₂) x ≡ just x')
      → (r : SplitBase.base (split-base-product a₁ a₂)
        (SplitBase.unbase (split-base-product a₁ a₂) x')
        ≡ just x')
      → Arrow'.ArrowEqual (arrow-product F₁' F₂')
        (SplitMap.map (split-map-product m₁ m₂) q r (normalize-arrow x q))
        (Identity.identity (identity-product i₁' i₂') x')
    normalize-valid (x₁ , x₂) {x' = (x₁' , x₂')} _ _
      with SplitBase.base a₁ x₁
      | inspect (SplitBase.base a₁) x₁
      | SplitBase.base a₂ x₂
      | inspect (SplitBase.base a₂) x₂
      | SplitBase.base a₁ (SplitBase.unbase a₁ x₁')
      | inspect (SplitBase.base a₁) (SplitBase.unbase a₁ x₁')
      | SplitBase.base a₂ (SplitBase.unbase a₂ x₂')
      | inspect (SplitBase.base a₂) (SplitBase.unbase a₂ x₂')
    normalize-valid (x₁ , x₂) refl refl
      | just _ | [ q₁ ] | just _ | [ q₂ ]
      | just _ | [ r₁ ] | just _ | [ r₂ ]
      = SplitIdentity.normalize-valid p₁ x₁ q₁ r₁
      , SplitIdentity.normalize-valid p₂ x₂ q₂ r₂

  split-identity-product
    : SplitIdentity i₁ i₁' m₁
    → SplitIdentity i₂ i₂' m₂
    → SplitIdentity
      (identity-product i₁ i₂)
      (identity-product i₁' i₂')
      (split-map-product m₁ m₂)
  split-identity-product p₁ p₂
    = record {SplitIdentityProduct p₁ p₂}

-- ### SplitCompose

module _
  {X₁ X₂ Y₁ Y₂ Z₁ Z₂ X₁' X₂' Y₁' Y₂' Z₁' Z₂' : Object'}
  {F₁ : Arrow' Y₁ Z₁}
  {F₂ : Arrow' Y₂ Z₂}
  {G₁ : Arrow' X₁ Y₁}
  {G₂ : Arrow' X₂ Y₂}
  {H₁ : Arrow' X₁ Z₁}
  {H₂ : Arrow' X₂ Z₂}
  {F₁' : Arrow' Y₁' Z₁'}
  {F₂' : Arrow' Y₂' Z₂'}
  {G₁' : Arrow' X₁' Y₁'}
  {G₂' : Arrow' X₂' Y₂'}
  {H₁' : Arrow' X₁' Z₁'}
  {H₂' : Arrow' X₂' Z₂'}
  {j₁ : Compose F₁ G₁ H₁}
  {j₂ : Compose F₂ G₂ H₂}
  {j₁' : Compose F₁' G₁' H₁'}
  {j₂' : Compose F₂' G₂' H₂'}
  {a₁ : SplitBase X₁ X₁'}
  {a₂ : SplitBase X₂ X₂'}
  {b₁ : SplitBase Y₁ Y₁'}
  {b₂ : SplitBase Y₂ Y₂'}
  {c₁ : SplitBase Z₁ Z₁'}
  {c₂ : SplitBase Z₂ Z₂'}
  {m₁ : SplitMap F₁ F₁' b₁ c₁}
  {m₂ : SplitMap F₂ F₂' b₂ c₂}
  {n₁ : SplitMap G₁ G₁' a₁ b₁}
  {n₂ : SplitMap G₂ G₂' a₂ b₂}
  {o₁ : SplitMap H₁ H₁' a₁ c₁}
  {o₂ : SplitMap H₂ H₂' a₂ c₂}
  where

  module SplitComposeProduct
    (p₁ : SplitCompose j₁ j₁' m₁ n₁ o₁)
    (p₂ : SplitCompose j₂ j₂' m₂ n₂ o₂)
    where

    map
      : {x : Object'.Object (object-product X₁ X₂)}
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → {z : Object'.Object (object-product Z₁ Z₂)}
      → {x' : Object'.Object (object-product X₁' X₂')}
      → {y' : Object'.Object (object-product Y₁' Y₂')}
      → {z' : Object'.Object (object-product Z₁' Z₂')}
      → (q : SplitBase.base (split-base-product a₁ a₂) x ≡ just x')
      → (r : SplitBase.base (split-base-product b₁ b₂) y ≡ just y')
      → (s : SplitBase.base (split-base-product c₁ c₂) z ≡ just z')
      → (f : Arrow'.Arrow (arrow-product F₁ F₂) y z)
      → (g : Arrow'.Arrow (arrow-product G₁ G₂) x y)
      → Arrow'.ArrowEqual (arrow-product H₁' H₂')
        (SplitMap.map (split-map-product o₁ o₂) q s
          (Compose.compose (compose-product j₁ j₂) f g))
        (Compose.compose (compose-product j₁' j₂')
          (SplitMap.map (split-map-product m₁ m₂) r s f)
          (SplitMap.map (split-map-product n₁ n₂) q r g))
    map {x = (x₁ , x₂)} {y = (y₁ , y₂)} {z = (z₁ , z₂)} _ _ _ _ _
      with SplitBase.base a₁ x₁
      | inspect (SplitBase.base a₁) x₁
      | SplitBase.base a₂ x₂
      | inspect (SplitBase.base a₂) x₂
      | SplitBase.base b₁ y₁
      | inspect (SplitBase.base b₁) y₁
      | SplitBase.base b₂ y₂
      | inspect (SplitBase.base b₂) y₂
      | SplitBase.base c₁ z₁
      | inspect (SplitBase.base c₁) z₁
      | SplitBase.base c₂ z₂
      | inspect (SplitBase.base c₂) z₂
    map refl refl refl (f₁ , f₂) (g₁ , g₂)
      | just _ | [ q₁ ] | just _ | [ q₂ ]
      | just _ | [ r₁ ] | just _ | [ r₂ ]
      | just _ | [ s₁ ] | just _ | [ s₂ ]
      = SplitCompose.map p₁ q₁ r₁ s₁ f₁ g₁
      , SplitCompose.map p₂ q₂ r₂ s₂ f₂ g₂

    unmap
      : {x : Object'.Object (object-product X₁' X₂')}
      → {y : Object'.Object (object-product Y₁' Y₂')}
      → {z : Object'.Object (object-product Z₁' Z₂')}
      → (f : Arrow'.Arrow (arrow-product F₁' F₂') y z)
      → (g : Arrow'.Arrow (arrow-product G₁' G₂') x y)
      → Arrow'.ArrowEqual (arrow-product H₁ H₂)
        (SplitMap.unmap (split-map-product o₁ o₂)
          (Compose.compose (compose-product j₁' j₂') f g))
        (Compose.compose (compose-product j₁ j₂)
          (SplitMap.unmap (split-map-product m₁ m₂) f)
          (SplitMap.unmap (split-map-product n₁ n₂) g))
    unmap (f₁ , f₂) (g₁ , g₂)
      = SplitCompose.unmap p₁ f₁ g₁
      , SplitCompose.unmap p₂ f₂ g₂

  split-compose-product
    : SplitCompose j₁ j₁' m₁ n₁ o₁
    → SplitCompose j₂ j₂' m₂ n₂ o₂
    → SplitCompose
      (compose-product j₁ j₂)
      (compose-product j₁' j₂')
      (split-map-product m₁ m₂)
      (split-map-product n₁ n₂)
      (split-map-product o₁ o₂)
  split-compose-product p₁ p₂
    = record {SplitComposeProduct p₁ p₂}

-- ## Dependent

-- ### DependentSplitBase

dependent-split-base-product
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' X₂' X₁'' X₂'' : DependentObject X}
  → DependentSplitBase X₁' X₁''
  → DependentSplitBase X₂' X₂''
  → DependentSplitBase
    (dependent-object-product X₁' X₂')
    (dependent-object-product X₁'' X₂'')
dependent-split-base-product {n = zero} a₁ a₂
  = split-base-product a₁ a₂
dependent-split-base-product {n = suc _} a₁ a₂
  = record
  { tail
    = λ x → dependent-split-base-product
      (DependentSplitBase.tail a₁ x)
      (DependentSplitBase.tail a₂ x)
  }

-- ### DependentSplitMap

dependent-split-map-product
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₂' X₁'' X₂'' : DependentObject X}
  → {Y₁' Y₂' Y₁'' Y₂'' : DependentObject Y}
  → {F₁ : DependentArrow X₁' Y₁'}
  → {F₂ : DependentArrow X₂' Y₂'}
  → {F₁' : DependentArrow X₁'' Y₁''}
  → {F₂' : DependentArrow X₂'' Y₂''}
  → {a₁ : DependentSplitBase X₁' X₁''}
  → {a₂ : DependentSplitBase X₂' X₂''}
  → {b₁ : DependentSplitBase Y₁' Y₁''}
  → {b₂ : DependentSplitBase Y₂' Y₂''}
  → DependentSplitMap F₁ F₁' a₁ b₁
  → DependentSplitMap F₂ F₂' a₂ b₂
  → DependentSplitMap
    (dependent-arrow-product F₁ F₂)
    (dependent-arrow-product F₁' F₂')
    (dependent-split-base-product a₁ a₂)
    (dependent-split-base-product b₁ b₂)
dependent-split-map-product {n = zero} m₁ m₂
  = split-map-product m₁ m₂
dependent-split-map-product {n = suc _} m₁ m₂
  = record
  { tail
    = λ x y → dependent-split-map-product
      (DependentSplitMap.tail m₁ x y)
      (DependentSplitMap.tail m₂ x y)
  }

-- ### DependentSplitIdentity

dependent-split-identity-product
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' X₂' X₁'' X₂'' : DependentObject X}
  → {F₁ : DependentArrow X₁' X₁'}
  → {F₂ : DependentArrow X₂' X₂'}
  → {F₁' : DependentArrow X₁'' X₁''}
  → {F₂' : DependentArrow X₂'' X₂''}
  → {i₁ : DependentIdentity F₁}
  → {i₂ : DependentIdentity F₂}
  → {i₁' : DependentIdentity F₁'}
  → {i₂' : DependentIdentity F₂'}
  → {a₁ : DependentSplitBase X₁' X₁''}
  → {a₂ : DependentSplitBase X₂' X₂''}
  → {m₁ : DependentSplitMap F₁ F₁' a₁ a₁}
  → {m₂ : DependentSplitMap F₂ F₂' a₂ a₂}
  → DependentSplitIdentity i₁ i₁' m₁
  → DependentSplitIdentity i₂ i₂' m₂
  → DependentSplitIdentity
    (dependent-identity-product i₁ i₂)
    (dependent-identity-product i₁' i₂')
    (dependent-split-map-product m₁ m₂)
dependent-split-identity-product {n = zero} p₁ p₂
  = split-identity-product p₁ p₂
dependent-split-identity-product {n = suc _} p₁ p₂
  = record
  { tail
    = λ x → dependent-split-identity-product
      (DependentSplitIdentity.tail p₁ x)
      (DependentSplitIdentity.tail p₂ x)
  }

-- ### DependentSplitCompose

dependent-split-compose-product
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X₁' X₂' X₁'' X₂'' : DependentObject X}
  → {Y₁' Y₂' Y₁'' Y₂'' : DependentObject Y}
  → {Z₁' Z₂' Z₁'' Z₂'' : DependentObject Z}
  → {F₁ : DependentArrow Y₁' Z₁'}
  → {F₂ : DependentArrow Y₂' Z₂'}
  → {G₁ : DependentArrow X₁' Y₁'}
  → {G₂ : DependentArrow X₂' Y₂'}
  → {H₁ : DependentArrow X₁' Z₁'}
  → {H₂ : DependentArrow X₂' Z₂'}
  → {F₁' : DependentArrow Y₁'' Z₁''}
  → {F₂' : DependentArrow Y₂'' Z₂''}
  → {G₁' : DependentArrow X₁'' Y₁''}
  → {G₂' : DependentArrow X₂'' Y₂''}
  → {H₁' : DependentArrow X₁'' Z₁''}
  → {H₂' : DependentArrow X₂'' Z₂''}
  → {j₁ : DependentCompose F₁ G₁ H₁}
  → {j₂ : DependentCompose F₂ G₂ H₂}
  → {j₁' : DependentCompose F₁' G₁' H₁'}
  → {j₂' : DependentCompose F₂' G₂' H₂'}
  → {a₁ : DependentSplitBase X₁' X₁''}
  → {a₂ : DependentSplitBase X₂' X₂''}
  → {b₁ : DependentSplitBase Y₁' Y₁''}
  → {b₂ : DependentSplitBase Y₂' Y₂''}
  → {c₁ : DependentSplitBase Z₁' Z₁''}
  → {c₂ : DependentSplitBase Z₂' Z₂''}
  → {m₁ : DependentSplitMap F₁ F₁' b₁ c₁}
  → {m₂ : DependentSplitMap F₂ F₂' b₂ c₂}
  → {n₁ : DependentSplitMap G₁ G₁' a₁ b₁}
  → {n₂ : DependentSplitMap G₂ G₂' a₂ b₂}
  → {o₁ : DependentSplitMap H₁ H₁' a₁ c₁}
  → {o₂ : DependentSplitMap H₂ H₂' a₂ c₂}
  → DependentSplitCompose j₁ j₁' m₁ n₁ o₁
  → DependentSplitCompose j₂ j₂' m₂ n₂ o₂
  → DependentSplitCompose
    (dependent-compose-product j₁ j₂)
    (dependent-compose-product j₁' j₂')
    (dependent-split-map-product m₁ m₂)
    (dependent-split-map-product n₁ n₂)
    (dependent-split-map-product o₁ o₂)
dependent-split-compose-product {n = zero} p₁ p₂
  = split-compose-product p₁ p₂
dependent-split-compose-product {n = suc _} p₁ p₂
  = record
  { tail
    = λ x y z → dependent-split-compose-product
      (DependentSplitCompose.tail p₁ x y z)
      (DependentSplitCompose.tail p₂ x y z)
  }

