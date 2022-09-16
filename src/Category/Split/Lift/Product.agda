module Category.Split.Lift.Product where

open import Category.Core
  using (Arrow'; ChainArrow; ChainCompose; ChainIdentity; ChainObject;
    DependentArrow; DependentCompose; DependentIdentity; DependentObject;
    Object')
open import Category.Core.Product
  using (arrow-equal-product; arrow-product; object-product)
open import Category.Lift
  using (ChainLift; ChainPath; DependentLift; DependentPath; Path)
open import Category.Lift.Product
  using (dependent-lift-product; dependent-path-product; path-product)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitMap; SplitBase; SplitMap)
open import Category.Split.Core.Product
  using (dependent-split-map-product; split-base-product; split-map-product)
open import Category.Split.Lift
  using (DependentSplitLift; DependentSplitPath; SplitPath; tt)
open import Category.State.Lift
  using (DependentStateLift; DependentStatePath; StatePath)
open import Category.State.Lift.Product
  using (dependent-state-lift-product; dependent-state-path-product;
    state-path-product)
open import Data.Equal
  using (_≡_; refl)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (_,_)

-- ## Base

-- ### SplitPath

module _
  {X₁ X₂ Y₁ Y₂ X₁' X₂' Y₁' Y₂' : Object'}
  {F₁ : Arrow' X₁ Y₁}
  {F₂ : Arrow' X₂ Y₂}
  {F₁' : Arrow' X₁' Y₁'}
  {F₂' : Arrow' X₂' Y₂'}
  {p₁ : StatePath F₁}
  {p₂ : StatePath F₂}
  {p₁' : Path F₁'}
  {p₂' : Path F₂'}
  {a₁ : SplitBase X₁ X₁'}
  {a₂ : SplitBase X₂ X₂'}
  {b₁ : SplitBase Y₁ Y₁'}
  {b₂ : SplitBase Y₂ Y₂'}
  {m₁ : SplitMap F₁ F₁' a₁ b₁}
  {m₂ : SplitMap F₂ F₂' a₂ b₂}
  where

  module SplitPathProduct
    (q₁ : SplitPath p₁ p₁' m₁)
    (q₂ : SplitPath p₂ p₂' m₂)
    where

    base
      : (x : Object'.Object (object-product X₁ X₂))
      → {x' : Object'.Object (object-product X₁' X₂')}
      → SplitBase.base (split-base-product a₁ a₂) x ≡ just x'
      → SplitBase.base (split-base-product b₁ b₂)
        (StatePath.base (state-path-product p₁ p₂) x)
      ≡ Path.base (path-product p₁' p₂') x'
    base (x₁ , x₂) _
      with SplitBase.base a₁ x₁
      | inspect (SplitBase.base a₁) x₁
      | SplitBase.base a₂ x₂
      | inspect (SplitBase.base a₂) x₂
    base (x₁ , x₂) refl
      | just x₁' | [ r₁ ] | just x₂' | [ r₂ ]
      with SplitBase.base b₁ (StatePath.base p₁ x₁)
      | Path.base p₁' x₁'
      | SplitPath.base q₁ x₁ r₁
      | SplitBase.base b₂ (StatePath.base p₂ x₂)
      | Path.base p₂' x₂'
      | SplitPath.base q₂ x₂ r₂
    ... | nothing | _ | refl | _ | _ | refl
      = refl
    ... | just _ | _ | refl | nothing | _ | refl
      = refl
    ... | just _ | _ | refl | just _ | _ | refl
      = refl

    map
      : (x : Object'.Object (object-product X₁ X₂))
      → {x' : Object'.Object (object-product X₁' X₂')}
      → {y' : Object'.Object (object-product Y₁' Y₂')}
      → (r : Path.base (path-product p₁' p₂') x' ≡ just y')
      → (s : SplitBase.base (split-base-product a₁ a₂) x ≡ just x')
      → (t : SplitBase.base (split-base-product b₁ b₂)
        (StatePath.base (state-path-product p₁ p₂) x)
        ≡ just y')
      → Arrow'.ArrowEqual (arrow-product F₁' F₂')
        (SplitMap.map (split-map-product m₁ m₂) s t
          (StatePath.map (state-path-product p₁ p₂) x))
        (Path.map (path-product p₁' p₂') x' r)
    map (x₁ , x₂) {x' = (x₁' , x₂')} _ _ _
      with Path.base p₁' x₁'
      | inspect (Path.base p₁') x₁'
      | Path.base p₂' x₂'
      | inspect (Path.base p₂') x₂'
      | SplitBase.base a₁ x₁
      | inspect (SplitBase.base a₁) x₁
      | SplitBase.base a₂ x₂
      | inspect (SplitBase.base a₂) x₂
      | SplitBase.base b₁ (StatePath.base p₁ x₁)
      | inspect (SplitBase.base b₁) (StatePath.base p₁ x₁)
      | SplitBase.base b₂ (StatePath.base p₂ x₂)
      | inspect (SplitBase.base b₂) (StatePath.base p₂ x₂)
    map (x₁ , x₂) refl refl refl
      | just _ | [ r₁ ] | just _ | [ r₂ ]
      | just _ | [ s₁ ] | just _ | [ s₂ ]
      | just _ | [ t₁ ] | just _ | [ t₂ ]
      = SplitPath.map q₁ x₁ r₁ s₁ t₁
      , SplitPath.map q₂ x₂ r₂ s₂ t₂
    
    unmap
      : (x : Object'.Object (object-product X₁' X₂'))
      → {y : Object'.Object (object-product Y₁' Y₂')}
      → (r : Path.base (path-product p₁' p₂') x ≡ just y)
      → Arrow'.ArrowEqual' (arrow-product F₁ F₂)
        (SplitMap.unmap (split-map-product m₁ m₂)
          (Path.map (path-product p₁' p₂') x r))
        (StatePath.map (state-path-product p₁ p₂)
          (SplitBase.unbase (split-base-product a₁ a₂) x))
    unmap (x₁ , x₂) _
      with Path.base p₁' x₁
      | inspect (Path.base p₁') x₁
      | Path.base p₂' x₂
      | inspect (Path.base p₂') x₂
    unmap (x₁ , x₂) refl
      | just _ | [ r₁ ] | just _ | [ r₂ ]
      = arrow-equal-product
        (SplitPath.unmap q₁ x₁ r₁)
        (SplitPath.unmap q₂ x₂ r₂)

  split-path-product
    : SplitPath p₁ p₁' m₁
    → SplitPath p₂ p₂' m₂
    → SplitPath
      (state-path-product p₁ p₂)
      (path-product p₁' p₂')
      (split-map-product m₁ m₂)
  split-path-product q₁ q₂
    = record {SplitPathProduct q₁ q₂}

-- ## Dependent

-- ### DependentSplitPath

dependent-split-path-product
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₂' X₁'' X₂'' : DependentObject X}
  → {Y₁' Y₂' Y₁'' Y₂'' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F₁' : DependentArrow X₁' Y₁'}
  → {F₂' : DependentArrow X₂' Y₂'}
  → {F₁'' : DependentArrow X₁'' Y₁''}
  → {F₂'' : DependentArrow X₂'' Y₂''}
  → {p : ChainPath F}
  → {p₁' : DependentStatePath F₁' p}
  → {p₂' : DependentStatePath F₂' p}
  → {p₁'' : DependentPath F₁'' p}
  → {p₂'' : DependentPath F₂'' p}
  → {a₁ : DependentSplitBase X₁' X₁''}
  → {a₂ : DependentSplitBase X₂' X₂''}
  → {b₁ : DependentSplitBase Y₁' Y₁''}
  → {b₂ : DependentSplitBase Y₂' Y₂''}
  → {m₁ : DependentSplitMap F₁' F₁'' a₁ b₁}
  → {m₂ : DependentSplitMap F₂' F₂'' a₂ b₂}
  → DependentSplitPath p₁' p₁'' m₁
  → DependentSplitPath p₂' p₂'' m₂
  → DependentSplitPath
    (dependent-state-path-product p₁' p₂')
    (dependent-path-product p₁'' p₂'')
    (dependent-split-map-product m₁ m₂)
dependent-split-path-product {n = zero} q₁ q₂
  = split-path-product q₁ q₂
dependent-split-path-product {n = suc _} q₁ q₂
  = record
  { tail
    = λ x p' → dependent-split-path-product
      (DependentSplitPath.tail q₁ x p')
      (DependentSplitPath.tail q₂ x p')
  }

-- ### DependentSplitLift

dependent-split-lift-product
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' X₂' X₁'' X₂'' : DependentObject X}
  → {F : ChainArrow X X}
  → {F₁' : DependentArrow X₁' X₁'}
  → {F₂' : DependentArrow X₂' X₂'}
  → {F₁'' : DependentArrow X₁'' X₁''}
  → {F₂'' : DependentArrow X₂'' X₂''}
  → {i : ChainIdentity F}
  → {i₁' : DependentIdentity F₁'}
  → {i₂' : DependentIdentity F₂'}
  → {i₁'' : DependentIdentity F₁''}
  → {i₂'' : DependentIdentity F₂''}
  → {j : ChainCompose F F F}
  → {j₁'' : DependentCompose F₁'' F₁'' F₁''}
  → {j₂'' : DependentCompose F₂'' F₂'' F₂''}
  → {l : ChainLift F}
  → {l₁' : DependentStateLift i i₁' l}
  → {l₂' : DependentStateLift i i₂' l}
  → {l₁'' : DependentLift i i₁'' j j₁'' l}
  → {l₂'' : DependentLift i i₂'' j j₂'' l}
  → {a₁ : DependentSplitBase X₁' X₁''}
  → {a₂ : DependentSplitBase X₂' X₂''}
  → {m₁ : DependentSplitMap F₁' F₁'' a₁ a₁}
  → {m₂ : DependentSplitMap F₂' F₂'' a₂ a₂}
  → DependentSplitLift l₁' l₁'' m₁
  → DependentSplitLift l₂' l₂'' m₂
  → DependentSplitLift
    (dependent-state-lift-product l₁' l₂')
    (dependent-lift-product l₁'' l₂'')
    (dependent-split-map-product m₁ m₂)
dependent-split-lift-product {n = zero} _ _
  = tt
dependent-split-lift-product {n = suc _} p₁ p₂
  = record
  { path
    = λ f → dependent-split-path-product
      (DependentSplitLift.path p₁ f)
      (DependentSplitLift.path p₂ f)
  ; tail
    = λ x → dependent-split-lift-product
      (DependentSplitLift.tail p₁ x)
      (DependentSplitLift.tail p₂ x)
  }

