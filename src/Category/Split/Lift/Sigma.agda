module Category.Split.Lift.Sigma where

open import Category.Core
  using (Arrow'; ChainArrow; ChainCompose; ChainIdentity; ChainObject;
    DependentArrow; DependentArrow₁; DependentCompose; DependentIdentity;
    DependentObject; DependentObject₁; Object')
open import Category.Core.Sigma
  using (module ArrowSigma; arrow-sigma; object-sigma)
open import Category.Core.Sigma.Sum
  using (arrow-equal-sigma-sum₂; arrow-sigma-sum; object-sigma-sum)
open import Category.Core.Snoc
  using (chain-compose-snoc; chain-identity-snoc; chain-object-snoc)
open import Category.Lift
  using (ChainLift; ChainPath; DependentLift; DependentPath; DependentPath₁;
    Path)
open import Category.Lift.Sigma
  using (dependent-lift-sigma; dependent-path-sigma; path-sigma)
open import Category.Lift.Snoc
  using (chain-lift-snoc; chain-path-snoc)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitBase₁; DependentSplitMap;
    DependentSplitMap₁; SplitBase; SplitMap)
open import Category.Split.Core.Sigma
  using (dependent-split-map-sigma; split-base-sigma; split-map-sigma)
open import Category.Split.Lift
  using (DependentSplitLift; DependentSplitPath; DependentSplitPath₁; SplitPath;
    tt)
open import Category.State.Lift
  using (DependentStateLift; DependentStatePath; DependentStatePath₁; StatePath)
open import Category.State.Lift.Sigma.Sum
  using (dependent-state-lift-sigma-sum; dependent-state-path-sigma-sum;
    state-path-sigma-sum)
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
open import Data.Sum
  using (ι₂)

-- ## Base

-- ### SplitPath

module _
  {X₁ Y₁ X₁' Y₁' : Object'}
  {X₂ X₂' : DependentObject₁ X₁'}
  {Y₂ Y₂' : DependentObject₁ Y₁'}
  {F₁ : Arrow' X₁ Y₁}
  {F₁' : Arrow' X₁' Y₁'}
  {F₂ : DependentArrow₁ X₂ Y₂}
  {F₂' : DependentArrow₁ X₂' Y₂'}
  where

  module SplitPathSigma
    (p₁ : StatePath F₁)
    {p₁' : Path F₁'}
    {p₂ : DependentStatePath₁ F₂ p₁'}
    {p₂' : DependentPath₁ F₂' p₁'}
    {a₁ : SplitBase X₁ X₁'}
    {b₁ : SplitBase Y₁ Y₁'}
    {a₂ : DependentSplitBase₁ X₂ X₂'}
    {b₂ : DependentSplitBase₁ Y₂ Y₂'}
    (m₁ : SplitMap F₁ F₁' a₁ b₁)
    {m₂ : DependentSplitMap₁ F₂ F₂' a₂ b₂}
    (q₂ : DependentSplitPath₁ p₂ p₂' m₂)
    where

    base
      : (x : Object'.Object (object-sigma-sum X₁ X₂))
      → {x' : Object'.Object (object-sigma X₂')}
      → SplitBase.base (split-base-sigma X₁ a₂) x ≡ just x'
      → SplitBase.base (split-base-sigma Y₁ b₂)
        (StatePath.base (state-path-sigma-sum p₁ p₂ m₁) x)
      ≡ Path.base (path-sigma p₂') x'
    base (ι₂ (_ , x₂)) _
      with DependentSplitBase₁.base a₂ x₂
      | inspect (DependentSplitBase₁.base a₂) x₂
    base (ι₂ (x₁ , x₂)) refl | just x₂' | [ r₂ ]
      with Path.base p₁' x₁
      | inspect (Path.base p₁') x₁
    ... | nothing | _
      = refl
    ... | just _ | [ p₁'' ]
      with DependentPath₁.base p₂' p₁'' x₂'
      | DependentSplitBase₁.base b₂ (DependentStatePath₁.base p₂ p₁'' x₂)
      | DependentSplitPath₁.base q₂ p₁'' x₂ r₂
    ... | nothing | _ | refl
      = refl
    ... | just _ | _ | refl
      = refl

    base₁
      : {x₁ x₁' : Object'.Object X₁'}
      → (x₂ : DependentObject₁.Object X₂ x₁)
      → {x₂' : DependentObject₁.Object X₂' x₁'}
      → SplitBase.base (split-base-sigma X₁ a₂) (ι₂ (x₁ , x₂))
        ≡ just (x₁' , x₂')
      → x₁ ≡ x₁'
    base₁ x₂ _
      with DependentSplitBase₁.base a₂ x₂
    base₁ _ refl | just _
      = refl

    map
      : (x : Object'.Object (object-sigma-sum X₁ X₂))
      → {x' : Object'.Object (object-sigma X₂')}
      → {y' : Object'.Object (object-sigma Y₂')}
      → (q : Path.base (path-sigma p₂') x' ≡ just y')
      → (r : SplitBase.base (split-base-sigma X₁ a₂) x ≡ just x')
      → (s : SplitBase.base (split-base-sigma Y₁ b₂)
        (StatePath.base (state-path-sigma-sum p₁ p₂ m₁) x)
        ≡ just y')
      → Arrow'.ArrowEqual (arrow-sigma F₁' F₂')
        (SplitMap.map (split-map-sigma m₁ m₂) r s
          (StatePath.map (state-path-sigma-sum p₁ p₂ m₁) x))
        (Path.map (path-sigma p₂') x' q)
    map (ι₂ (x₁ , x₂)) _ r _
      with base₁ x₂ r
    ... | refl
      with Path.base p₁' x₁
      | inspect (Path.base p₁') x₁
    ... | just _ | _
      with DependentSplitBase₁.base a₂ x₂
      | inspect (DependentSplitBase₁.base a₂) x₂
    map (ι₂ (_ , x₂)) _ refl _
      | _ | _ | [ p₁'' ] | just x₂' | [ t₂ ]
      with DependentPath₁.base p₂' p₁'' x₂'
      | inspect (DependentPath₁.base p₂' p₁'') x₂'
      | DependentSplitBase₁.base b₂
        (DependentStatePath₁.base p₂ p₁'' x₂)
      | inspect (DependentSplitBase₁.base b₂)
        (DependentStatePath₁.base p₂ p₁'' x₂)
    map (ι₂ (x₁ , x₂)) refl _ refl
      | _ | just y₁ | [ p₁'' ] | _ | [ t₂ ]
      | just _ | [ p₂'' ] | just _ | [ u₂ ]
      = ArrowSigma.arrow₂
        (SplitMap.map-unmap m₁ t₁ u₁ f₁)
        (DependentSplitPath₁.map q₂ p₁'' x₂ p₂'' t₂ u₂)
      where
        f₁ = Path.map p₁' x₁ p₁''
        t₁ = SplitBase.base-unbase a₁ x₁
        u₁ = SplitBase.base-unbase b₁ y₁
    
    unmap
      : (x : Object'.Object (object-sigma X₂'))
      → {y : Object'.Object (object-sigma Y₂')}
      → (q : Path.base (path-sigma p₂') x ≡ just y)
      → Arrow'.ArrowEqual' (arrow-sigma-sum F₁ F₂ a₁ b₁)
        (SplitMap.unmap (split-map-sigma m₁ m₂)
          (Path.map (path-sigma p₂') x q))
        (StatePath.map (state-path-sigma-sum p₁ p₂ m₁)
          (SplitBase.unbase (split-base-sigma X₁ a₂) x))
    unmap (x₁ , x₂) _
      with Path.base p₁' x₁
      | inspect (Path.base p₁') x₁
    ... | just _ | [ p₁'' ]
      with DependentPath₁.base p₂' p₁'' x₂
      | inspect (DependentPath₁.base p₂' p₁'') x₂
    unmap (_ , x₂) refl | _ | [ p₁'' ] | just _ | [ p₂'' ]
      = arrow-equal-sigma-sum₂ a₁ b₁
        (Arrow'.arrow-refl F₁)
        (DependentSplitPath₁.unmap q₂ p₁'' x₂ p₂'')

  split-path-sigma
    : (p₁ : StatePath F₁)
    → {p₁' : Path F₁'}
    → {p₂ : DependentStatePath₁ F₂ p₁'}
    → {p₂' : DependentPath₁ F₂' p₁'}
    → {a₁ : SplitBase X₁ X₁'}
    → {b₁ : SplitBase Y₁ Y₁'}
    → {a₂ : DependentSplitBase₁ X₂ X₂'}
    → {b₂ : DependentSplitBase₁ Y₂ Y₂'}
    → (m₁ : SplitMap F₁ F₁' a₁ b₁)
    → {m₂ : DependentSplitMap₁ F₂ F₂' a₂ b₂}
    → DependentSplitPath₁ p₂ p₂' m₂
    → SplitPath
      (state-path-sigma-sum p₁ p₂ m₁)
      (path-sigma p₂')
      (split-map-sigma m₁ m₂)
  split-path-sigma p₁ m₁ q₂
    = record {SplitPathSigma p₁ m₁ q₂}

-- ## Dependent

-- ### DependentSplitPath

dependent-split-path-sigma
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₁'' : DependentObject X}
  → {Y₁' Y₁'' : DependentObject Y}
  → {X₂' X₂'' : DependentObject (chain-object-snoc X₁'')}
  → {Y₂' Y₂'' : DependentObject (chain-object-snoc Y₁'')}
  → {F : ChainArrow X Y}
  → {F₁' : DependentArrow X₁' Y₁'}
  → {F₁'' : DependentArrow X₁'' Y₁''}
  → {F₂' : DependentArrow X₂' Y₂'}
  → {F₂'' : DependentArrow X₂'' Y₂''}
  → {p : ChainPath F}
  → (p₁' : DependentStatePath F₁' p)
  → {p₁'' : DependentPath F₁'' p}
  → {p₂' : DependentStatePath F₂' (chain-path-snoc p₁'')}
  → {p₂'' : DependentPath F₂'' (chain-path-snoc p₁'')}
  → {a₁ : DependentSplitBase X₁' X₁''}
  → {b₁ : DependentSplitBase Y₁' Y₁''}
  → {a₂ : DependentSplitBase X₂' X₂''}
  → {b₂ : DependentSplitBase Y₂' Y₂''}
  → (m₁ : DependentSplitMap F₁' F₁'' a₁ b₁)
  → {m₂ : DependentSplitMap F₂' F₂'' a₂ b₂}
  → DependentSplitPath p₂' p₂'' m₂
  → DependentSplitPath
    (dependent-state-path-sigma-sum p₁' p₂' m₁)
    (dependent-path-sigma p₂'')
    (dependent-split-map-sigma m₁ m₂)
dependent-split-path-sigma {n = zero} p₁' m₁ q₂
  = split-path-sigma p₁' m₁ q₂
dependent-split-path-sigma {n = suc _} p₁' m₁ q₂
  = record
  { tail
    = λ x {y} p' → dependent-split-path-sigma
      (DependentStatePath.tail p₁' x p')
      (DependentSplitMap.tail m₁ x y)
      (DependentSplitPath.tail q₂ x p')
  }

-- ### DependentSplitLift

dependent-split-lift-sigma
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' X₁'' : DependentObject X}
  → {X₂' X₂'' : DependentObject (chain-object-snoc X₁'')}
  → {F : ChainArrow X X}
  → {F₁' : DependentArrow X₁' X₁'}
  → {F₁'' : DependentArrow X₁'' X₁''}
  → {F₂' : DependentArrow X₂' X₂'}
  → {F₂'' : DependentArrow X₂'' X₂''}
  → {i : ChainIdentity F}
  → {i₁' : DependentIdentity F₁'}
  → {i₁'' : DependentIdentity F₁''}
  → {i₂' : DependentIdentity F₂'}
  → {i₂'' : DependentIdentity F₂''}
  → {j : ChainCompose F F F}
  → {j₁'' : DependentCompose F₁'' F₁'' F₁''}
  → {j₂'' : DependentCompose F₂'' F₂'' F₂''}
  → {l : ChainLift F}
  → {l₁' : DependentStateLift i i₁' l}
  → {l₁'' : DependentLift i i₁'' j j₁'' l}
  → {l₂' : DependentStateLift
    (chain-identity-snoc i i₁'') i₂'
    (chain-lift-snoc l₁'')}
  → {l₂'' : DependentLift
    (chain-identity-snoc i i₁'') i₂''
    (chain-compose-snoc j j₁'') j₂''
    (chain-lift-snoc l₁'')}
  → {a₁ : DependentSplitBase X₁' X₁''}
  → {a₂ : DependentSplitBase X₂' X₂''}
  → {m₁ : DependentSplitMap F₁' F₁'' a₁ a₁}
  → {m₂ : DependentSplitMap F₂' F₂'' a₂ a₂}
  → (p₁ : DependentSplitLift l₁' l₁'' m₁)
  → DependentSplitLift l₂' l₂'' m₂
  → DependentSplitLift
    (dependent-state-lift-sigma-sum l₂' p₁)
    (dependent-lift-sigma l₂'')
    (dependent-split-map-sigma m₁ m₂)
dependent-split-lift-sigma {n = zero} _ _
  = tt
dependent-split-lift-sigma {n = suc _} {l₁' = l₁'} {m₁ = m₁} p₁ p₂
  = record
  { path
    = λ {x} {y} f → dependent-split-path-sigma
      (DependentStateLift.path l₁' f)
      (DependentSplitMap.tail m₁ x y)
      (DependentSplitLift.path p₂ f)
  ; tail
    = λ x → dependent-split-lift-sigma
      (DependentSplitLift.tail p₁ x)
      (DependentSplitLift.tail p₂ x)
  }

