module Category.State.Lift.Sigma.Sum where

open import Category.Core
  using (Arrow'; ChainArrow; ChainCompose; ChainIdentity; ChainObject;
    DependentArrow; DependentArrow₁; DependentCompose; DependentIdentity;
    DependentIdentity₁; DependentObject; DependentObject₁; Identity; Object')
open import Category.Core.Sigma.Sum
  using (module ArrowSigmaSum; arrow-equal-sigma-sum₁; arrow-equal-sigma-sum₂;
    arrow-sigma-sum; dependent-arrow-sigma-sum; dependent-identity-sigma-sum;
    identity-sigma-sum; object-sigma-sum)
open import Category.Core.Snoc
  using (chain-identity-snoc; chain-object-snoc)
open import Category.Lift
  using (ChainLift; ChainPath; DependentLift; DependentPath; DependentPathEqual;
    DependentPathIdentity; Path; PathEqual; PathIdentity)
open import Category.Lift.Snoc
  using (chain-lift-snoc; chain-path-snoc)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitMap; SplitBase; SplitMap)
open import Category.Split.Lift
  using (DependentSplitLift; DependentSplitPath; SplitPath)
open import Category.State.Lift
  using (DependentStateLift; DependentStatePath; DependentStatePath₁;
    DependentStatePathEqual; DependentStatePathEqual₁;
    DependentStatePathIdentity; DependentStatePathIdentity₁; StatePath;
    StatePathEqual; StatePathIdentity; tt)
open import Data.Equal
  using (refl; sub)
open import Data.Function
  using (_$_)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (_,_)
open import Data.Sum
  using (ι₁; ι₂)

-- ## Base

-- ### StatePath

module _
  {X₁ Y₁ X₁' Y₁' : Object'}
  {X₂ : DependentObject₁ X₁'}
  {Y₂ : DependentObject₁ Y₁'}
  {F₁ : Arrow' X₁ Y₁}
  {F₁' : Arrow' X₁' Y₁'}
  {F₂ : DependentArrow₁ X₂ Y₂}
  where

  module StatePathSigmaSum
    (p₁ : StatePath F₁)
    {p₁' : Path F₁'}
    (p₂ : DependentStatePath₁ F₂ p₁')
    {a₁ : SplitBase X₁ X₁'}
    {b₁ : SplitBase Y₁ Y₁'}
    (m₁ : SplitMap F₁ F₁' a₁ b₁)
    where

    base
      : Object'.Object (object-sigma-sum X₁ X₂)
      → Object'.Object (object-sigma-sum Y₁ Y₂)
    base (ι₁ x₁)
      = ι₁ (StatePath.base p₁ x₁)
    base (ι₂ (x₁ , x₂))
      with Path.base p₁' x₁
      | inspect (Path.base p₁') x₁
    ... | nothing | _
      = ι₁ (StatePath.base p₁ (SplitBase.unbase a₁ x₁))
    ... | just y₁ | [ p₁'' ]
      = ι₂ (y₁ , DependentStatePath₁.base p₂ p₁'' x₂)

    map
      : (x : Object'.Object (object-sigma-sum X₁ X₂))
      → Arrow'.Arrow (arrow-sigma-sum F₁ F₂ a₁ b₁) x (base x)
    map (ι₁ x₁)
      = ArrowSigmaSum.arrow₁
        (StatePath.map p₁ x₁)
    map (ι₂ (x₁ , x₂))
      with Path.base p₁' x₁
      | inspect (Path.base p₁') x₁
    ... | nothing | _
      = ArrowSigmaSum.arrow₁
        (StatePath.map p₁ (SplitBase.unbase a₁ x₁))
    ... | just _ | [ p₁'' ]
      = ArrowSigmaSum.arrow₂
        (SplitMap.unmap m₁ (Path.map p₁' x₁ p₁''))
        (DependentStatePath₁.map p₂ p₁'' x₂)

  state-path-sigma-sum
    : StatePath F₁
    → {p₁' : Path F₁'}
    → DependentStatePath₁ F₂ p₁'
    → {a₁ : SplitBase X₁ X₁'}
    → {b₁ : SplitBase Y₁ Y₁'}
    → SplitMap F₁ F₁' a₁ b₁
    → StatePath
      (arrow-sigma-sum F₁ F₂ a₁ b₁)
  state-path-sigma-sum p₁ p₂ m₁
    = record {StatePathSigmaSum p₁ p₂ m₁}

-- ### StatePathEqual

module _
  {X₁ Y₁ X₁' Y₁' : Object'}
  {X₂ : DependentObject₁ X₁'}
  {Y₂ : DependentObject₁ Y₁'}
  {F₁ : Arrow' X₁ Y₁}
  {F₁' : Arrow' X₁' Y₁'}
  {F₂ : DependentArrow₁ X₂ Y₂}
  {p₁₁ p₂₁ : StatePath F₁}
  {p₁₁' p₂₁' : Path F₁'}
  {p₁₂ : DependentStatePath₁ F₂ p₁₁'}
  {p₂₂ : DependentStatePath₁ F₂ p₂₁'}
  where

  module StatePathEqualSigmaSum
    (q₁ : StatePathEqual p₁₁ p₂₁)
    (q₁' : PathEqual p₁₁' p₂₁')
    (q₂ : DependentStatePathEqual₁ p₁₂ p₂₂)
    {a₁ : SplitBase X₁ X₁'}
    {b₁ : SplitBase Y₁ Y₁'}
    (m₁ : SplitMap F₁ F₁' a₁ b₁)
    where

    map
      : (x : Object'.Object (object-sigma-sum X₁ X₂))
      → Arrow'.ArrowEqual' (arrow-sigma-sum F₁ F₂ a₁ b₁)
        (StatePath.map (state-path-sigma-sum p₁₁ p₁₂ m₁) x)
        (StatePath.map (state-path-sigma-sum p₂₁ p₂₂ m₁) x)
    map (ι₁ x₁)
      = arrow-equal-sigma-sum₁ F₂ a₁ b₁ refl
        (sub ι₁ (StatePathEqual.base q₁ x₁))
        (StatePathEqual.map q₁ x₁)
    map (ι₂ (x₁ , x₂))
      with Path.base p₁₁' x₁
      | inspect (Path.base p₁₁') x₁
      | Path.base p₂₁' x₁
      | inspect (Path.base p₂₁') x₁
      | PathEqual.base q₁' x₁
    ... | nothing | _ | _ | _ | refl
      = arrow-equal-sigma-sum₁ F₂ a₁ b₁ refl
        (sub ι₁ (StatePathEqual.base q₁ (SplitBase.unbase a₁ x₁)))
        (StatePathEqual.map q₁ (SplitBase.unbase a₁ x₁))
    ... | just _ | [ p₁₁'' ] | _ | [ p₂₁'' ] | refl
      = arrow-equal-sigma-sum₂ a₁ b₁
        (SplitMap.unmap-equal m₁ (PathEqual.map q₁' x₁ p₁₁'' p₂₁''))
        (DependentStatePathEqual₁.map q₂ p₁₁'' p₂₁'' x₂)

  state-path-equal-sigma-sum
    : StatePathEqual p₁₁ p₂₁
    → PathEqual p₁₁' p₂₁'
    → DependentStatePathEqual₁ p₁₂ p₂₂
    → {a₁ : SplitBase X₁ X₁'}
    → {b₁ : SplitBase Y₁ Y₁'}
    → (m₁ : SplitMap F₁ F₁' a₁ b₁)
    → StatePathEqual
      (state-path-sigma-sum p₁₁ p₁₂ m₁)
      (state-path-sigma-sum p₂₁ p₂₂ m₁)
  state-path-equal-sigma-sum q₁ q₁' q₂ m₁
    = record {StatePathEqualSigmaSum q₁ q₁' q₂ m₁}

-- ### StatePathIdentity

module _
  {X₁ X₁' : Object'}
  {X₂ : DependentObject₁ X₁'}
  {F₁ : Arrow' X₁ X₁}
  {F₁' : Arrow' X₁' X₁'}
  {F₂ : DependentArrow₁ X₂ X₂}
  {i₁ : Identity F₁}
  {i₁' : Identity F₁'}
  {i₂ : DependentIdentity₁ F₂}
  {p₁ : StatePath F₁}
  {p₁' : Path F₁'}
  {p₂ : DependentStatePath₁ F₂ p₁'}
  where

  module StatePathIdentitySigmaSum
    (q₁ : StatePathIdentity i₁ p₁)
    (q₁' : PathIdentity i₁' p₁')
    (q₂ : DependentStatePathIdentity₁ i₂ p₂)
    {a₁ : SplitBase X₁ X₁'}
    {m₁ : SplitMap F₁ F₁' a₁ a₁}
    (r₁ : SplitPath p₁ p₁' m₁)
    where

    map
      : (x : Object'.Object (object-sigma-sum X₁ X₂))
      → Arrow'.ArrowEqual' (arrow-sigma-sum F₁ F₂ a₁ a₁)
        (StatePath.map (state-path-sigma-sum p₁ p₂ m₁) x)
        (Identity.identity (identity-sigma-sum i₁ i₂ a₁) x)
    map (ι₁ x₁)
      = arrow-equal-sigma-sum₁ F₂ a₁ a₁ refl
        (sub ι₁ (StatePathIdentity.base q₁ x₁))
        (StatePathIdentity.map q₁ x₁)
    map (ι₂ (x₁ , x₂))
      with Path.base p₁' x₁
      | inspect (Path.base p₁') x₁
      | PathIdentity.base q₁' x₁
    ... | _ | [ p₁'' ] | refl
      = arrow-equal-sigma-sum₂ a₁ a₁ t₁ t₂
      where
        t₁ = Arrow'.arrow-equal' F₁
          $ Arrow'.arrow-trans' F₁ (SplitPath.unmap r₁ x₁ p₁'')
          $ StatePathIdentity.map q₁ (SplitBase.unbase a₁ x₁)
        t₂ = DependentStatePathIdentity₁.map q₂ p₁'' x₂

  state-path-identity-sigma-sum
    : StatePathIdentity i₁ p₁
    → PathIdentity i₁' p₁'
    → DependentStatePathIdentity₁ i₂ p₂
    → {a₁ : SplitBase X₁ X₁'}
    → {m₁ : SplitMap F₁ F₁' a₁ a₁}
    → SplitPath p₁ p₁' m₁
    → StatePathIdentity
      (identity-sigma-sum i₁ i₂ a₁)
      (state-path-sigma-sum p₁ p₂ m₁)
  state-path-identity-sigma-sum q₁ q₁' q₂ r₁
    = record {StatePathIdentitySigmaSum q₁ q₁' q₂ r₁}

-- ## Dependent

-- ### DependentStatePath

dependent-state-path-sigma-sum
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₁'' : DependentObject X}
  → {Y₁' Y₁'' : DependentObject Y}
  → {X₂' : DependentObject (chain-object-snoc X₁'')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁'')}
  → {F : ChainArrow X Y}
  → {F₁' : DependentArrow X₁' Y₁'}
  → {F₁'' : DependentArrow X₁'' Y₁''}
  → {F₂' : DependentArrow X₂' Y₂'}
  → {p : ChainPath F}
  → DependentStatePath F₁' p
  → {p₁'' : DependentPath F₁'' p}
  → DependentStatePath F₂' (chain-path-snoc p₁'')
  → {a₁ : DependentSplitBase X₁' X₁''}
  → {b₁ : DependentSplitBase Y₁' Y₁''}
  → DependentSplitMap F₁' F₁'' a₁ b₁
  → DependentStatePath
    (dependent-arrow-sigma-sum F₁' F₂' a₁ b₁) p
dependent-state-path-sigma-sum {n = zero} p₁' p₂' m₁
  = state-path-sigma-sum p₁' p₂' m₁
dependent-state-path-sigma-sum {n = suc _} p₁' p₂' m₁
  = record
  { tail
    = λ x {y} p' → dependent-state-path-sigma-sum
      (DependentStatePath.tail p₁' x p')
      (DependentStatePath.tail p₂' x p')
      (DependentSplitMap.tail m₁ x y)
  }

-- ### DependentStatePathEqual

dependent-state-path-equal-sigma-sum
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₁'' : DependentObject X}
  → {Y₁' Y₁'' : DependentObject Y}
  → {X₂' : DependentObject (chain-object-snoc X₁'')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁'')}
  → {F : ChainArrow X Y}
  → {F₁' : DependentArrow X₁' Y₁'}
  → {F₁'' : DependentArrow X₁'' Y₁''}
  → {F₂' : DependentArrow X₂' Y₂'}
  → {p₁ p₂ : ChainPath F}
  → {p₁₁' : DependentStatePath F₁' p₁}
  → {p₂₁' : DependentStatePath F₁' p₂}
  → {p₁₁'' : DependentPath F₁'' p₁}
  → {p₂₁'' : DependentPath F₁'' p₂}
  → {p₁₂' : DependentStatePath F₂' (chain-path-snoc p₁₁'')}
  → {p₂₂' : DependentStatePath F₂' (chain-path-snoc p₂₁'')}
  → DependentStatePathEqual p₁₁' p₂₁'
  → DependentPathEqual p₁₁'' p₂₁''
  → DependentStatePathEqual p₁₂' p₂₂'
  → {a₁ : DependentSplitBase X₁' X₁''}
  → {b₁ : DependentSplitBase Y₁' Y₁''}
  → (m₁ : DependentSplitMap F₁' F₁'' a₁ b₁)
  → DependentStatePathEqual
    (dependent-state-path-sigma-sum p₁₁' p₁₂' m₁)
    (dependent-state-path-sigma-sum p₂₁' p₂₂' m₁)
dependent-state-path-equal-sigma-sum {n = zero} q₁ q₁' q₂ m₁
  = state-path-equal-sigma-sum q₁ q₁' q₂ m₁
dependent-state-path-equal-sigma-sum {n = suc _} q₁ q₁' q₂ m₁
  = record
  { tail
    = λ x {y} p₁' p₂' → dependent-state-path-equal-sigma-sum
      (DependentStatePathEqual.tail q₁ x p₁' p₂')
      (DependentPathEqual.tail q₁' x p₁' p₂')
      (DependentStatePathEqual.tail q₂ x p₁' p₂')
      (DependentSplitMap.tail m₁ x y)
  }

-- ### DependentStatePathIdentity

dependent-state-path-identity-sigma-sum
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' X₁'' : DependentObject X}
  → {X₂' : DependentObject (chain-object-snoc X₁'')}
  → {F : ChainArrow X X}
  → {F₁' : DependentArrow X₁' X₁'}
  → {F₁'' : DependentArrow X₁'' X₁''}
  → {F₂' : DependentArrow X₂' X₂'}
  → {i₁ : DependentIdentity F₁'}
  → {i₁' : DependentIdentity F₁''}
  → {i₂ : DependentIdentity F₂'}
  → {p : ChainPath F}
  → {p₁' : DependentStatePath F₁' p}
  → {p₁'' : DependentPath F₁'' p}
  → {p₂' : DependentStatePath F₂' (chain-path-snoc p₁'')}
  → DependentStatePathIdentity i₁ p₁'
  → DependentPathIdentity i₁' p₁''
  → DependentStatePathIdentity i₂ p₂'
  → {a₁ : DependentSplitBase X₁' X₁''}
  → {m₁ : DependentSplitMap F₁' F₁'' a₁ a₁}
  → DependentSplitPath p₁' p₁'' m₁
  → DependentStatePathIdentity
    (dependent-identity-sigma-sum i₁ i₂ a₁)
    (dependent-state-path-sigma-sum p₁' p₂' m₁)
dependent-state-path-identity-sigma-sum {n = zero} q₁ q₁' q₂ r₁
  = state-path-identity-sigma-sum q₁ q₁' q₂ r₁
dependent-state-path-identity-sigma-sum {n = suc _} q₁ q₁' q₂ r₁
  = record
  { tail
    = λ {x} p' → dependent-state-path-identity-sigma-sum
      (DependentStatePathIdentity.tail q₁ p')
      (DependentPathIdentity.tail q₁' p')
      (DependentStatePathIdentity.tail q₂ p')
      (DependentSplitPath.tail r₁ x p')
  }

-- ### DependentStateLift

dependent-state-lift-sigma-sum
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' X₁'' : DependentObject X}
  → {X₂' : DependentObject (chain-object-snoc X₁'')}
  → {F : ChainArrow X X}
  → {F₁' : DependentArrow X₁' X₁'}
  → {F₁'' : DependentArrow X₁'' X₁''}
  → {F₂' : DependentArrow X₂' X₂'}
  → {i : ChainIdentity F}
  → {i₁' : DependentIdentity F₁'}
  → {i₁'' : DependentIdentity F₁''}
  → {i₂' : DependentIdentity F₂'}
  → {j : ChainCompose F F F}
  → {j₁'' : DependentCompose F₁'' F₁'' F₁''}
  → {l : ChainLift F}
  → {l₁' : DependentStateLift i i₁' l}
  → {l₁'' : DependentLift i i₁'' j j₁'' l}
  → DependentStateLift
    (chain-identity-snoc i i₁'') i₂'
    (chain-lift-snoc l₁'')
  → {a₁ : DependentSplitBase X₁' X₁''}
  → {m₁ : DependentSplitMap F₁' F₁'' a₁ a₁}
  → DependentSplitLift l₁' l₁'' m₁
  → DependentStateLift i
    (dependent-identity-sigma-sum i₁' i₂' a₁) l
dependent-state-lift-sigma-sum {n = zero} _ _
  = tt
dependent-state-lift-sigma-sum {n = suc _}
  {i = i} {l₁' = l₁'} {l₁'' = l₁''} l₂'
  {m₁ = m₁} p₁
  = record
  { path
    = λ {x} {y} f → dependent-state-path-sigma-sum
      (DependentStateLift.path l₁' f)
      (DependentStateLift.path l₂' f)
      (DependentSplitMap.tail m₁ x y)
  ; path-equal
    = λ {x} {y} q → dependent-state-path-equal-sigma-sum
      (DependentStateLift.path-equal l₁' q)
      (DependentLift.path-equal l₁'' q)
      (DependentStateLift.path-equal l₂' q)
      (DependentSplitMap.tail m₁ x y)
  ; path-identity
    = λ x → dependent-state-path-identity-sigma-sum
      (DependentStateLift.path-identity l₁' x)
      (DependentLift.path-identity l₁'' x)
      (DependentStateLift.path-identity l₂' x)
      (DependentSplitLift.path p₁
        (ChainIdentity.identity i x))
  ; tail
    = λ x → dependent-state-lift-sigma-sum
      (DependentStateLift.tail l₂' x)
      (DependentSplitLift.tail p₁ x)
  }

