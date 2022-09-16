module Category.State where

open import Category
  using (Category; ChainCategory; chain-category₀; chain-category₁)
open import Category.Core
  using (Arrow'; Associative; Compose; ComposeEqual; DependentArrow;
    DependentAssociative; DependentCompose; DependentComposeEqual;
    DependentIdentity; DependentObject; DependentPostcompose;
    DependentPrecompose; DependentSimplify; Identity; Object'; Postcompose;
    Precompose; Simplify)
open import Category.State.Lift
  using (DependentStateLift; DependentStateLift₁)
open import Data.Nat
  using (ℕ; suc)

-- ## Dependent

-- ### Definition

record DependentStateCategory'
  {n : ℕ}
  (C : ChainCategory n)
  : Set₁
  where

  no-eta-equality

  field

    {object}
      : DependentObject
        (ChainCategory.object C)

    {arrow}
      : DependentArrow object object

    simplify
      : DependentSimplify arrow

    {identity}
      : DependentIdentity arrow

    {compose}
      : DependentCompose arrow arrow arrow

    compose-equal
      : DependentComposeEqual compose

    precompose
      : DependentPrecompose identity compose

    postcompose
      : DependentPostcompose identity compose

    associative
      : DependentAssociative compose compose compose compose

    lift
      : DependentStateLift
        (ChainCategory.identity C) identity
        (ChainCategory.lift C)

DependentStateCategory
  = DependentStateCategory'

-- ### Module

module DependentStateCategory where

  open module DependentStateCategory'' {n C} C'
    = DependentStateCategory' {n} {C} C' public

  tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → DependentStateCategory C
    → (x : ChainCategory.Object C)
    → DependentStateCategory
      (ChainCategory.tail C x)
  tail C' x
    = record
    { simplify
      = DependentSimplify.tail (simplify C') x x
    ; compose-equal
      = DependentComposeEqual.tail (compose-equal C') x x x
    ; precompose
      = DependentPrecompose.tail (precompose C') x x
    ; postcompose
      = DependentPostcompose.tail (postcompose C') x x
    ; associative
      = DependentAssociative.tail (associative C') x x x x
    ; lift
      = DependentStateLift.tail (lift C') x
    }

-- ## Nondependent

-- ### Definition

StateCategory
  : Set₁
StateCategory
  = DependentStateCategory
    chain-category₀

-- ### Module

module StateCategory
  (C : StateCategory)
  where

  open DependentStateCategory' C public

  open Object' object public
    using () renaming
    ( Object
      to Object
    )

  open Arrow' arrow public
    using () renaming
    ( Arrow
      to Arrow
    ; ArrowEqual
      to ArrowEqual
    ; arrow-refl
      to arrow-refl
    ; arrow-sym
      to arrow-sym
    ; arrow-trans
      to arrow-trans
    ; arrow
      to arrow'
    )

  open Simplify simplify public
    using () renaming
    ( simplify
      to simplify'
    ; simplify-equal
      to simplify-equal
    )

  open Identity identity public
    using () renaming
    ( identity
      to identity'
    )

  open Compose compose public
    using () renaming
    ( compose
      to compose'
    )

  open ComposeEqual compose-equal public
    using () renaming
    ( compose-equal
      to compose-equal'
    )

  open Precompose precompose public
    using () renaming
    ( precompose
      to precompose'
    )

  open Postcompose postcompose public
    using () renaming
    ( postcompose
      to postcompose'
    )

  open Associative associative public
    using () renaming
    ( associative
      to associative'
    )

-- ## Dependent₁

-- ### Definition

DependentStateCategory₁
  : Category
  → Set₁
DependentStateCategory₁ C
  = DependentStateCategory
    (chain-category₁ C)

-- ### Module

module DependentStateCategory₁
  (C : Category)
  (C' : DependentStateCategory₁ C)
  where

  open DependentStateCategory' C' public
    using (lift)
  open DependentStateLift₁ lift public

  open module StateCategory' x
    = StateCategory (DependentStateCategory.tail C' x) public
    using (Object)
  open module StateCategory'' {x}
    = StateCategory (DependentStateCategory.tail C' x) public
    hiding (Object; lift)

