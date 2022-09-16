module Category where

open import Category.Core
  using (Arrow'; Associative; ChainArrow; ChainCompose; ChainIdentity;
    ChainObject; Compose; ComposeEqual; DependentArrow; DependentAssociative;
    DependentCompose; DependentComposeEqual; DependentIdentity; DependentObject;
    DependentPostcompose; DependentPrecompose; Identity; Object'; Postcompose;
    Precompose; chain-compose₁; chain-identity₁)
open import Category.Lift
  using (ChainLift; DependentLift; DependentPrelift; DependentPrelift';
    chain-lift₁)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Chain

-- ### ChainCategory

-- #### Definition

record ChainCategory'
  (n : ℕ)
  : Set₁
  where

  field

    {object}
      : ChainObject n

    {arrow}
      : ChainArrow object object

    identity
      : ChainIdentity arrow

    compose
      : ChainCompose arrow arrow arrow

    lift
      : ChainLift arrow

ChainCategory
  = ChainCategory'

-- #### Module

module ChainCategory where

  open module ChainCategory'' {n} C
    = ChainCategory' {n} C public
  open module ChainObject' {n} C
    = ChainObject {n} (object C) public
    using (Object)
  open module ChainArrow' {n} C
    = ChainArrow {n} (arrow C) public
    using (Arrow; ArrowEqual; arrow-refl; arrow-sym; arrow-trans)
  open module ChainIdentity' {n} C
    = ChainIdentity {n} (identity C) public
    using (identity)
  open module ChainCompose' {n} C
    = ChainCompose {n} (compose C) public
    using (compose)

  tail
    : {n : ℕ}
    → (C : ChainCategory (suc n))
    → Object C
    → ChainCategory n
  tail C x
    = record
    { identity
      = ChainIdentity.tail (identity C) x
    ; compose
      = ChainCompose.tail (compose C) x x x
    ; lift
      = ChainLift.tail (lift C) x
    }

-- #### Construction

chain-category₀
  : ChainCategory zero
chain-category₀
  = record {}

-- ## Dependent

-- ### DependentPrecategory

record DependentPrecategory
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

    identity
      : DependentIdentity arrow

    {compose}
      : DependentCompose arrow arrow arrow

    lift
      : DependentPrelift
        (ChainCategory.compose C) compose
        (ChainCategory.lift C)

-- ### DependentPrecategory'

record DependentPrecategory'
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

    identity
      : DependentIdentity arrow

    compose
      : DependentCompose arrow arrow arrow

    lift
      : DependentPrelift' arrow
        (ChainCategory.lift C)

-- ### DependentCategory

-- #### Definition

record DependentCategory'
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
      : DependentLift
        (ChainCategory.identity C) identity
        (ChainCategory.compose C) compose
        (ChainCategory.lift C)

DependentCategory
  = DependentCategory'

-- #### Module

module DependentCategory where

  open module DependentCategory'' {n C} C'
    = DependentCategory' {n} {C} C' public

  tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → DependentCategory C
    → (x : ChainCategory.Object C)
    → DependentCategory
      (ChainCategory.tail C x)
  tail C' x
    = record
    { compose-equal
      = DependentComposeEqual.tail (compose-equal C') x x x
    ; precompose
      = DependentPrecompose.tail (precompose C') x x
    ; postcompose
      = DependentPostcompose.tail (postcompose C') x x
    ; associative
      = DependentAssociative.tail (associative C') x x x x
    ; lift
      = DependentLift.tail (lift C') x
    }

-- ## Nondependent

-- ### Precategory

-- #### Definition

Precategory
  : Set₁
Precategory
  = DependentPrecategory
    chain-category₀

-- #### Module

module Precategory
  (C : Precategory)
  where

  open DependentPrecategory C public

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

-- ### Precategory'

-- #### Definition

Precategory'
  : Set₁
Precategory'
  = DependentPrecategory'
    chain-category₀

-- #### Module

module Precategory'
  (C : Precategory')
  where

  open DependentPrecategory' C public

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

-- ### Category

-- #### Definition

Category
  : Set₁
Category
  = DependentCategory
    chain-category₀

-- #### Module

module Category
  (C : Category)
  where

  open DependentCategory' C public

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

-- #### Construction

chain-category₁
  : Category
  → ChainCategory (suc zero)
chain-category₁ C
  = record
  { identity
    = chain-identity₁
      (Category.identity C)
  ; compose
    = chain-compose₁
      (Category.compose C)
  ; lift
    = chain-lift₁
      (Category.arrow C)
  }

-- ## Dependent₁

-- ### Dependent₁Category

-- #### Definition

DependentCategory₁
  : Category
  → Set₁
DependentCategory₁ C
  = DependentCategory
    (chain-category₁ C)

-- #### Module

module DependentCategory₁
  (C : Category)
  (C' : DependentCategory₁ C)
  where

  open module Category' x
    = Category (DependentCategory.tail C' x) public
    using (Object)
  open module Category'' {x}
    = Category (DependentCategory.tail C' x) public
    hiding (Object)

