module Category.Split where

open import Category
  using (Category; ChainCategory; DependentCategory; DependentPrecategory;
    DependentPrecategory'; Precategory; Precategory')
open import Category.Bool
  using (DependentBoolFunction)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitCompose; DependentSplitIdentity;
    DependentSplitMap; SplitBase; SplitCompose; SplitIdentity; SplitMap)
open import Category.Split.Lift
  using (DependentSplitLift; DependentSplitLift'; DependentSplitPrelift;
    DependentSplitPrelift')
open import Category.State
  using (DependentStateCategory; StateCategory)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Dependent

-- ### DependentSplitPrefunctor

record DependentSplitPrefunctor
  {n : ℕ}
  {C : ChainCategory n}
  (C' : DependentStateCategory C)
  (D' : DependentPrecategory C)
  : Set
  where

  field

    {base}
      : DependentSplitBase
        (DependentStateCategory.object C')
        (DependentPrecategory.object D')

    {map}
      : DependentSplitMap
        (DependentStateCategory.arrow C')
        (DependentPrecategory.arrow D') base base

    identity
      : DependentSplitIdentity
        (DependentStateCategory.identity C')
        (DependentPrecategory.identity D') map

    compose
      : DependentSplitCompose
        (DependentStateCategory.compose C')
        (DependentPrecategory.compose D') map map map

    lift
      : DependentSplitPrelift
        (DependentStateCategory.lift C')
        (DependentPrecategory.lift D') map

-- ### DependentSplitPrefunctor'

record DependentSplitPrefunctor'
  {n : ℕ}
  {C : ChainCategory n}
  (C' : DependentCategory C)
  (D' : DependentPrecategory' C)
  : Set
  where

  field

    {base}
      : DependentSplitBase
        (DependentCategory.object C')
        (DependentPrecategory'.object D')

    {map}
      : DependentSplitMap
        (DependentCategory.arrow C')
        (DependentPrecategory'.arrow D') base base

    identity
      : DependentSplitIdentity
        (DependentCategory.identity C')
        (DependentPrecategory'.identity D') map

    compose
      : DependentSplitCompose
        (DependentCategory.compose C')
        (DependentPrecategory'.compose D') map map map

    lift
      : DependentSplitPrelift'
        (DependentCategory.lift C')
        (DependentPrecategory'.lift D') map

-- ### DependentSplitFunctor

-- #### Definition

record DependentSplitFunctor''
  {n : ℕ}
  {C : ChainCategory n}
  (C' : DependentStateCategory C)
  (D' : DependentCategory C)
  : Set
  where

  field

    {base}
      : DependentSplitBase
        (DependentStateCategory.object C')
        (DependentCategory.object D')

    {map}
      : DependentSplitMap
        (DependentStateCategory.arrow C')
        (DependentCategory.arrow D') base base

    identity
      : DependentSplitIdentity
        (DependentStateCategory.identity C')
        (DependentCategory.identity D') map

    compose
      : DependentSplitCompose
        (DependentStateCategory.compose C')
        (DependentCategory.compose D') map map map

    lift
      : DependentSplitLift
        (DependentStateCategory.lift C')
        (DependentCategory.lift D') map

DependentSplitFunctor
  = DependentSplitFunctor''

-- #### Module

module DependentSplitFunctor where

  open module DependentSplitFunctor'''' {n C C' D'} F
    = DependentSplitFunctor'' {n} {C} {C'} {D'} F public

  tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentStateCategory C}
    → {D' : DependentCategory C}
    → DependentSplitFunctor C' D'
    → (x : ChainCategory.Object C)
    → DependentSplitFunctor
      (DependentStateCategory.tail C' x)
      (DependentCategory.tail D' x)
  tail F x
    = record
    { identity
      = DependentSplitIdentity.tail (identity F) x
    ; compose
      = DependentSplitCompose.tail (compose F) x x x
    ; lift
      = DependentSplitLift.tail (lift F) x
    }

  bool-function
    : {n : ℕ}
    → {C : ChainCategory n}
    → {C' : DependentStateCategory C}
    → {D' : DependentCategory C}
    → DependentSplitFunctor C' D'
    → DependentBoolFunction C'
  bool-function {n = zero} F
    = SplitBase.bool-function (base F)
  bool-function {n = suc _} F
    = record
    { tail
      = λ x → bool-function (tail F x)
    }

-- ### DependentSplitFunctor'

-- #### Definition

record DependentSplitFunctor'''
  {n : ℕ}
  {C : ChainCategory n}
  (C' D' : DependentCategory C)
  : Set
  where

  field

    {base}
      : DependentSplitBase
        (DependentCategory.object C')
        (DependentCategory.object D')

    {map}
      : DependentSplitMap
        (DependentCategory.arrow C')
        (DependentCategory.arrow D') base base

    identity
      : DependentSplitIdentity
        (DependentCategory.identity C')
        (DependentCategory.identity D') map

    compose
      : DependentSplitCompose
        (DependentCategory.compose C')
        (DependentCategory.compose D') map map map

    lift
      : DependentSplitLift'
        (DependentCategory.lift C')
        (DependentCategory.lift D') map

DependentSplitFunctor'
  = DependentSplitFunctor'''

-- #### Module

module DependentSplitFunctor' where

  open module DependentSplitFunctor'''' {n C C' D'} F
    = DependentSplitFunctor''' {n} {C} {C'} {D'} F public

  tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' D' : DependentCategory C}
    → DependentSplitFunctor' C' D'
    → (x : ChainCategory.Object C)
    → DependentSplitFunctor'
      (DependentCategory.tail C' x)
      (DependentCategory.tail D' x)
  tail F x
    = record
    { identity
      = DependentSplitIdentity.tail (identity F) x
    ; compose
      = DependentSplitCompose.tail (compose F) x x x
    ; lift
      = DependentSplitLift'.tail (lift F) x
    }

-- ## Nondependent

-- ### SplitPrefunctor

-- #### Definition

SplitPrefunctor
  : StateCategory
  → Precategory
  → Set
SplitPrefunctor
  = DependentSplitPrefunctor

-- #### Module

module SplitPrefunctor
  {C : StateCategory}
  {D : Precategory}
  (F : SplitPrefunctor C D)
  where

  open DependentSplitPrefunctor F

  open SplitBase base public
    using () renaming
    ( base
      to base'
    ; unbase
      to unbase
    ; base-unbase
      to base-unbase
    )

  open SplitMap map public
    using () renaming
    ( map
      to map'
    ; map-equal
      to map-equal
    ; unmap
      to unmap
    ; unmap-equal
      to unmap-equal
    ; map-unmap
      to map-unmap
    )

  open SplitIdentity identity public
    using () renaming
    ( map
      to map-identity
    ; unmap
      to unmap-identity
    ; normalize-arrow
      to normalize-arrow
    ; normalize-valid
      to normalize-valid
    )

  open SplitCompose compose public
    using () renaming
    ( map
      to map-compose
    ; unmap
      to unmap-compose
    )

-- ### SplitPrefunctor'

-- #### Definition

SplitPrefunctor'
  : Category
  → Precategory'
  → Set
SplitPrefunctor'
  = DependentSplitPrefunctor'

-- #### Module

module SplitPrefunctor'
  {C : Category}
  {D : Precategory'}
  (F : SplitPrefunctor' C D)
  where

  open DependentSplitPrefunctor' F

  open SplitBase base public
    using () renaming
    ( base
      to base'
    ; unbase
      to unbase
    ; base-unbase
      to base-unbase
    )

  open SplitMap map public
    using () renaming
    ( map
      to map'
    ; map-equal
      to map-equal
    ; unmap
      to unmap
    ; unmap-equal
      to unmap-equal
    ; map-unmap
      to map-unmap
    )

  open SplitIdentity identity public
    using () renaming
    ( map
      to map-identity
    ; unmap
      to unmap-identity
    ; normalize-arrow
      to normalize-arrow
    ; normalize-valid
      to normalize-valid
    )

  open SplitCompose compose public
    using () renaming
    ( map
      to map-compose
    ; unmap
      to unmap-compose
    )

-- ### SplitFunctor

-- #### Definition

SplitFunctor
  : StateCategory
  → Category
  → Set
SplitFunctor
  = DependentSplitFunctor

-- #### Module

module SplitFunctor
  {C : StateCategory}
  {D : Category}
  (F : SplitFunctor C D)
  where

  open DependentSplitFunctor'' F public

  open SplitBase base public
    using () renaming
    ( base
      to base'
    ; unbase
      to unbase
    ; base-unbase
      to base-unbase
    )

  open SplitMap map public
    using () renaming
    ( map
      to map'
    ; map-equal
      to map-equal
    ; unmap
      to unmap
    ; unmap-equal
      to unmap-equal
    ; map-unmap
      to map-unmap
    )

  open SplitIdentity identity public
    using () renaming
    ( map
      to map-identity
    ; unmap
      to unmap-identity
    ; normalize-arrow
      to normalize-arrow
    ; normalize-valid
      to normalize-valid
    )

  open SplitCompose compose public
    using () renaming
    ( map
      to map-compose
    ; unmap
      to unmap-compose
    )

-- ### SplitFunctor'

-- #### Definition

SplitFunctor'
  : Category
  → Category
  → Set
SplitFunctor'
  = DependentSplitFunctor'

-- #### Module

module SplitFunctor'
  {C D : Category}
  (F : SplitFunctor' C D)
  where

  open DependentSplitFunctor''' F public

  open SplitBase base public
    using () renaming
    ( base
      to base'
    ; unbase
      to unbase
    ; base-unbase
      to base-unbase
    )

  open SplitMap map public
    using () renaming
    ( map
      to map'
    ; map-equal
      to map-equal
    ; unmap
      to unmap
    ; unmap-equal
      to unmap-equal
    ; map-unmap
      to map-unmap
    )

  open SplitIdentity identity public
    using () renaming
    ( map
      to map-identity
    ; unmap
      to unmap-identity
    ; normalize-arrow
      to normalize-arrow
    ; normalize-valid
      to normalize-valid
    )

  open SplitCompose compose public
    using () renaming
    ( map
      to map-compose
    ; unmap
      to unmap-compose
    )

