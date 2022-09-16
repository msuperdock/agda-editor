module Category.Core.Collection where

open import Category.Core
  using (Arrow'; ChainObject; Compose; DependentArrow; DependentCompose;
    DependentIdentity; DependentObject; Identity; Object')
open import Category.Core.List
  using (module ArrowList; module ComposeList; module IdentityList)
open import Category.Core.Relation
  using (DependentRelation)
open import Data.Collection
  using (Collection)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Relation
  using (Relation)

-- ## Base

-- ### Object'

object-collection
  : {X : Object'}
  → Relation (Object'.Object X)
  → Object'
object-collection R
  = record
  { Object
    = Collection R
  }

-- ### Arrow'

module _
  {X Y : Object'}
  where

  module ArrowCollection
    (R : Relation (Object'.Object X))
    (S : Relation (Object'.Object Y))
    (F : Arrow' X Y)
    where

    record Arrow
      (xs : Object'.Object (object-collection R))
      (ys : Object'.Object (object-collection S))
      : Set
      where

      constructor

        arrow

      field

        elements
          : ArrowList.Arrow F
            (Collection.elements xs)
            (Collection.elements ys)

    record ArrowEqual
      {xs : Object'.Object (object-collection R)}
      {ys : Object'.Object (object-collection S)}
      (fs₁ fs₂ : Arrow xs ys)
      : Set
      where

      constructor

        arrow-equal

      field

        elements
          : ArrowList.ArrowEqual F
            (Arrow.elements fs₁)
            (Arrow.elements fs₂)

    arrow-refl
      : {xs : Object'.Object (object-collection R)}
      → {ys : Object'.Object (object-collection S)}
      → {fs : Arrow xs ys}
      → ArrowEqual fs fs
    arrow-refl
      = arrow-equal (ArrowList.arrow-refl F)

    arrow-sym
      : {xs : Object'.Object (object-collection R)}
      → {ys : Object'.Object (object-collection S)}
      → {fs₁ fs₂ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual fs₂ fs₁
    arrow-sym (arrow-equal ps)
      = arrow-equal (ArrowList.arrow-sym F ps)

    arrow-trans
      : {xs : Object'.Object (object-collection R)}
      → {ys : Object'.Object (object-collection S)}
      → {fs₁ fs₂ fs₃ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual fs₂ fs₃
      → ArrowEqual fs₁ fs₃
    arrow-trans (arrow-equal ps₁) (arrow-equal ps₂)
      = arrow-equal (ArrowList.arrow-trans F ps₁ ps₂)
    
  arrow-collection
    : (R : Relation (Object'.Object X))
    → (S : Relation (Object'.Object Y))
    → Arrow' X Y
    → Arrow'
      (object-collection R)
      (object-collection S)
  arrow-collection R S F
    = record {ArrowCollection R S F}

-- ### Identity

identity-collection
  : {X : Object'}
  → (R : Relation (Object'.Object X))
  → {F : Arrow' X X}
  → Identity F
  → Identity
    (arrow-collection R R F)
identity-collection _ i
  = record
  { identity
    = λ xs
    → ArrowCollection.arrow
    $ IdentityList.identity i
      (Collection.elements xs)
  }

-- ### Compose

compose-collection
  : {X Y Z : Object'}
  → (R : Relation (Object'.Object X))
  → (S : Relation (Object'.Object Y))
  → (T : Relation (Object'.Object Z))
  → {F : Arrow' Y Z}
  → {G : Arrow' X Y}
  → {H : Arrow' X Z}
  → Compose F G H
  → Compose
    (arrow-collection S T F)
    (arrow-collection R S G)
    (arrow-collection R T H)
compose-collection _ _ _ j
  = record
  { compose
    = λ fs gs
    → ArrowCollection.arrow
    $ ComposeList.compose j
      (ArrowCollection.Arrow.elements fs)
      (ArrowCollection.Arrow.elements gs)
  }

-- ## Dependent

-- ### DependentObject

dependent-object-collection
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → DependentRelation X'
  → DependentObject X
dependent-object-collection {n = zero} R
  = object-collection R
dependent-object-collection {n = suc _} R
  = record
  { tail
    = λ x → dependent-object-collection
      (DependentRelation.tail R x)
  }

-- ### DependentArrow

dependent-arrow-collection
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → (R : DependentRelation X')
  → (S : DependentRelation Y')
  → DependentArrow X' Y'
  → DependentArrow
    (dependent-object-collection R)
    (dependent-object-collection S)
dependent-arrow-collection {n = zero} R S F
  = arrow-collection R S F
dependent-arrow-collection {n = suc _} R S F
  = record
  { tail
    = λ x y → dependent-arrow-collection
      (DependentRelation.tail R x)
      (DependentRelation.tail S y)
      (DependentArrow.tail F x y)
  }

-- ### DependentIdentity

dependent-identity-collection
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → (R : DependentRelation X')
  → {F : DependentArrow X' X'}
  → DependentIdentity F
  → DependentIdentity
    (dependent-arrow-collection R R F)
dependent-identity-collection {n = zero} R i
  = identity-collection R i
dependent-identity-collection {n = suc _} R i
  = record
  { tail
    = λ x → dependent-identity-collection
      (DependentRelation.tail R x)
      (DependentIdentity.tail i x)
  }

-- ### DependentCompose

dependent-compose-collection
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {Z' : DependentObject Z}
  → (R : DependentRelation X')
  → (S : DependentRelation Y')
  → (T : DependentRelation Z')
  → {F : DependentArrow Y' Z'}
  → {G : DependentArrow X' Y'}
  → {H : DependentArrow X' Z'}
  → DependentCompose F G H
  → DependentCompose
    (dependent-arrow-collection S T F)
    (dependent-arrow-collection R S G)
    (dependent-arrow-collection R T H)
dependent-compose-collection {n = zero} R S T j
  = compose-collection R S T j
dependent-compose-collection {n = suc _} R S T j
  = record
  { tail
    = λ x y z → dependent-compose-collection
      (DependentRelation.tail R x)
      (DependentRelation.tail S y)
      (DependentRelation.tail T z)
      (DependentCompose.tail j x y z)
  }

