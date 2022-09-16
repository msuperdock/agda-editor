module Category.Core.Collection.Unit where

open import Category.Core
  using (Arrow'; ChainObject; Compose; DependentArrow; DependentCompose;
    DependentIdentity; DependentObject; Identity; Object')
open import Category.Core.Collection
  using (dependent-object-collection; object-collection)
open import Category.Core.Relation
  using (DependentRelation)
open import Category.Core.List.Unit
  using (module ArrowListUnit; module ComposeListUnit; module IdentityListUnit)
open import Data.Collection
  using (Collection)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Relation
  using (Relation)

-- ## Base

-- ### Arrow'

module _
  {X Y : Object'}
  where

  module ArrowCollectionUnit
    (R : Relation (Object'.Object X))
    (S : Relation (Object'.Object Y))
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
          : ArrowListUnit.Arrow X Y
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
          : ArrowListUnit.ArrowEqual X Y
            (Arrow.elements fs₁)
            (Arrow.elements fs₂)

    arrow-refl
      : {xs : Object'.Object (object-collection R)}
      → {ys : Object'.Object (object-collection S)}
      → {fs : Arrow xs ys}
      → ArrowEqual fs fs
    arrow-refl
      = arrow-equal (ArrowListUnit.arrow-refl X Y)

    arrow-sym
      : {xs : Object'.Object (object-collection R)}
      → {ys : Object'.Object (object-collection S)}
      → {fs₁ fs₂ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual fs₂ fs₁
    arrow-sym (arrow-equal ps)
      = arrow-equal (ArrowListUnit.arrow-sym X Y ps)

    arrow-trans
      : {xs : Object'.Object (object-collection R)}
      → {ys : Object'.Object (object-collection S)}
      → {fs₁ fs₂ fs₃ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual fs₂ fs₃
      → ArrowEqual fs₁ fs₃
    arrow-trans (arrow-equal ps₁) (arrow-equal ps₂)
      = arrow-equal (ArrowListUnit.arrow-trans X Y ps₁ ps₂)
    
  arrow-collection-unit
    : (R : Relation (Object'.Object X))
    → (S : Relation (Object'.Object Y))
    → Arrow'
      (object-collection R)
      (object-collection S)
  arrow-collection-unit R S
    = record {ArrowCollectionUnit R S}

-- ### Identity

identity-collection-unit
  : {X : Object'}
  → (R : Relation (Object'.Object X))
  → Identity
    (arrow-collection-unit R R)
identity-collection-unit {X = X} _
  = record
  { identity
    = λ xs
    → ArrowCollectionUnit.arrow
    $ IdentityListUnit.identity X
      (Collection.elements xs)
  }

-- ### Compose

compose-collection-unit
  : {X Y Z : Object'}
  → (R : Relation (Object'.Object X))
  → (S : Relation (Object'.Object Y))
  → (T : Relation (Object'.Object Z))
  → Compose
    (arrow-collection-unit S T)
    (arrow-collection-unit R S)
    (arrow-collection-unit R T)
compose-collection-unit {X = X} {Y = Y} {Z = Z} _ _ _
  = record
  { compose
    = λ fs gs
    → ArrowCollectionUnit.arrow
    $ ComposeListUnit.compose X Y Z
      (ArrowCollectionUnit.Arrow.elements fs)
      (ArrowCollectionUnit.Arrow.elements gs)
  }

-- ## Dependent

-- ### DependentArrow

dependent-arrow-collection-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → (R : DependentRelation X')
  → (S : DependentRelation Y')
  → DependentArrow
    (dependent-object-collection R)
    (dependent-object-collection S)
dependent-arrow-collection-unit {n = zero} R S
  = arrow-collection-unit R S
dependent-arrow-collection-unit {n = suc _} R S
  = record
  { tail
    = λ x y → dependent-arrow-collection-unit
      (DependentRelation.tail R x)
      (DependentRelation.tail S y)
  }

-- ### DependentIdentity

dependent-identity-collection-unit
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → (R : DependentRelation X')
  → DependentIdentity
    (dependent-arrow-collection-unit R R)
dependent-identity-collection-unit {n = zero} R
  = identity-collection-unit R
dependent-identity-collection-unit {n = suc _} R
  = record
  { tail
    = λ x → dependent-identity-collection-unit
      (DependentRelation.tail R x)
  }

-- ### DependentCompose

dependent-compose-collection-unit
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {Z' : DependentObject Z}
  → (R : DependentRelation X')
  → (S : DependentRelation Y')
  → (T : DependentRelation Z')
  → DependentCompose
    (dependent-arrow-collection-unit S T)
    (dependent-arrow-collection-unit R S)
    (dependent-arrow-collection-unit R T)
dependent-compose-collection-unit {n = zero} R S T
  = compose-collection-unit R S T
dependent-compose-collection-unit {n = suc _} R S T
  = record
  { tail
    = λ x y z → dependent-compose-collection-unit
      (DependentRelation.tail R x)
      (DependentRelation.tail S y)
      (DependentRelation.tail T z)
  }

