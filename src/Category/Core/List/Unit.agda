module Category.Core.List.Unit where

open import Category.Core
  using (Arrow'; ChainObject; Compose; DependentArrow; DependentCompose;
    DependentIdentity; DependentObject; Identity; Object')
open import Category.Core.List
  using (dependent-object-list; object-list)
open import Data.Any
  using (any)
open import Data.Equal
  using (_≡_; refl; sym; trans)
open import Data.Fin
  using (Fin)
open import Data.Inspect
  using ([_]; inspect)
open import Data.List
  using (List)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Vec
  using (Vec)

-- ## Base

-- ### Arrow'

module ArrowListUnit
  (X Y : Object')
  where

  record Arrow
    (xs : Object'.Object (object-list X))
    (ys : Object'.Object (object-list Y))
    : Set
    where

    field

      lookup
        : Fin (List.length xs)
        → Maybe (Fin (List.length ys))

      injective
        : (k₁ k₂ : Fin (List.length xs))
        → {l : Fin (List.length ys)}
        → lookup k₁ ≡ just l
        → lookup k₂ ≡ just l
        → k₁ ≡ k₂

  arrow-identity
    : {n : ℕ}
    → (xs : Vec (Object'.Object X) n)
    → (ys : Vec (Object'.Object Y) n)
    → Arrow (any xs) (any ys)
  arrow-identity _ _
    = record
    { lookup
      = just
    ; injective
      = λ {_ _ refl refl → refl}
    }

  record ArrowEqual
    {xs : Object'.Object (object-list X)}
    {ys : Object'.Object (object-list Y)}
    (fs₁ fs₂ : Arrow xs ys)
    : Set
    where

    field
    
      lookup
        : (k : Fin (List.length xs))
        → Arrow.lookup fs₁ k ≡ Arrow.lookup fs₂ k

  arrow-refl
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {fs : Arrow xs ys}
    → ArrowEqual fs fs
  arrow-refl
    = record
    { lookup
      = λ _ → refl
    }

  arrow-sym
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {fs₁ fs₂ : Arrow xs ys}
    → ArrowEqual fs₁ fs₂
    → ArrowEqual fs₂ fs₁
  arrow-sym ps
    = record
    { lookup
      = λ k → sym
        (ArrowEqual.lookup ps k)
    }

  arrow-trans
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {fs₁ fs₂ fs₃ : Arrow xs ys}
    → ArrowEqual fs₁ fs₂
    → ArrowEqual fs₂ fs₃
    → ArrowEqual fs₁ fs₃
  arrow-trans ps₁ ps₂
    = record
    { lookup
      = λ k → trans
        (ArrowEqual.lookup ps₁ k)
        (ArrowEqual.lookup ps₂ k)
    }
  
arrow-list-unit
  : (X Y : Object')
  → Arrow'
    (object-list X)
    (object-list Y)
arrow-list-unit X Y
  = record {ArrowListUnit X Y}

-- ### Identity

module IdentityListUnit
  (X : Object')
  where

  identity
    : (xs : Object'.Object (object-list X))
    → Arrow'.Arrow (arrow-list-unit X X) xs xs
  identity (any xs)
    = ArrowListUnit.arrow-identity X X xs xs

identity-list-unit
  : (X : Object')
  → Identity
    (arrow-list-unit X X)
identity-list-unit X
  = record {IdentityListUnit X}

-- ### Compose

module ComposeListUnit
  (X Y Z : Object')
  where

  compose-lookup
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {zs : Object'.Object (object-list Z)}
    → Arrow'.Arrow (arrow-list-unit Y Z) ys zs
    → Arrow'.Arrow (arrow-list-unit X Y) xs ys
    → Fin (List.length xs)
    → Maybe (Fin (List.length zs))
  compose-lookup fs gs k
    with ArrowListUnit.Arrow.lookup gs k
  ... | nothing
    = nothing
  ... | just l
    = ArrowListUnit.Arrow.lookup fs l

  compose-injective
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {zs : Object'.Object (object-list Z)}
    → (fs : Arrow'.Arrow (arrow-list-unit Y Z) ys zs)
    → (gs : Arrow'.Arrow (arrow-list-unit X Y) xs ys)
    → (k₁ k₂ : Fin (List.length xs))
    → {l : Fin (List.length zs)}
    → compose-lookup fs gs k₁ ≡ just l
    → compose-lookup fs gs k₂ ≡ just l
    → k₁ ≡ k₂
  compose-injective fs gs k₁ k₂ q₁ q₂
    with ArrowListUnit.Arrow.lookup gs k₁
    | inspect (ArrowListUnit.Arrow.lookup gs) k₁
    | ArrowListUnit.Arrow.lookup gs k₂
    | inspect (ArrowListUnit.Arrow.lookup gs) k₂
  ... | just l₁ | [ p₁ ] | just l₂ | [ p₂ ]
    with ArrowListUnit.Arrow.injective fs l₁ l₂ q₁ q₂
  ... | refl
    = ArrowListUnit.Arrow.injective gs k₁ k₂ p₁ p₂

  compose
    : {xs : Object'.Object (object-list X)}
    → {ys : Object'.Object (object-list Y)}
    → {zs : Object'.Object (object-list Z)}
    → Arrow'.Arrow (arrow-list-unit Y Z) ys zs
    → Arrow'.Arrow (arrow-list-unit X Y) xs ys
    → Arrow'.Arrow (arrow-list-unit X Z) xs zs
  compose fs gs
    = record
    { lookup
      = compose-lookup fs gs
    ; injective
      = compose-injective fs gs
    }

compose-list-unit
  : (X Y Z : Object')
  → Compose
    (arrow-list-unit Y Z)
    (arrow-list-unit X Y)
    (arrow-list-unit X Z)
compose-list-unit X Y Z
  = record {ComposeListUnit X Y Z}

-- ## Dependent

-- ### DependentArrow'

dependent-arrow-list-unit
  : {n : ℕ}
  → {X Y : ChainObject n}
  → (X' : DependentObject X)
  → (Y' : DependentObject Y)
  → DependentArrow
    (dependent-object-list X')
    (dependent-object-list Y')
dependent-arrow-list-unit {n = zero} X' Y'
  = arrow-list-unit X' Y'
dependent-arrow-list-unit {n = suc _} X' Y'
  = record
  { tail
    = λ x y → dependent-arrow-list-unit
      (DependentObject.tail X' x)
      (DependentObject.tail Y' y)
  }

-- ### DependentIdentity

dependent-identity-list-unit
  : {n : ℕ}
  → {X : ChainObject n}
  → (X' : DependentObject X)
  → DependentIdentity
    (dependent-arrow-list-unit X' X')
dependent-identity-list-unit {n = zero} X'
  = identity-list-unit X'
dependent-identity-list-unit {n = suc _} X'
  = record
  { tail
    = λ x → dependent-identity-list-unit
      (DependentObject.tail X' x)
  }

-- ### DependentCompose

dependent-compose-list-unit
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → (X' : DependentObject X)
  → (Y' : DependentObject Y)
  → (Z' : DependentObject Z)
  → DependentCompose
    (dependent-arrow-list-unit Y' Z')
    (dependent-arrow-list-unit X' Y')
    (dependent-arrow-list-unit X' Z')
dependent-compose-list-unit {n = zero} X' Y' Z'
  = compose-list-unit X' Y' Z'
dependent-compose-list-unit {n = suc _} X' Y' Z'
  = record
  { tail
    = λ x y z → dependent-compose-list-unit
      (DependentObject.tail X' x)
      (DependentObject.tail Y' y)
      (DependentObject.tail Z' z)
  }

