module Category.Core.Symbol where

open import Category.Core
  using (Arrow'; ChainObject; Compose; DependentArrow; DependentCompose;
    DependentIdentity; DependentObject; Identity; Object')
open import Category.Symbol.Core
  using (DependentSymbol)
open import Data.Equal
  using (_≡_; refl; sym; trans)
open import Data.Fin
  using (Fin)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Symbol
  using (Symbol')

-- ## Base

-- ### Object'

object-symbol
  : {S : Set}
  → Symbol' S
  → Object'
object-symbol S'
  = record
  { Object
    = Symbol'.Symbol S'
  }

-- ### Arrow'

module _
  {S : Set}
  where

  module ArrowSymbol
    (S' T' : Symbol' S)
    where

    record Arrow
      (s : Object'.Object (object-symbol S'))
      (t : Object'.Object (object-symbol T'))
      : Set
      where

      field

        lookup
          : Fin (Symbol'.arity S' s)
          → Maybe (Fin (Symbol'.arity T' t))

        injective
          : (k₁ k₂ : Fin (Symbol'.arity S' s))
          → {l : Fin (Symbol'.arity T' t)}
          → lookup k₁ ≡ just l
          → lookup k₂ ≡ just l
          → k₁ ≡ k₂

    record ArrowEqual
      {s : Object'.Object (object-symbol S')}
      {t : Object'.Object (object-symbol T')}
      (f₁ f₂ : Arrow s t)
      : Set
      where

      field

        lookup
          : (k : Fin (Symbol'.arity S' s))
          → Arrow.lookup f₁ k ≡ Arrow.lookup f₂ k

    arrow-refl
      : {s : Object'.Object (object-symbol S')}
      → {t : Object'.Object (object-symbol T')}
      → {f : Arrow s t}
      → ArrowEqual f f
    arrow-refl
      = record
      { lookup
        = λ _ → refl
      }

    arrow-sym
      : {s : Object'.Object (object-symbol S')}
      → {t : Object'.Object (object-symbol T')}
      → {f₁ f₂ : Arrow s t}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₁
    arrow-sym p
      = record
      { lookup
        = λ k → sym
          (ArrowEqual.lookup p k)
      }

    arrow-trans
      : {s : Object'.Object (object-symbol S')}
      → {t : Object'.Object (object-symbol T')}
      → {f₁ f₂ f₃ : Arrow s t}
      → ArrowEqual f₁ f₂
      → ArrowEqual f₂ f₃
      → ArrowEqual f₁ f₃
    arrow-trans p₁ p₂
      = record
      { lookup
        = λ k → trans
          (ArrowEqual.lookup p₁ k)
          (ArrowEqual.lookup p₂ k)
      }
    
  arrow-symbol
    : (S' T' : Symbol' S)
    → Arrow'
      (object-symbol S')
      (object-symbol T')
  arrow-symbol S' T'
    = record {ArrowSymbol S' T'}

-- ### Identity

module _
  {S : Set}
  where

  module IdentitySymbol
    (S' : Symbol' S)
    where

    identity
      : (s : Object'.Object (object-symbol S'))
      → Arrow'.Arrow (arrow-symbol S' S') s s
    identity _
      = record
      { lookup
        = just
      ; injective
        = λ {_ _ refl refl → refl}
      }

  identity-symbol
    : (S' : Symbol' S)
    → Identity
      (arrow-symbol S' S')
  identity-symbol S'
    = record {IdentitySymbol S'}

-- ### Compose

module _
  {S : Set}
  where

  module ComposeSymbol
    (S' T' U' : Symbol' S)
    where

    compose-lookup
      : {s : Object'.Object (object-symbol S')}
      → {t : Object'.Object (object-symbol T')}
      → {u : Object'.Object (object-symbol U')}
      → Arrow'.Arrow (arrow-symbol T' U') t u
      → Arrow'.Arrow (arrow-symbol S' T') s t
      → Fin (Symbol'.arity S' s)
      → Maybe (Fin (Symbol'.arity U' u))
    compose-lookup f g k
      with ArrowSymbol.Arrow.lookup g k
    ... | nothing
      = nothing
    ... | just l
      = ArrowSymbol.Arrow.lookup f l

    compose-injective
      : {s : Object'.Object (object-symbol S')}
      → {t : Object'.Object (object-symbol T')}
      → {u : Object'.Object (object-symbol U')}
      → (f : Arrow'.Arrow (arrow-symbol T' U') t u)
      → (g : Arrow'.Arrow (arrow-symbol S' T') s t)
      → (k₁ k₂ : Fin (Symbol'.arity S' s))
      → {l : Fin (Symbol'.arity U' u)}
      → compose-lookup f g k₁ ≡ just l
      → compose-lookup f g k₂ ≡ just l
      → k₁ ≡ k₂
    compose-injective f g k₁ k₂ q₁ q₂
      with ArrowSymbol.Arrow.lookup g k₁
      | inspect (ArrowSymbol.Arrow.lookup g) k₁
      | ArrowSymbol.Arrow.lookup g k₂
      | inspect (ArrowSymbol.Arrow.lookup g) k₂
    ... | just l₁ | [ p₁ ] | just l₂ | [ p₂ ]
      with ArrowSymbol.Arrow.injective f l₁ l₂ q₁ q₂
    ... | refl
      = ArrowSymbol.Arrow.injective g k₁ k₂ p₁ p₂

    compose
      : {s : Object'.Object (object-symbol S')}
      → {t : Object'.Object (object-symbol T')}
      → {u : Object'.Object (object-symbol U')}
      → Arrow'.Arrow (arrow-symbol T' U') t u
      → Arrow'.Arrow (arrow-symbol S' T') s t
      → Arrow'.Arrow (arrow-symbol S' U') s u
    compose f g
      = record
      { lookup
        = compose-lookup f g
      ; injective
        = compose-injective f g
      }

  compose-symbol
    : (S' T' U' : Symbol' S)
    → Compose
      (arrow-symbol T' U')
      (arrow-symbol S' T')
      (arrow-symbol S' U')
  compose-symbol S' T' U'
    = record {ComposeSymbol S' T' U'}

-- ## Dependent

-- ### DependentObject

dependent-object-symbol
  : {S : Set}
  → {n : ℕ}
  → {X : ChainObject n}
  → DependentSymbol S X
  → DependentObject X
dependent-object-symbol {n = zero} S'
  = object-symbol S'
dependent-object-symbol {n = suc _} S'
  = record
  { tail
    = λ x → dependent-object-symbol
      (DependentSymbol.tail S' x)
  }

-- ### DependentArrow

dependent-arrow-symbol
  : {S : Set}
  → {n : ℕ}
  → {X Y : ChainObject n}
  → (S' : DependentSymbol S X)
  → (T' : DependentSymbol S Y)
  → DependentArrow
    (dependent-object-symbol S')
    (dependent-object-symbol T')
dependent-arrow-symbol {n = zero} S' T'
  = arrow-symbol S' T'
dependent-arrow-symbol {n = suc _} S' T'
  = record
  { tail
    = λ x y → dependent-arrow-symbol
      (DependentSymbol.tail S' x)
      (DependentSymbol.tail T' y)
  }

-- ### DependentIdentity

dependent-identity-symbol
  : {S : Set}
  → {n : ℕ}
  → {X : ChainObject n}
  → (S' : DependentSymbol S X)
  → DependentIdentity
    (dependent-arrow-symbol S' S')
dependent-identity-symbol {n = zero} S'
  = identity-symbol S'
dependent-identity-symbol {n = suc _} S'
  = record
  { tail
    = λ x → dependent-identity-symbol
      (DependentSymbol.tail S' x)
  }

-- ### DependentCompose

dependent-compose-symbol
  : {S : Set}
  → {n : ℕ}
  → {X Y Z : ChainObject n}
  → (S' : DependentSymbol S X)
  → (T' : DependentSymbol S Y)
  → (U' : DependentSymbol S Z)
  → DependentCompose
    (dependent-arrow-symbol T' U')
    (dependent-arrow-symbol S' T')
    (dependent-arrow-symbol S' U')
dependent-compose-symbol {n = zero} S' T' U'
  = compose-symbol S' T' U'
dependent-compose-symbol {n = suc _} S' T' U'
  = record
  { tail
    = λ x y z → dependent-compose-symbol
      (DependentSymbol.tail S' x)
      (DependentSymbol.tail T' y)
      (DependentSymbol.tail U' z)
  }

