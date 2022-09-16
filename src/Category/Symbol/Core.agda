module Category.Symbol.Core where

open import Category.Core
  using (ChainObject)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Symbol
  using (Symbol')

-- ## Dependent

-- ### Types

DependentSymbol
  : Set
  → {n : ℕ}
  → ChainObject n
  → Set₁

record DependentSymbol'
  (S : Set)
  {n : ℕ}
  (X : ChainObject (suc n))
  : Set₁

-- ### Definitions

DependentSymbol S {n = zero} _
  = Symbol' S
DependentSymbol S {n = suc _} X
  = DependentSymbol' S X

record DependentSymbol' S X where

  inductive
  no-eta-equality

  field

    tail
      : (x : ChainObject.Object X)
      → DependentSymbol S
        (ChainObject.tail X x)

module DependentSymbol
  = DependentSymbol'

