module Data.Formula where

open import Data.Symbol
  using (Symbol')
open import Data.Nat
  using (ℕ)
open import Data.Vec
  using (Vec)

-- ## Definition

record Formula
  {S : Set}
  (S' : Symbol' S)
  : Set
  where

  inductive

  field

    {arity}
      : ℕ

    root
      : Symbol'.SymbolWith' S' arity

    subformulas
      : Vec (Formula S') arity

