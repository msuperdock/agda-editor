module Data.Symbol where

open import Data.Bool
  using (Bool; T; _∨_; _∧_; false; true)
open import Data.If
  using (If; just)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (module Nat; ℕ; suc)
open import Data.Relation
  using (τ₁; τ₂)
open import Data.Sigma
  using (_×_; _,_)
open import Data.Symbol.Associativity
  using (Associativity)
open import Data.Symbol.Token
  using (Token)
open import Data.Vec
  using (Vec)

-- ## Definition

record Symbol'
  (S : Set)
  : Set₁
  where

  field

    {Symbol}
      : Set

    has-left
      : Symbol
      → Bool

    has-right
      : Symbol
      → Bool

    center-arity
      : Symbol
      → ℕ

    tokens
      : (s : Symbol)
      → Vec Token (center-arity s)

    precedence
      : (s : Symbol)
      → If ℕ (has-left s ∨ has-right s)

    associativity
      : (s : Symbol)
      → If (Maybe Associativity) (has-left s ∧ has-right s)

    style
      : Symbol
      → S

  arity
    : Symbol
    → ℕ
  arity s
    with has-left s
    | has-right s
  ... | false | false
    = center-arity s
  ... | false | true
    = suc (center-arity s)
  ... | true | false
    = suc (center-arity s)
  ... | true | true
    = suc (suc (center-arity s))

  data SymbolWith
    : Bool
    → Bool
    → ℕ
    → Set
    where

    symbol-with
      : (s : Symbol)
      → SymbolWith
        (has-left s)
        (has-right s)
        (center-arity s)

  data SymbolWith'
    : ℕ
    → Set
    where

    symbol-with'
      : (s : Symbol)
      → SymbolWith'
        (arity s)

  to-pair
    : Symbol
    → Maybe (ℕ × Maybe Associativity)
  to-pair s
    with has-left s
    | has-right s
    | precedence s
    | associativity s
  ... | false | false | _ | _
    = nothing
  ... | false | true | just n | _
    = just (n , just Associativity.right)
  ... | true | false | just n | _
    = just (n , just Associativity.left)
  ... | true | true | just n | just a
    = just (n , a)

  child-valid
    : {l r : Bool}
    → {n : ℕ}
    → Associativity
    → SymbolWith l r n
    → Maybe Symbol
    → Bool
  child-valid _ _ nothing
    = true
  child-valid _ (symbol-with s) (just s')
    with to-pair s
    | to-pair s'
  ... | nothing | _
    = false
  ... | _ | nothing
    = true
  ... | just (p , _) | just (p' , _)
    with Nat.compare p p'
  ... | τ₁ _ _ _
    = true
  child-valid Associativity.left _ _
    | just (_ , just Associativity.left)
    | just (_ , just Associativity.left)
    | τ₂ _ _ _
    = true
  child-valid Associativity.right _ _
    | just (_ , just Associativity.right)
    | just (_ , just Associativity.right)
    | τ₂ _ _ _
    = true
  ... | _
    = false

  LeftValid
    : {l r : Bool}
    → {n : ℕ}
    → SymbolWith l r n
    → Maybe Symbol
    → Set
  LeftValid s s'
    = T (child-valid Associativity.left s s')

  RightValid
    : {l r : Bool}
    → {n : ℕ}
    → SymbolWith l r n
    → Maybe Symbol
    → Set
  RightValid s s'
    = T (child-valid Associativity.right s s')

