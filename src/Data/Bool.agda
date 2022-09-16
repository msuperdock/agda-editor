module Data.Bool where

open import Data.Empty
  using (⊥)
open import Data.Equal
  using (_≡_; _≢_)

import Agda.Builtin.Bool
  as Builtin

-- ## Definition

Bool
  : Set
Bool
  = Builtin.Bool

open Builtin.Bool public

-- ## Module

module Bool where

  -- ### Interface
  
  not
    : Bool
    → Bool
  not true
    = false
  not false
    = true
  
  infixr 5 _∨_
  infixr 6 _∧_
  
  _∨_
    : Bool
    → Bool
    → Bool
  false ∨ b
    = b
  true ∨ _
    = true

  _∧_
    : Bool
    → Bool
    → Bool
  false ∧ _
    = false
  true ∧ b
    = b
  
  -- ### Conversion

  F
    : Bool
    → Set
  F b
    = b ≡ false

  T
    : Bool
    → Set
  T b
    = b ≡ true

  -- ### Properties
  
  false≢true
    : false ≢ true
  false≢true ()

  ¬both
    : {x : Bool}
    → F x
    → T x
    → ⊥
  ¬both {x = false} _ ()

-- ## Exports

open Bool public
  using (F; T; _∨_; _∧_; not)

