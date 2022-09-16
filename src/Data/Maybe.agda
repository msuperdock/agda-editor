module Data.Maybe where

open import Data.Bool
  using (Bool; false; true)
open import Data.Equal
  using (_≡_; _≢_; refl)

-- ## Definition

data Maybe'
  (A : Set)
  : Set
  where

  nothing
    : Maybe' A

  just
    : A
    → Maybe' A

{-# COMPILE GHC Maybe' = data Maybe
  ( Nothing
  | Just
  )
#-}

Maybe
  = Maybe'

-- ## Module

module Maybe where

  open Maybe' public

  -- ### Interface

  is-just
    : {A : Set}
    → Maybe A
    → Bool
  is-just nothing
    = false
  is-just (just _)
    = true

  maybe
    : {A B : Set}
    → Maybe A
    → B
    → (A → B)
    → B
  maybe nothing n _
    = n
  maybe (just x) _ j
    = j x
  
  map
    : {A B : Set}
    → (A → B)
    → Maybe A
    → Maybe B
  map _ nothing
    = nothing
  map f (just x)
    = just (f x)

  -- ### Properties

  just≢nothing
    : {A : Set}
    → {x : A}
    → just x ≢ nothing
  just≢nothing ()

  just-injective
    : {A : Set}
    → {x₁ x₂ : A}
    → just x₁ ≡ just x₂
    → x₁ ≡ x₂
  just-injective refl
    = refl

  map-nothing
    : {A B : Set}
    → (f : A → B)
    → (x : Maybe A)
    → map f x ≡ nothing
    → x ≡ nothing
  map-nothing _ nothing _
    = refl

-- ## Exports

open Maybe public
  using (maybe)

