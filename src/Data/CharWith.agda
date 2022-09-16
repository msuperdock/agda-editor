module Data.CharWith where

open import Data.Bool
  using (Bool; T; true)
open import Data.Char
  using (Char)
open import Data.Digit
  using (Digit; 0d; 1d; 2d; 3d; 4d; 5d; 6d; 7d; 8d; 9d)
open import Data.Empty
  using (⊥-elim)
open import Data.Equal
  using (_≡_; refl)
open import Data.Function
  using (const)
open import Data.Maybe
  using (just; nothing)
open import Data.Retraction
  using (Retraction)

-- ## Definition

record CharWith'
  (p : Char → Bool)
  : Set
  where

  constructor
  
    char-with

  field
  
    char
      : Char

    valid
      : T (p char)

CharWith
  = CharWith'

-- ## Module

module CharWith where

  -- ### Characters

  open CharWith' public

  retraction
    : Retraction (CharWith (const true)) Char
  retraction
    = record
    { to
      = char
    ; from
      = λ c → char-with c refl
    ; to-from
      = λ _ → refl
    }

  -- ### Digits

  module CharWithRetractionDigit where

    to
      : CharWith Char.is-digit
      → Digit
    to (char-with c p)
      with Char.to-digit c
    ... | nothing
      = ⊥-elim (Bool.false≢true p)
    ... | just n
      = n

    from
      : Digit
      → CharWith Char.is-digit
    from d
      = char-with (Char.from-digit d) (Char.is-digit-from-digit d)

    to-from
      : (d : Digit)
      → to (from d) ≡ d
    to-from 0d
      = refl
    to-from 1d
      = refl
    to-from 2d
      = refl
    to-from 3d
      = refl
    to-from 4d
      = refl
    to-from 5d
      = refl
    to-from 6d
      = refl
    to-from 7d
      = refl
    to-from 8d
      = refl
    to-from 9d
      = refl

  retraction-digit
    : Retraction (CharWith Char.is-digit) Digit
  retraction-digit
    = record {CharWithRetractionDigit}

