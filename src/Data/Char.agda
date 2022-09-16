module Data.Char where
  
open import Data.Bool
  using (Bool; T)
open import Data.Digit
  using (Digit; 0d; 1d; 2d; 3d; 4d; 5d; 6d; 7d; 8d; 9d)
open import Data.Equal
  using (refl)
open import Data.Maybe
  using (Maybe; just; nothing)

import Agda.Builtin.Char
  as Builtin

-- ## Definition

open Builtin public
  using (Char)

-- ## Module

module Char where

  -- ### Interface

  postulate

    is-space
      : Char
      → Bool

  {-# FOREIGN GHC
    import Data.Char
      (isSpace)
  #-}

  {-# COMPILE GHC is-space
    = isSpace #-}

  -- ### Conversion

  from-digit
    : Digit
    → Char
  from-digit 0d
    = '0'
  from-digit 1d
    = '1'
  from-digit 2d
    = '2'
  from-digit 3d
    = '3'
  from-digit 4d
    = '4'
  from-digit 5d
    = '5'
  from-digit 6d
    = '6'
  from-digit 7d
    = '7'
  from-digit 8d
    = '8'
  from-digit 9d
    = '9'

  to-digit
    : Char
    → Maybe Digit
  to-digit '0'
    = just 0d
  to-digit '1'
    = just 1d
  to-digit '2'
    = just 2d
  to-digit '3'
    = just 3d
  to-digit '4'
    = just 4d
  to-digit '5'
    = just 5d
  to-digit '6'
    = just 6d
  to-digit '7'
    = just 7d
  to-digit '8'
    = just 8d
  to-digit '9'
    = just 9d
  to-digit _
    = nothing
  
  is-digit
    : Char
    → Bool
  is-digit c
    = Maybe.is-just (to-digit c)

  IsDigit
    : Char
    → Set
  IsDigit c
    = T (is-digit c)

  is-digit-from-digit
    : (d : Digit)
    → IsDigit (from-digit d)
  is-digit-from-digit 0d
    = refl
  is-digit-from-digit 1d
    = refl
  is-digit-from-digit 2d
    = refl
  is-digit-from-digit 3d
    = refl
  is-digit-from-digit 4d
    = refl
  is-digit-from-digit 5d
    = refl
  is-digit-from-digit 6d
    = refl
  is-digit-from-digit 7d
    = refl
  is-digit-from-digit 8d
    = refl
  is-digit-from-digit 9d
    = refl

