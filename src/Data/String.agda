module Data.String where

open import Data.Char
  using (Char)
open import Data.Function
  using (_∘_)
open import Data.List
  using (List)

import Agda.Builtin.String
  as Builtin

open Builtin
  using () renaming
  ( primStringFromList
    to from-list'
  )

-- ## Definition

open Builtin public
  using (String)

-- ## Module

module String where

  from-list
    : List Char
    → String
  from-list
    = from-list'
    ∘ List.to-builtin

