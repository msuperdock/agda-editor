module Data.Text where

open import Data.Char
  using (Char)
open import Data.List
  using (List)

-- ## Definition

Text
  : Set
Text
  = List Char

-- ## Module

module Text
  = List
  using (length)

