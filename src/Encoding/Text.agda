module Encoding.Text where

open import Data.Bool
  using (Bool)
open import Data.Char
  using (Char)
open import Data.Text
  using (Text)
open import Data.TextWith
  using (TextWith)
open import Encoding
  using (Encoding)
open import Encoding.Char
  using (encoding-char)
open import Encoding.List
  using (encoding-list)

-- ## Base

encoding-text
  : (p : Char → Bool)
  → Encoding (TextWith p) Text
encoding-text p
  = encoding-list
    (encoding-char p)

