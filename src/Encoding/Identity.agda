module Encoding.Identity where

open import Category.Core
  using (object')
open import Category.Split.Core.Identity
  using (split-base-identity)
open import Data.Function
  using (_$_)
open import Encoding
  using (Encoding; split-base-encoding)

-- ## Base

encoding-identity
  : (A : Set)
  → Encoding A A
encoding-identity A
  = split-base-encoding
  $ split-base-identity
    (object' A)

