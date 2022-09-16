module Encoding where

open import Category
  using (Category; ChainCategory; DependentCategory)
open import Category.Core
  using (Object'; object')
open import Category.Split.Core
  using (SplitBase)
open import Data.Equal
  using (_≡_)
open import Data.Maybe
  using (Maybe; just)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### Definition

record Encoding
  (A B : Set)
  : Set
  where

  field

    encode
      : A
      → B
    
    decode
      : B
      → Maybe A

    decode-encode
      : (x : A)
      → decode (encode x) ≡ just x

  split-base
    : SplitBase
      (object' B)
      (object' A)
  split-base
    = record
    { base
      = decode
    ; unbase
      = encode
    ; base-unbase
      = decode-encode
    }

-- ### Conversion

split-base-encoding
  : {X X' : Object'}
  → SplitBase X X'
  → Encoding
    (Object'.Object X')
    (Object'.Object X)
split-base-encoding a
  = record
  { encode
    = SplitBase.unbase a
  ; decode
    = SplitBase.base a
  ; decode-encode
    = SplitBase.base-unbase a
  }

-- ## Dependent

-- ### Types

DependentEncoding
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → Set
  → Set

record DependentEncoding'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentCategory C)
  (A : Set)
  : Set

-- ### Definitions

DependentEncoding {n = zero} C'
  = Encoding (Category.Object C')
DependentEncoding {n = suc _} C'
  = DependentEncoding' C'

record DependentEncoding' {_ C} C' A where

  inductive

  field

    tail
      : (x : ChainCategory.Object C)
      → DependentEncoding
        (DependentCategory.tail C' x) A

module DependentEncoding
  = DependentEncoding'

