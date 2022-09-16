module Data.Any where

open import Data.Equal
  using (_≡_; sub)
open import Data.Retraction
  using (Retraction)

-- ## Definition

record Any'
  {A : Set}
  (B : A → Set)
  : Set
  where

  constructor

    any

  field

    {index}
      : A

    value
      : B index

Any
  = Any'

-- ## Module

module Any where

  open Any' public

  -- ### Retraction

  module _
    {A : Set}
    {B C : A → Set}
    where

    module AnyRetraction
      (F : (x : A) → Retraction (B x) (C x))
      where
  
      to
        : Any B
        → Any C
      to (any {x} y)
        = any (Retraction.to (F x) y)
  
      from
        : Any C
        → Any B
      from (any {x} z)
        = any (Retraction.from (F x) z)
  
      to-from
        : (z : Any C)
        → to (from z) ≡ z
      to-from (any {x} z)
        = sub any (Retraction.to-from (F x) z)
  
    retraction
      : ((x : A) → Retraction (B x) (C x))
      → Retraction (Any B) (Any C)
    retraction F
      = record {AnyRetraction F}

