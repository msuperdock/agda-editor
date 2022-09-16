module Data.Inspect where

open import Data.Equal
  using (_≡_; refl)

module _
  {A : Set}
  {B : A → Set}
  where

  record Inspect
    (f : (x : A) → B x)
    (x : A)
    (y : B x)
    : Set
    where
  
    constructor

      [_]

    field

      equal
        : f x ≡ y
  
  inspect
    : (f : (x : A) → B x)
    → (x : A)
    → Inspect f x (f x)
  inspect _ _
    = [ refl ]

