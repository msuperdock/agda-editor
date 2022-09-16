module Data.Retraction where

open import Data.Equal
  using (_≡_; sub; trans)
open import Data.Function
  using (_$_; _∘_)

-- ## Definition

record Retraction
  (A B : Set)
  : Set
  where

  field

    to
      : A
      → B

    from
      : B
      → A

    to-from
      : (x : B)
      → to (from x) ≡ x

-- ## Compose

retraction-compose
  : {A B C : Set}
  → Retraction B C
  → Retraction A B
  → Retraction A C
retraction-compose F G
  = record
  { to
    = Retraction.to F
    ∘ Retraction.to G
  ; from
    = Retraction.from G
    ∘ Retraction.from F
  ; to-from
    = λ x
    → trans (sub (Retraction.to F) (Retraction.to-from G (Retraction.from F x)))
    $ Retraction.to-from F x
  }

