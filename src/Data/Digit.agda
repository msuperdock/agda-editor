module Data.Digit where

open import Data.Equal
  using (_≡_; refl; sub; trans)
open import Data.Fin
  using (Fin; suc; zero)
open import Data.Function
  using (_$_)
open import Data.Inspect
  using ([_]; inspect)
open import Data.List
  using (List; []; _∷_)
open import Data.Maybe
  using (just; nothing)
open import Data.Nat
  using (ℕ; _+_; _*_; suc; zero)
open import Data.Retraction
  using (Retraction; retraction-compose)

-- ## Internal

module Internal where

  -- ### Definitions

  Digit
    : Set
  Digit
    = Fin 10

  pattern 0d
    = zero
  pattern 1d
    = suc zero
  pattern 2d
    = suc (suc zero)
  pattern 3d
    = suc (suc (suc zero))
  pattern 4d
    = suc (suc (suc (suc zero)))
  pattern 5d
    = suc (suc (suc (suc (suc zero))))
  pattern 6d
    = suc (suc (suc (suc (suc (suc zero)))))
  pattern 7d
    = suc (suc (suc (suc (suc (suc (suc zero))))))
  pattern 8d
    = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
  pattern 9d
    = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

  Digits
    : Set
  Digits
    = List Digit

  -- ### Interface

  digits-increment
    : Digits
    → Digits
  digits-increment []
    = 1d ∷ []
  digits-increment (d ∷ ds)
    with Fin.increment d
  ... | nothing
    = 0d ∷ digits-increment ds
  ... | just d'
    = d' ∷ ds

  -- ### Conversion

  digits-to-nat
    : Digits
    → ℕ
  digits-to-nat []
    = zero
  digits-to-nat (d ∷ ds)
    = Fin.to-nat d + digits-to-nat ds * 10

  digits-to-nat-increment
    : (ds : Digits)
    → digits-to-nat (digits-increment ds) ≡ suc (digits-to-nat ds)
  digits-to-nat-increment []
    = refl
  digits-to-nat-increment (d ∷ _)
    with Fin.increment d
    | inspect Fin.increment d
  digits-to-nat-increment (d ∷ ds) | nothing | [ p ]
    with Fin.increment-nothing d p
    | digits-to-nat (digits-increment ds)
    | digits-to-nat-increment ds
  ... | refl | _ | refl
    = refl
  digits-to-nat-increment (d ∷ _) | just d' | [ p ]
    with Fin.to-nat d'
    | Fin.increment-just d p
  ... | _ | refl
    = refl

  digits-from-nat
    : ℕ
    → Digits
  digits-from-nat zero
    = []
  digits-from-nat (suc n)
    = digits-increment (digits-from-nat n)

  digits-to-from-nat
    : (n : ℕ)
    → digits-to-nat (digits-from-nat n) ≡ n
  digits-to-from-nat zero
    = refl
  digits-to-from-nat (suc n)
    = trans (digits-to-nat-increment (digits-from-nat n))
    $ sub suc (digits-to-from-nat n)

  -- ### Retractions

  digits-retraction'
    : Retraction Digits ℕ
  digits-retraction'
    = record
    { to
      = digits-to-nat
    ; from
      = digits-from-nat
    ; to-from
      = digits-to-from-nat
    }

  digits-retraction
    : Retraction Digits ℕ
  digits-retraction
    = retraction-compose digits-retraction'
    $ List.retraction-reverse Digit

-- ## Modules

-- ### Digit

Digit
  = Internal.Digit

open Internal public
  using (0d; 1d; 2d; 3d; 4d; 5d; 6d; 7d; 8d; 9d)

-- ### Digits

module Digits where

  open Internal public
    using () renaming
    ( digits-retraction
      to retraction
    )

