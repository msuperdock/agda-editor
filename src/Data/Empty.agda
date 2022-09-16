module Data.Empty where

-- ## Definition

data ⊥
  : Set
  where

-- ## Module

module Empty where

  ⊥-elim
    : {A : Set}
    → .⊥
    → A
  ⊥-elim ()

  infix 3 ¬_

  ¬_
    : Set
    → Set
  ¬ P
    = P → ⊥

-- ## Exports

open Empty public
  using (¬_; ⊥-elim)

