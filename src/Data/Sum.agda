module Data.Sum where

-- ## Definition

infixr 1 _⊔_

data _⊔_
  (A₁ : Set)
  (A₂ : Set)
  : Set
  where

  ι₁
    : A₁
    → A₁ ⊔ A₂

  ι₂
    : A₂
    → A₁ ⊔ A₂

