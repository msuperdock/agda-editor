module Data.Pair where

data Pair
  (A₁ A₂ : Set)
  : Set
  where

  pair
    : A₁
    → A₂
    → Pair A₁ A₂

{-# COMPILE GHC Pair
  = data (,) ((,)) #-}

