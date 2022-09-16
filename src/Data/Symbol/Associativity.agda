module Data.Symbol.Associativity where

-- ## Definition

data Associativity
  : Set
  where

  left
    : Associativity

  right
    : Associativity

