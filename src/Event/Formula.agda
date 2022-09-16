module Event.Formula where

open import Data.Symbol
  using (Symbol')

-- ## Definition

data FormulaEvent
  {S : Set}
  (S' : Symbol' S)
  : Set
  where

  insert
    : Symbol'.Symbol S'
    → FormulaEvent S'

