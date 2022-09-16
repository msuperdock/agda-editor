module Event.Text where

open import Data.Char
  using (Char)

-- ## Definition

data TextEvent
  : Set
  where

  delete-previous
    : TextEvent

  delete-next
    : TextEvent

  insert
    : Char
    → TextEvent

