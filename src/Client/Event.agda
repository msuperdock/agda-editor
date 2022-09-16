module Client.Event where

open import Data.Direction
  using (Direction)

data SpecialEvent
  : Set
  where

  quit
    : SpecialEvent

  write
    : SpecialEvent

  escape
    : SpecialEvent

  return
    : SpecialEvent

  direction
    : Direction
    → SpecialEvent

