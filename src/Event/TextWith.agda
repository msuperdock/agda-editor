module Event.TextWith where

open import Data.Bool
  using (Bool)
open import Data.Char
  using (Char)
open import Data.CharWith
  using (CharWith)

-- ## Definition

data TextWithEvent
  (p : Char → Bool)
  : Set
  where

  delete-previous
    : TextWithEvent p

  delete-next
    : TextWithEvent p

  insert
    : CharWith p
    → TextWithEvent p

