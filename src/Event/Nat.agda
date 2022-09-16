module Event.Nat where

open import Data.Char
  using (Char)
open import Event.TextWith
  using (TextWithEvent)

-- ## Definition

NatEvent
  : Set
NatEvent
  = TextWithEvent Char.is-digit

