module Encoding.Char where

open import Data.Bool
  using (Bool; false; true)
open import Data.Char
  using (Char)
open import Data.CharWith
  using (CharWith; char-with)
open import Data.Empty
  using (⊥-elim)
open import Data.Equal
  using (Equal; _≡_; sub)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Encoding
  using (Encoding)

-- ## Base

module EncodingChar
  (p : Char → Bool)
  where

  encode
    : CharWith p
    → Char
  encode
    = CharWith.char
  
  decode
    : Char
    → Maybe (CharWith p)
  decode c
    with p c
    | inspect p c
  ... | false | _
    = nothing
  ... | true | [ p' ]
    = just (char-with c p')

  decode-encode
    : (c : CharWith p)
    → decode (encode c) ≡ just c
  decode-encode c
    with p (CharWith.char c)
    | inspect p (CharWith.char c)
  decode-encode (char-with _ p') | false | [ ¬p' ]
    = ⊥-elim (Bool.¬both ¬p' p')
  decode-encode (char-with c' p') | true | [ p'' ]
    = sub just (sub (char-with c') (Equal.irrelevant p'' p'))

encoding-char
  : (p : Char → Bool)
  → Encoding (CharWith p) Char
encoding-char p
  = record {EncodingChar p}

