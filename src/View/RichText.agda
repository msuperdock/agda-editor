module View.RichText where

open import Data.Fin
  using (Fin)
open import Data.List
  using (List; _!_)
open import Data.Text
  using (Text)

-- ## Definitions

data RichText
  (S : Set)
  : Set
  where
  
  plain
    : Text
    → RichText S

  style
    : S
    → RichText S
    → RichText S

  texts
    : List (RichText S)
    → RichText S
  
data RichTextPath
  {S : Set}
  : RichText S
  → Set
  where

  plain
    : {t : Text}
    → Fin (Text.length t)
    → RichTextPath (plain t)
    
  style
    : {s : S}
    → {t : RichText S}
    → RichTextPath t
    → RichTextPath (style s t)

  text
    : {ts : List (RichText S)}
    → (k : Fin (List.length ts))
    → RichTextPath (ts ! k)
    → RichTextPath (texts ts)

