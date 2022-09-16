module Stack.Base.RichText where

open import Stack.Base
  using (BaseViewStack)
open import View.RichText
  using (RichText; RichTextPath)

-- ## Stacks

-- ### BaseViewStack

base-view-stack-rich-text
  : Set
  → BaseViewStack
base-view-stack-rich-text S
  = record
  { View
    = RichText S
  ; ViewPath
    = RichTextPath
  }

