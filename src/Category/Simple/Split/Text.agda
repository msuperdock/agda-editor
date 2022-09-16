module Category.Simple.Split.Text where

open import Category.Simple.Split
  using (SimpleSplitFunctor; simple-split-functor-from-retraction)
open import Data.Bool
  using (true)
open import Data.Function
  using (const)
open import Data.Text
  using (Text)
open import Data.TextWith
  using (TextWith)

-- ## Nondependent

simple-split-functor-text
  : SimpleSplitFunctor (TextWith (const true)) Text
simple-split-functor-text
  = simple-split-functor-from-retraction TextWith.retraction

