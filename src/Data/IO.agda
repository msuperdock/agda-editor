module Data.IO where

open import Agda.Builtin.IO public
  using (IO)

module IO where

  infixl 1 _>>=_

  postulate

    return
      : {A : Set}
      → A
      → IO A

    _>>=_ 
      : {A B : Set}
      → IO A
      → (A → IO B)
      → IO B

  {-# COMPILE GHC return
    = \_ -> return #-}
  {-# COMPILE GHC _>>=_
    = \_ _ -> (>>=) #-}

open IO public
  using (_>>=_)

