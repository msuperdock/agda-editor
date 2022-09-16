module Client.Aeson where

open import Data.Bool
  using (Bool)
open import Data.Char
  using (Char)
open import Data.IO
  using (IO)
open import Data.List
  using (List')
open import Data.Maybe
  using (Maybe)
open import Data.Nat
  using (ℕ)
open import Data.String
  using (String)
open import Data.Unit
  using (⊤)

-- ## Types

data Value
  : Set
  where

  array
    : List' Value
    → Value

  string
    : List' Char
    → Value

  number
    : ℕ
    → Value

  boolean
    : Bool
    → Value

  null
    : Value

-- ## Postulates

postulate

  -- ### Types

  ByteString
    : Set

  -- ### Functions

  decode
    : ByteString
    → Maybe Value

  encode
    : Value
    → ByteString

  is-file
    : String
    → IO Bool

  read-file
    : String
    → IO ByteString

  write-file
    : String
    → ByteString
    → IO ⊤

-- ## Foreign

-- ### Imports

{-# FOREIGN GHC
  import qualified Data.Aeson as Aeson
    (decode, encode, Value(..))
  import Data.ByteString.Lazy
    (ByteString)
  import qualified Data.ByteString.Lazy as ByteString
    (readFile, writeFile)
  import Data.Scientific
    (floatingOrInteger, scientific)
  import Data.Text
    (pack, unpack)
  import Data.Vector
    (fromList, toList)
  import System.Directory
    (doesFileExist)
#-}

-- ### Definitions

{-# FOREIGN GHC
  data Value
    = Array [Value]
    | String [Char]
    | Number Integer
    | Boolean Bool
    | Null

  fromAeson
    :: Aeson.Value
    -> Maybe Value
  fromAeson (Aeson.Object vs)
    = Nothing
  fromAeson (Aeson.Array vs)
    = Array <$> traverse fromAeson (toList vs)
  fromAeson (Aeson.String s)
    = Just (String (unpack s))
  fromAeson (Aeson.Number n)
    = either (const Nothing) (Just . Number) (floatingOrInteger n)
  fromAeson (Aeson.Bool b)
    = Just (Boolean b)
  fromAeson Aeson.Null
    = Just Null

  toAeson
    :: Value
    -> Aeson.Value
  toAeson (Array vs)
    = Aeson.Array (toAeson <$> fromList vs)
  toAeson (String cs)
    = Aeson.String (pack cs)
  toAeson (Number n)
    = Aeson.Number (scientific n 0)
  toAeson (Boolean b)
    = Aeson.Bool b
  toAeson Null
    = Aeson.Null

  decode
    :: ByteString
    -> Maybe Value
  decode s
    = Aeson.decode s
    >>= fromAeson

  encode
    :: Value
    -> ByteString
  encode
    = Aeson.encode
    . toAeson
#-}

-- ### Data

{-# COMPILE GHC Value
  = data Value
    ( Array
    | String
    | Number
    | Boolean
    | Null
    )
#-}

-- ### Types

{-# COMPILE GHC ByteString
  = type ByteString #-}

-- ### Functions

{-# COMPILE GHC decode
  = decode #-}
{-# COMPILE GHC encode
  = encode #-}
{-# COMPILE GHC is-file
  = doesFileExist . unpack #-}
{-# COMPILE GHC read-file
  = ByteString.readFile . unpack #-}
{-# COMPILE GHC write-file
  = ByteString.writeFile . unpack #-}

