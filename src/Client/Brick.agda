module Client.Brick where

open import Data.Char
  using (Char)
open import Data.Fin
  using (Fin)
open import Data.Function
  using (_∘_)
open import Data.IO
  using (IO)
open import Data.List
  using (List; List')
open import Data.Maybe
  using (Maybe)
open import Data.Nat
  using (ℕ; zero)
open import Data.Pair
  using (Pair)
open import Data.Sigma
  using (module Sigma; _×_)
open import Data.String
  using (String)
open import Data.Text
  using (Text)

-- ## Types

data ViewportType
  : Set
  where

  horizontal
    : ViewportType

  vertical
    : ViewportType
  
  both
    : ViewportType

data InputEvent
  : Set
  where

  escape
    : InputEvent

  return
    : InputEvent

  backspace
    : InputEvent

  delete
    : InputEvent

  up
    : InputEvent

  down
    : InputEvent

  left
    : InputEvent

  right
    : InputEvent

  char
    : Char
    → InputEvent

-- ## Postulates

postulate
  
  -- ### Types

  App
    : Set
    → Set

  Attribute
    : Set

  AttributeMap
    : Set

  AttributeName
    : Set

  BrickEvent
    : Set

  Color
    : Set

  CursorLocation
    : Set

  EventM
    : Set
    → Set

  Location
    : Set

  Next
    : Set
    → Set

  Padding
    : Set

  Widget
    : Set

  -- ### Functions

  app
    : {S : Set}
    → (S → List' Widget)
    → (S → List' CursorLocation → Maybe CursorLocation)
    → (S → BrickEvent → EventM (Next S))
    → (S → EventM S)
    → (S → AttributeMap)
    → App S

  attribute-map'
    : Attribute
    → List' (Pair AttributeName Attribute)
    → AttributeMap

  attribute-name
    : String
    → AttributeName

  continue
    : {S : Set}
    → S
    → EventM (Next S)

  default-attribute
    : Attribute

  default-main
    : {S : Set}
    → App S
    → S
    → IO S

  event-bind
    : {A B : Set}
    → EventM A
    → (A → EventM B)
    → EventM B

  event-pure
    : {S : Set}
    → S
    → EventM S

  from-brick-event
    : BrickEvent
    → Maybe InputEvent

  halt
    : {S : Set}
    → S
    → EventM (Next S)

  horizontal-box'
    : List' Widget
    → Widget

  liftIO
    : {A : Set}
    → IO A
    → EventM A

  location
    : ℕ
    → ℕ
    → Location

  pad-bottom-with
    : Padding
    → Widget
    → Widget

  pad-left-with
    : Padding
    → Widget
    → Widget

  pad-right-with
    : Padding
    → Widget
    → Widget

  pad-top-with
    : Padding
    → Widget
    → Widget

  padding-max
    : Padding

  show-cursor
    : Location
    → Widget
    → Widget

  string 
    : String
    → Widget

  vertical-box'
    : List' Widget
    → Widget

  viewport
    : ViewportType
    → Widget
    → Widget

  with-attribute
    : AttributeName
    → Widget
    → Widget

  with-background
    : Attribute
    → Color
    → Attribute

  with-foreground
    : Attribute
    → Color
    → Attribute

  -- ### Colors

  black
    : Color

  red
    : Color

  green
    : Color

  yellow
    : Color

  blue
    : Color

  magenta
    : Color

  cyan
    : Color

  white
    : Color

  bright-black
    : Color

  bright-red
    : Color

  bright-green
    : Color

  bright-yellow
    : Color

  bright-blue
    : Color

  bright-magenta
    : Color

  bright-cyan
    : Color

  bright-white
    : Color

-- ## Foreign

-- ### Imports

{-# FOREIGN GHC
  import Brick.AttrMap
    (AttrMap, AttrName, attrMap)
  import Brick.Main
    (App(..), continue, defaultMain, halt)
  import Brick.Types
    (BrickEvent(..), CursorLocation, EventM, Location(..), Next, Padding(..),
      ViewportType(..), Widget)
  import Brick.Widgets.Core
    (hBox, padBottom, padLeft, padRight, padTop, showCursor, txt, vBox,
      viewport, withDefAttr)
  import Control.Monad.IO.Class
    (liftIO)
  import Data.String
    (fromString)
  import Data.Text
    (unpack)
  import Graphics.Vty.Attributes
    (Attr, defAttr, withBackColor, withForeColor)
  import Graphics.Vty.Attributes.Color
    (Color, black, blue, brightBlack, brightBlue, brightCyan, brightGreen,
      brightMagenta, brightRed, brightWhite, brightYellow, cyan, green, magenta,
      red, white, yellow)
  import Graphics.Vty.Input.Events
    (Event(..), Key(..))
  import Prelude
    hiding (Left, Right)
#-}

-- ### Definitions

{-# FOREIGN GHC
  type SimpleApp s
    = App s () ()

  data InputEvent
    = Escape
    | Return
    | Backspace
    | Delete
    | Up
    | Down
    | Left
    | Right
    | Char Char

  fromBrickEvent
    :: BrickEvent () ()
    -> Maybe InputEvent
  fromBrickEvent (VtyEvent (EvKey KEsc _))
    = Just Escape
  fromBrickEvent (VtyEvent (EvKey KEnter _))
    = Just Return
  fromBrickEvent (VtyEvent (EvKey KBS _))
    = Just Backspace
  fromBrickEvent (VtyEvent (EvKey KDel _))
    = Just Delete
  fromBrickEvent (VtyEvent (EvKey KUp _))
    = Just Up
  fromBrickEvent (VtyEvent (EvKey KDown _))
    = Just Down
  fromBrickEvent (VtyEvent (EvKey KLeft _))
    = Just Left
  fromBrickEvent (VtyEvent (EvKey KRight _))
    = Just Right
  fromBrickEvent (VtyEvent (EvKey (KChar c) _))
    = Just (Char c)
  fromBrickEvent _
    = Nothing

  location
    :: Integer
    -> Integer
    -> Location
  location c r
    = Location (fromIntegral c, fromIntegral r)
#-}

-- ### Data

{-# COMPILE GHC InputEvent
  = data InputEvent
    ( Escape
    | Return
    | Backspace
    | Delete
    | Up
    | Down
    | Left
    | Right
    | Char
    )
#-}

{-# COMPILE GHC ViewportType
  = data ViewportType
    ( Horizontal
    | Vertical
    | Both
    )
#-}

-- ### Types

{-# COMPILE GHC App
  = type SimpleApp #-}
{-# COMPILE GHC Attribute
  = type Attr #-}
{-# COMPILE GHC AttributeMap
  = type AttrMap #-}
{-# COMPILE GHC AttributeName
  = type AttrName #-}
{-# COMPILE GHC BrickEvent
  = type BrickEvent () () #-}
{-# COMPILE GHC Color
  = type Color #-}
{-# COMPILE GHC CursorLocation
  = type CursorLocation () #-}
{-# COMPILE GHC EventM
  = type EventM () #-}
{-# COMPILE GHC Location
  = type Location #-}
{-# COMPILE GHC Next
  = type Next #-}
{-# COMPILE GHC Padding
  = type Padding #-}
{-# COMPILE GHC Widget
  = type Widget () #-}

-- ### Functions

{-# COMPILE GHC app
  = \ _ -> App #-}
{-# COMPILE GHC attribute-map'
  = attrMap #-}
{-# COMPILE GHC attribute-name
  = fromString . unpack #-}
{-# COMPILE GHC continue
  = \ _ -> continue #-}
{-# COMPILE GHC default-attribute
  = defAttr #-}
{-# COMPILE GHC default-main
  = \ _ -> defaultMain #-}
{-# COMPILE GHC event-bind
  = \ _ _ -> (>>=) #-}
{-# COMPILE GHC event-pure
  = \ _ -> pure #-}
{-# COMPILE GHC from-brick-event
  = fromBrickEvent #-}
{-# COMPILE GHC halt
  = \ _ -> halt #-}
{-# COMPILE GHC horizontal-box'
  = hBox #-}
{-# COMPILE GHC liftIO
  = \ _ -> liftIO #-}
{-# COMPILE GHC location
  = location #-}
{-# COMPILE GHC pad-bottom-with
  = padBottom #-}
{-# COMPILE GHC pad-left-with
  = padLeft #-}
{-# COMPILE GHC pad-right-with
  = padRight #-}
{-# COMPILE GHC pad-top-with
  = padTop #-}
{-# COMPILE GHC padding-max
  = Max #-}
{-# COMPILE GHC show-cursor
  = showCursor () #-}
{-# COMPILE GHC string
  = txt #-}
{-# COMPILE GHC vertical-box'
  = vBox #-}
{-# COMPILE GHC viewport
  = viewport () #-}
{-# COMPILE GHC with-attribute
  = withDefAttr #-}
{-# COMPILE GHC with-background
  = withBackColor #-}
{-# COMPILE GHC with-foreground
  = withForeColor #-}

-- ### Colors

{-# COMPILE GHC black
  = black #-}
{-# COMPILE GHC red
  = red #-}
{-# COMPILE GHC green
  = green #-}
{-# COMPILE GHC yellow
  = yellow #-}
{-# COMPILE GHC blue
  = blue #-}
{-# COMPILE GHC magenta
  = magenta #-}
{-# COMPILE GHC cyan
  = cyan #-}
{-# COMPILE GHC white
  = white #-}

{-# COMPILE GHC bright-black
  = brightBlack #-}
{-# COMPILE GHC bright-red
  = brightRed #-}
{-# COMPILE GHC bright-green
  = brightGreen #-}
{-# COMPILE GHC bright-yellow
  = brightYellow #-}
{-# COMPILE GHC bright-blue
  = brightBlue #-}
{-# COMPILE GHC bright-magenta
  = brightMagenta #-}
{-# COMPILE GHC bright-cyan
  = brightCyan #-}
{-# COMPILE GHC bright-white
  = brightWhite #-}

-- ## Attributes

attribute-background
  : Color
  → Attribute
attribute-background
  = with-background default-attribute

attribute-foreground
  : Color
  → Attribute
attribute-foreground
  = with-foreground default-attribute

attribute-map
  : List (AttributeName × Attribute)
  → AttributeMap
attribute-map
  = attribute-map' default-attribute
  ∘ List.to-builtin
  ∘ List.map Sigma.to-pair

-- ## Widgets

-- ### Empty

empty-line
  : Widget
empty-line
  = string " "

-- ### Padding

pad-bottom
  : Widget
  → Widget
pad-bottom
  = pad-bottom-with padding-max

pad-left
  : Widget
  → Widget
pad-left
  = pad-left-with padding-max

pad-right
  : Widget
  → Widget
pad-right
  = pad-right-with padding-max

pad-top
  : Widget
  → Widget
pad-top
  = pad-top-with padding-max

-- ### Boxes

horizontal-box
  : List Widget
  → Widget
horizontal-box ws
  = horizontal-box' (List.to-builtin ws)

vertical-box
  : List Widget
  → Widget
vertical-box ws
  = vertical-box' (List.to-builtin ws)

-- ### Text

text
  : Text
  → Widget
text t
  = string (String.from-list t)

text-with
  : (t : Text)
  → Fin (Text.length t)
  → Widget
text-with t k
  = show-cursor (location (Fin.to-nat k) zero) (text t)

