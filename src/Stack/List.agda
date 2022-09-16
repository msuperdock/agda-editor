module Stack.List where

open import Data.Any
  using (any)
open import Data.Empty
  using (⊥)
open import Data.Fin
  using (Fin; suc; zero)
open import Data.List
  using (List; []; _∷_; _!_)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (suc; zero)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Sum
  using (_⊔_)
open import Data.Unit
  using (⊤; tt)
open import Stack
  using (EventStack; ViewStack; ViewStackMap)

-- ## Stacks

-- ### ViewStack

module ViewStackList
  (V : ViewStack)
  where

  View
    : Set
  View
    = List
      (ViewStack.View V)

  ViewPath
    : View
    → Set
  ViewPath (any {zero} _)
    = ⊤
  ViewPath vs@(any {suc _} _)
    = k ∈ Fin (List.length vs)
    × ViewStack.ViewPath V (vs ! k)
  
  ViewInner
    : (v : View)
    → ViewPath v
    → Set
  ViewInner (any {zero} _) _
    = ⊥
  ViewInner vs@(any {suc _} _) (k , vp)
    = ViewStack.ViewInner V (vs ! k) vp

  ViewInnerPath
    : (v : View)
    → (vp : ViewPath v)
    → ViewInner v vp
    → Set
  ViewInnerPath vs@(any {suc _} _) (k , vp)
    = ViewStack.ViewInnerPath V (vs ! k) vp

view-stack-list
  : ViewStack
  → ViewStack
view-stack-list V
  = record {ViewStackList V}

-- ### EventStack

data ListEvent
  : Set
  where

  insert-before
    : ListEvent

  insert-after
    : ListEvent

  delete
    : ListEvent

  move-previous
    : ListEvent

  move-next
    : ListEvent

data ListEvent₀
  : Set
  where

  insert
    : ListEvent₀

module EventStackList
  (E : EventStack)
  where

  open EventStack E public
    using (ModeInner; EventInner)

  Mode
    : Set
  Mode
    = Maybe (EventStack.Mode E)

  Event
    : Mode
    → Set
  Event nothing
    = ListEvent₀
  Event (just m)
    = EventStack.Event E m ⊔ ListEvent

event-stack-list
  : EventStack
  → EventStack
event-stack-list E
  = record {EventStackList E}

-- ## StackMaps

-- ### ViewStackMap

module _
  {V W : ViewStack}
  where

  module ViewStackMapList
    (F : ViewStackMap V W)
    where

    view
      : ViewStack.View (view-stack-list V)
      → ViewStack.View (view-stack-list W)
    view
      = List.map (ViewStackMap.view F)

    view-with
      : (v : ViewStack.View (view-stack-list V))
      → ViewStack.ViewPath (view-stack-list V) v
      → ViewStack.View (view-stack-list W)
    view-with [] _
      = []
    view-with (v ∷ vs) (zero , vp)
      = ViewStackMap.view-with F v vp ∷ view vs
    view-with (v ∷ vs@(_ ∷ _)) (suc k , vp)
      = ViewStackMap.view F v ∷ view-with vs (k , vp)
    
    view-path
      : (v : ViewStack.View (view-stack-list V))
      → (vp : ViewStack.ViewPath (view-stack-list V) v)
      → ViewStack.ViewPath (view-stack-list W)
        (view-with v vp)
    view-path [] _
      = tt
    view-path (v ∷ _) (zero , vp)
      = (zero , ViewStackMap.view-path F v vp)
    view-path (_ ∷ v ∷ _) (suc zero , vp)
      = (suc zero , ViewStackMap.view-path F v vp)
    view-path (_ ∷ vs@(_ ∷ _ ∷ _)) (suc k@(suc _) , vp)
      with view-path vs (k , vp)
    ... | (k' , vp')
      = (suc k' , vp')

    view-inner-with
      : (v : ViewStack.View (view-stack-list V))
      → (vp : ViewStack.ViewPath (view-stack-list V) v)
      → (v' : ViewStack.ViewInner (view-stack-list V) v vp)
      → ViewStack.ViewInnerPath (view-stack-list V) v vp v'
      → ViewStack.ViewInner (view-stack-list W)
        (view-with v vp)
        (view-path v vp)
    view-inner-with (v ∷ _) (zero , vp)
      = ViewStackMap.view-inner-with F v vp
    view-inner-with (_ ∷ v ∷ _) (suc zero , vp)
      = ViewStackMap.view-inner-with F v vp
    view-inner-with (_ ∷ vs@(_ ∷ _ ∷ _)) (suc k@(suc _) , vp)
      = view-inner-with vs (k , vp)

    view-inner-path
      : (v : ViewStack.View (view-stack-list V))
      → (vp : ViewStack.ViewPath (view-stack-list V) v)
      → (v' : ViewStack.ViewInner (view-stack-list V) v vp)
      → (vp' : ViewStack.ViewInnerPath (view-stack-list V) v vp v')
      → ViewStack.ViewInnerPath (view-stack-list W)
        (view-with v vp)
        (view-path v vp)
        (view-inner-with v vp v' vp')
    view-inner-path (v ∷ _) (zero , vp)
      = ViewStackMap.view-inner-path F v vp
    view-inner-path (_ ∷ v ∷ _) (suc zero , vp)
      = ViewStackMap.view-inner-path F v vp
    view-inner-path (_ ∷ vs@(_ ∷ _ ∷ _)) (suc k@(suc _) , vp)
      = view-inner-path vs (k , vp)

  view-stack-map-list
    : ViewStackMap V W
    → ViewStackMap
      (view-stack-list V)
      (view-stack-list W)
  view-stack-map-list F
    = record {ViewStackMapList F}

