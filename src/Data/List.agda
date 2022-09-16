module Data.List where

open import Data.Any
  using (Any; any)
open import Data.Empty
  using (¬_)
open import Data.Equal
  using (_≡_; _≢_; refl; sub)
open import Data.Fin
  using (Fin; _<_fin; suc)
open import Data.Function
  using (_∘_)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (Maybe; just)
open import Data.Nat
  using (ℕ; suc)
open import Data.Retraction
  using (Retraction)
open import Data.Vec
  using (Vec; cons; nil)

import Agda.Builtin.List
  as Builtin

-- ## Definition

List
  : Set
  → Set
List A
  = Any (Vec A)

-- ## Builtin

List'
  : Set
  → Set
List'
  = Builtin.List

module List' where

  open Builtin.List public
    using () renaming
    ( []
      to nil
    ; _∷_
      to cons
    )

open List' public
  using (cons; nil)

-- ## Module

module List where

  -- ### Interface

  infixr 5 _∷_
  
  pattern []
    = any nil
  pattern _∷_ x xs
    = any (cons x xs)

  length
    : {A : Set}
    → List A
    → ℕ
  length (any xs)
    = Vec.length xs
  
  lookup
    : {A : Set}
    → (xs : List A)
    → Fin (length xs)
    → A
  lookup (any xs) k
    = Vec.lookup xs k
  
  _!_
    = lookup
  
  update
    : {A : Set}
    → (xs : List A)
    → Fin (length xs)
    → A
    → List A
  update (any xs) k x
    = any (Vec.update xs k x)

  insert
    : {A : Set}
    → (xs : List A)
    → Fin (suc (length xs))
    → A
    → List A
  insert (any xs) k x
    = any (Vec.insert xs k x)

  delete
    : {A : Set}
    → (xs : List A)
    → Fin (length xs)
    → List A
  delete (any {suc _} xs) k
    = any (Vec.delete xs k)

  swap
    : {A : Set}
    → A
    → (xs : List A)
    → Fin (length xs)
    → List A
  swap x xs k
    = any (Vec.swap (cons x xs) k)

  map
    : {A B : Set}
    → (A → B)
    → List A
    → List B
  map f (any xs)
    = any (Vec.map f xs)

  map-maybe
    : {A B : Set}
    → (A → Maybe B)
    → List A
    → Maybe (List B)
  map-maybe f (any xs)
    = Maybe.map any (Vec.map-maybe f xs)

  -- ### Conversion

  module _
    {A : Set}
    where

    from-builtin
      : List' A
      → List A
    from-builtin nil
      = []
    from-builtin (cons x xs)
      = x ∷ from-builtin xs

    to-builtin
      : List A
      → List' A
    to-builtin (any xs)
      = Vec.to-builtin xs
  
  -- ### Retractions

  retraction
    : {A B : Set}
    → Retraction A B
    → Retraction (List A) (List B)
  retraction
    = Any.retraction
    ∘ Vec.retraction

  retraction-reverse
    : (A : Set)
    → Retraction (List A) (List A)
  retraction-reverse
    = Any.retraction
    ∘ Vec.retraction-reverse

  -- ### Properties

  lookup-update
    : {A : Set}
    → (xs : List A)
    → (k : Fin (length xs))
    → (y : A)
    → update xs k y ! k ≡ y
  lookup-update (any xs)
    = Vec.lookup-update xs

  lookup-update-other
    : {A : Set}
    → (xs : List A)
    → (k l : Fin (length xs))
    → (y : A)
    → k ≢ l
    → update xs k y ! l ≡ xs ! l
  lookup-update-other (any xs)
    = Vec.lookup-update-other xs

  lookup-insert
    : {A : Set}
    → (xs : List A)
    → (k : Fin (suc (length xs)))
    → (y : A)
    → insert xs k y ! k ≡ y
  lookup-insert (any xs)
    = Vec.lookup-insert xs

  lookup-insert-less
    : {A : Set}
    → (xs : List A)
    → {k : Fin (suc (length xs))}
    → (y : A)
    → (l : Fin (length xs))
    → Fin.lift l < k fin
    → insert xs k y ! Fin.lift l ≡ xs ! l
  lookup-insert-less (any xs)
    = Vec.lookup-insert-less xs

  lookup-insert-¬less
    : {A : Set}
    → (xs : List A)
    → (k : Fin (suc (length xs))) 
    → (y : A)
    → (l : Fin (length xs))
    → ¬ Fin.lift l < k fin
    → insert xs k y ! suc l ≡ xs ! l
  lookup-insert-¬less (any xs)
    = Vec.lookup-insert-¬less xs

  lookup-delete-less
    : {A : Set}
    → (x : A)
    → (xs : List A)
    → {k l : Fin (length (x ∷ xs))}
    → {l' : Fin (length (delete (x ∷ xs) k))}
    → Fin.drop l ≡ just l'
    → l < k fin
    → delete (x ∷ xs) k ! l' ≡ (x ∷ xs) ! l
  lookup-delete-less x xs
    = Vec.lookup-delete-less (cons x xs)

  lookup-delete-¬less
    : {A : Set}
    → (x : A)
    → (xs : List A)
    → (k : Fin (length (x ∷ xs)))
    → (l : Fin (length (delete (x ∷ xs) k)))
    → ¬ suc l < k fin
    → suc l ≢ k
    → delete (x ∷ xs) k ! l ≡ (x ∷ xs) ! suc l
  lookup-delete-¬less x xs
    = Vec.lookup-delete-¬less (cons x xs)

  lookup-swap₁
    : {A : Set}
    → (x : A)
    → (xs : List A)
    → (k : Fin (length xs))
    → swap x xs k ! Fin.lift k ≡ (x ∷ xs) ! suc k
  lookup-swap₁ x xs
    = Vec.lookup-swap₁ (cons x xs)

  lookup-swap₂
    : {A : Set}
    → (x : A)
    → (xs : List A)
    → (k : Fin (length xs))
    → swap x xs k ! suc k ≡ (x ∷ xs) ! Fin.lift k
  lookup-swap₂ x xs
    = Vec.lookup-swap₂ (cons x xs)

  lookup-swap₂'
    : {A : Set}
    → (x : A)
    → (xs : List A)
    → {k : Fin (length xs)}
    → (k' : Fin (length (x ∷ xs)))
    → Fin.drop k' ≡ just k
    → swap x xs k ! suc k ≡ (x ∷ xs) ! k'
  lookup-swap₂' x xs
    = Vec.lookup-swap₂' (cons x xs)

  lookup-swap-less
    : {A : Set}
    → (x : A)
    → (xs : List A)
    → (k : Fin (length xs)) 
    → {l : Fin (length (x ∷ xs))}
    → l < Fin.lift k fin
    → swap x xs k ! l ≡ (x ∷ xs) ! l
  lookup-swap-less x xs k
    = Vec.lookup-swap-less (cons x xs) k

  lookup-swap-greater
    : {A : Set}
    → (x : A)
    → (xs : List A)
    → {k : Fin (length xs)}
    → {l : Fin (length (x ∷ xs))}
    → suc k < l fin
    → swap x xs k ! l ≡ (x ∷ xs) ! l
  lookup-swap-greater x xs
    = Vec.lookup-swap-greater (cons x xs)

  lookup-map
    : {A B : Set}
    → (f : A → B)
    → (xs : List A)
    → (k : Fin (length xs))
    → map f xs ! k ≡ f (xs ! k)
  lookup-map f (any xs)
    = Vec.lookup-map f xs

  lookup-map-just
    : {n : ℕ}
    → {A B : Set}
    → (f : A → Maybe B)
    → (xs : Vec A n)
    → {ys : Vec B n}
    → map-maybe f (any xs) ≡ just (any ys)
    → (k : Fin n)
    → f (any xs ! k) ≡ just (any ys ! k)
  lookup-map-just f xs _
    with Vec.map-maybe f xs
    | inspect (Vec.map-maybe f) xs
  lookup-map-just f xs refl | just _ | [ p ]
    = Vec.lookup-map-just f xs p

  map-maybe-length
    : {A B : Set}
    → (f : A → Maybe B)
    → (xs : List A)
    → {ys : List B}
    → map-maybe f xs ≡ just ys
    → length xs ≡ length ys
  map-maybe-length f (any xs) _
    with Vec.map-maybe f xs
  map-maybe-length _ _ refl | just _
    = refl

  map-maybe-equal
    : {A B : Set}
    → (f₁ f₂ : A → Maybe B)
    → ((x : A)
      → f₁ x ≡ f₂ x)
    → ((xs : List A)
      → map-maybe f₁ xs ≡ map-maybe f₂ xs)
  map-maybe-equal f₁ f₂ p (any xs)
    = sub (Maybe.map any) (Vec.map-maybe-equal f₁ f₂ p xs)

  map-maybe-identity
    : {A : Set}
    → (f : A → Maybe A)
    → ((x : A)
      → f x ≡ just x)
    → ((xs : List A)
      → map-maybe f xs ≡ just xs)
  map-maybe-identity f p (any xs)
    with Vec.map-maybe f xs
    | Vec.map-maybe-identity f p xs
  ... | _ | refl
    = refl

  map-maybe-compose
    : {A B C : Set}
    → (f : B → Maybe C)
    → (g : A → Maybe B)
    → (h : A → Maybe C)
    → ((x : A)
      → {y : B}
      → g x ≡ just y
      → h x ≡ f y)
    → ((xs : List A)
      → {ys : List B}
      → map-maybe g xs ≡ just ys
      → map-maybe h xs ≡ map-maybe f ys)
  map-maybe-compose _ g _ _ (any xs) _
    with Vec.map-maybe g xs
    | inspect (Vec.map-maybe g) xs
  map-maybe-compose f g h p (any xs) refl | just _ | [ q ]
    = sub (Maybe.map any) (Vec.map-maybe-compose f g h p xs q)

-- ## Exports

open List public
  using ([]; _∷_; _!_)

