module Data.Vec where

open import Data.Any
  using (Any; any)
open import Data.Bool
  using (F)
open import Data.Empty
  using (¬_; ⊥-elim)
open import Data.Equal
  using (_≡_; _≢_; refl; sub; trans)
open import Data.Fin
  using (Fin; _<_fin; s<s; z<s; zero; suc)
open import Data.Function
  using (_$_; _∘_)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; zero; suc)
open import Data.Retraction
  using (Retraction)

open import Agda.Builtin.List
  using () renaming
  ( List
    to List'
  ; []
    to nil'
  ; _∷_
    to cons'
  )

-- ## Definition

data Vec'
  (A : Set)
  : ℕ
  → Set
  where

  nil
    : Vec' A zero

  cons
    : A
    → (xs : Any (Vec' A))
    → Vec' A (suc (Any.index xs))

Vec
  = Vec'

-- ## Module

module Vec where

  open Vec' public

  -- ### Interface

  infixr 5 _∷_

  pattern []
    = nil
  pattern _∷_ x xs
    = cons x (any xs)

  snoc
    : {A : Set}
    → {n : ℕ}
    → Vec A n
    → A
    → Vec A (suc n)
  snoc [] y
    = y ∷ []
  snoc (x ∷ xs) y
    = x ∷ snoc xs y

  length
    : {A : Set}
    → {n : ℕ}
    → Vec A n
    → ℕ
  length {n = n} _
    = n

  lookup
    : {A : Set}
    → {n : ℕ}
    → Vec A n
    → Fin n
    → A
  lookup (x ∷ _) zero
    = x
  lookup (_ ∷ xs) (suc k)
    = lookup xs k

  _!_
    = lookup

  update
    : {A : Set}
    → {n : ℕ}
    → Vec A n
    → Fin n
    → A
    → Vec A n
  update (_ ∷ xs) zero y
    = y ∷ xs
  update (x ∷ xs) (suc k) y
    = x ∷ update xs k y

  insert
    : {A : Set}
    → {n : ℕ}
    → Vec A n
    → Fin (suc n)
    → A
    → Vec A (suc n)
  insert xs zero y
    = y ∷ xs
  insert (x ∷ xs) (suc k) y
    = x ∷ insert xs k y

  delete
    : {A : Set}
    → {n : ℕ}
    → Vec A (suc n)
    → Fin (suc n)
    → Vec A n
  delete (_ ∷ xs) zero
    = xs
  delete (x ∷ xs@(_ ∷ _)) (suc k)
    = x ∷ delete xs k

  swap
    : {A : Set}
    → {n : ℕ}
    → Vec A (suc n)
    → Fin n
    → Vec A (suc n)
  swap (x ∷ y ∷ xs) zero
    = y ∷ x ∷ xs
  swap (x ∷ xs) (suc k)
    = x ∷ swap xs k

  map
    : {A B : Set}
    → {n : ℕ}
    → (A → B)
    → Vec A n
    → Vec B n
  map _ []
    = []
  map f (x ∷ xs)
    = f x ∷ map f xs

  map-maybe
    : {A B : Set}
    → {n : ℕ}
    → (A → Maybe B)
    → Vec A n
    → Maybe (Vec B n)
  map-maybe _ []
    = just []
  map-maybe f (x ∷ xs)
    with f x
    | map-maybe f xs
  ... | nothing | _
    = nothing
  ... | _ | nothing
    = nothing
  ... | just y | just ys
    = just (y ∷ ys)

  reverse
    : {A : Set}
    → {n : ℕ}
    → Vec A n
    → Vec A n
  reverse []
    = []
  reverse (x ∷ xs)
    = snoc (reverse xs) x

  -- ### Equality

  cons-equal
    : {A : Set}
    → {n : ℕ}
    → {x₁ x₂ : A}
    → {xs₁ xs₂ : Vec A n}
    → x₁ ≡ x₂
    → xs₁ ≡ xs₂
    → x₁ ∷ xs₁ ≡ x₂ ∷ xs₂
  cons-equal refl refl
    = refl

  -- ### Conversion

  to-builtin
    : {A : Set}
    → {n : ℕ}
    → Vec A n
    → List' A
  to-builtin []
    = nil'
  to-builtin (x ∷ xs)
    = cons' x (to-builtin xs)

  -- ### Properties

  lookup-update
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → (k : Fin n)
    → (y : A)
    → update xs k y ! k ≡ y
  lookup-update (_ ∷ _) zero _
    = refl
  lookup-update (_ ∷ xs) (suc k) y
    = lookup-update xs k y

  lookup-update-other
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → (k l : Fin n)
    → (y : A)
    → k ≢ l
    → update xs k y ! l ≡ xs ! l
  lookup-update-other (_ ∷ _) zero zero _ ¬p
    = ⊥-elim (¬p refl)
  lookup-update-other (_ ∷ _) zero (suc _) _ _
    = refl
  lookup-update-other (_ ∷ _) (suc _) zero _ _
    = refl
  lookup-update-other (_ ∷ xs) (suc k) (suc l) y ¬p
    = lookup-update-other xs k l y (¬p ∘ sub suc)

  lookup-insert
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → (k : Fin (suc n))
    → (y : A)
    → insert xs k y ! k ≡ y
  lookup-insert _ zero _
    = refl
  lookup-insert (_ ∷ xs) (suc k) y
    = lookup-insert xs k y

  lookup-insert-less
    : {A : Set}
    → {n : ℕ}
    → {k : Fin (suc n)}
    → (xs : Vec A n)
    → (y : A)
    → (l : Fin n)
    → Fin.lift l < k fin
    → insert xs k y ! Fin.lift l ≡ xs ! l
  lookup-insert-less (_ ∷ _) _ zero z<s
    = refl
  lookup-insert-less (_ ∷ xs) y (suc l) (s<s p)
    = lookup-insert-less xs y l p

  lookup-insert-¬less
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → (k : Fin (suc n)) 
    → (y : A)
    → (l : Fin n)
    → ¬ Fin.lift l < k fin
    → insert xs k y ! suc l ≡ xs ! l
  lookup-insert-¬less _ zero _ _ _
    = refl
  lookup-insert-¬less _ (suc _) _ zero ¬p
    = ⊥-elim (¬p z<s)
  lookup-insert-¬less (_ ∷ xs) (suc k) y (suc l) ¬p
    = lookup-insert-¬less xs k y l (¬p ∘ s<s)

  lookup-delete-less
    : {A : Set}
    → {n : ℕ}
    → {k l : Fin (suc n)}
    → {l' : Fin n}
    → (xs : Vec A (suc n))
    → Fin.drop l ≡ just l'
    → l < k fin
    → delete xs k ! l' ≡ xs ! l
  lookup-delete-less (_ ∷ _ ∷ _) refl z<s
    = refl
  lookup-delete-less {l = suc l} (_ ∷ _ ∷ _) _ _
    with Fin.drop l
    | inspect Fin.drop l
  lookup-delete-less (_ ∷ xs@(_ ∷ _)) refl (s<s p) | just _ | [ q ]
    = lookup-delete-less xs q p

  lookup-delete-¬less
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A (suc n))
    → (k : Fin (suc n))
    → (l : Fin n)
    → ¬ suc l < k fin
    → suc l ≢ k
    → delete xs k ! l ≡ xs ! suc l
  lookup-delete-¬less (_ ∷ _) zero _ _ _
    = refl
  lookup-delete-¬less _ (suc zero) zero _ ¬q
    = ⊥-elim (¬q refl)
  lookup-delete-¬less _ (suc (suc _)) zero ¬p _
    = ⊥-elim (¬p (s<s z<s))
  lookup-delete-¬less (_ ∷ xs@(_ ∷ _)) (suc k) (suc l) ¬p ¬q
    = lookup-delete-¬less xs k l (¬p ∘ s<s) (¬q ∘ sub suc)

  lookup-swap₁
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A (suc n))
    → (k : Fin n)
    → swap xs k ! Fin.lift k ≡ xs ! suc k
  lookup-swap₁ (_ ∷ _ ∷ _) zero
    = refl
  lookup-swap₁ (_ ∷ xs@(_ ∷ _)) (suc k)
    = lookup-swap₁ xs k

  lookup-swap₂
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A (suc n))
    → (k : Fin n)
    → swap xs k ! suc k ≡ xs ! Fin.lift k
  lookup-swap₂ (_ ∷ _ ∷ _) zero
    = refl
  lookup-swap₂ (_ ∷ xs@(_ ∷ _)) (suc k)
    = lookup-swap₂ xs k

  lookup-swap₂'
    : {A : Set}
    → {n : ℕ}
    → {k : Fin n}
    → (xs : Vec A (suc n))
    → (k' : Fin (suc n))
    → Fin.drop k' ≡ just k
    → swap xs k ! suc k ≡ xs ! k'
  lookup-swap₂' {k = k} xs k' p
    with Fin.drop-just k' p
  ... | refl
    = lookup-swap₂ xs k

  lookup-swap-less
    : {A : Set}
    → {n : ℕ}
    → {l : Fin (suc n)}
    → (xs : Vec A (suc n))
    → (k : Fin n)
    → l < Fin.lift k fin
    → swap xs k ! l ≡ xs ! l
  lookup-swap-less (_ ∷ _ ∷ _) (suc _) z<s
    = refl
  lookup-swap-less (_ ∷ xs@(_ ∷ _)) (suc k) (s<s p)
    = lookup-swap-less xs k p

  lookup-swap-greater
    : {A : Set}
    → {n : ℕ}
    → {k : Fin n}
    → {l : Fin (suc n)}
    → (xs : Vec A (suc n))
    → suc k < l fin
    → swap xs k ! l ≡ xs ! l
  lookup-swap-greater (_ ∷ _ ∷ _) (s<s z<s)
    = refl
  lookup-swap-greater (_ ∷ xs@(_ ∷ _)) (s<s p@(s<s _))
    = lookup-swap-greater xs p

  lookup-map
    : {A B : Set}
    → {n : ℕ}
    → (f : A → B)
    → (xs : Vec A n)
    → (k : Fin n)
    → map f xs ! k ≡ f (xs ! k)
  lookup-map _ (_ ∷ _) zero
    = refl
  lookup-map f (_ ∷ xs) (suc k)
    = lookup-map f xs k

  lookup-map-just
    : {A B : Set}
    → {n : ℕ}
    → {ys : Vec B n}
    → (f : A → Maybe B)
    → (xs : Vec A n)
    → map-maybe f xs ≡ just ys
    → (k : Fin n)
    → f (xs ! k) ≡ just (ys ! k)
  lookup-map-just f (x ∷ xs) _ zero
    with f x
    | map-maybe f xs
  lookup-map-just _ _ refl _ | just _ | just _
    = refl
  lookup-map-just f (x ∷ xs) _ (suc _)
    with f x
    | map-maybe f xs
    | inspect (map-maybe f) xs
  lookup-map-just f (_ ∷ xs) refl (suc k) | just _ | just _ | [ p ]
    = lookup-map-just f xs p k

  map-equal
    : {A B : Set}
    → {n : ℕ}
    → (f₁ f₂ : A → B)
    → ((x : A)
      → f₁ x ≡ f₂ x)
    → ((xs : Vec A n)
      → map f₁ xs ≡ map f₂ xs)
  map-equal _ _ _ []
    = refl
  map-equal f₁ f₂ p (x ∷ xs)
    = cons-equal (p x) (map-equal f₁ f₂ p xs)

  map-identity
    : {A : Set}
    → {n : ℕ}
    → (f : A → A)
    → ((x : A)
      → f x ≡ x)
    → ((xs : Vec A n)
      → map f xs ≡ xs)
  map-identity _ _ []
    = refl
  map-identity f p (x ∷ xs)
    = cons-equal (p x) (map-identity f p xs)

  map-maybe-equal
    : {A B : Set}
    → {n : ℕ}
    → (f₁ f₂ : A → Maybe B)
    → ((x : A)
      → f₁ x ≡ f₂ x)
    → ((xs : Vec A n)
      → map-maybe f₁ xs ≡ map-maybe f₂ xs)
  map-maybe-equal _ _ _ []
    = refl
  map-maybe-equal f₁ f₂ p (x ∷ xs)
    with f₁ x
    | f₂ x
    | p x
    | map-maybe f₁ xs
    | map-maybe f₂ xs
    | map-maybe-equal f₁ f₂ p xs
  ... | nothing | _ | refl | _ | _ | _
    = refl
  ... | just _ | _ | refl | nothing | _ | refl
    = refl
  ... | just _ | _ | refl | just _ | _ | refl
    = refl

  map-maybe-identity
    : {A : Set}
    → {n : ℕ}
    → (f : A → Maybe A)
    → ((x : A)
      → f x ≡ just x)
    → ((xs : Vec A n)
      → map-maybe f xs ≡ just xs)
  map-maybe-identity _ _ []
    = refl
  map-maybe-identity f p (x ∷ xs)
    with f x
    | p x
    | map-maybe f xs
    | map-maybe-identity f p xs
  ... | _ | refl | _ | refl
    = refl

  map-maybe-compose
    : {A B C : Set}
    → {n : ℕ}
    → (f : B → Maybe C)
    → (g : A → Maybe B)
    → (h : A → Maybe C)
    → ((x : A)
      → {y : B}
      → g x ≡ just y
      → h x ≡ f y)
    → ((xs : Vec A n)
      → {ys : Vec B n}
      → map-maybe g xs ≡ just ys
      → map-maybe h xs ≡ map-maybe f ys)
  map-maybe-compose _ _ _ _ [] {ys = []} _
    = refl
  map-maybe-compose _ g _ _ (x ∷ xs) _
    with g x
    | inspect g x
    | map-maybe g xs
    | inspect (map-maybe g) xs
  map-maybe-compose f g h p (x ∷ xs) refl
    | just y | [ q ] | just ys | [ r ]
    with h x
    | f y
    | p x q
    | map-maybe h xs
    | map-maybe f ys
    | map-maybe-compose f g h p xs r
  ... | nothing | _ | refl | _ | _ | _
    = refl
  ... | just _ | _ | refl | nothing | _ | refl
    = refl
  ... | just _ | _ | refl | just _ | _ | refl
    = refl

  reverse-snoc
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → (x : A)
    → reverse (snoc xs x) ≡ x ∷ reverse xs
  reverse-snoc [] _
    = refl
  reverse-snoc (_ ∷ xs) x
    with reverse (snoc xs x)
    | reverse-snoc xs x
  ... | _ | refl
    = refl

  reverse-involution
    : {A : Set}
    → {n : ℕ}
    → (xs : Vec A n)
    → reverse (reverse xs) ≡ xs
  reverse-involution []
    = refl
  reverse-involution (x ∷ xs)
    = trans (reverse-snoc (reverse xs) x)
    $ cons-equal refl (reverse-involution xs)

  -- ### Retractions

  module VecRetraction
    {A B : Set}
    (F : Retraction A B)
    where

    to
      : {n : ℕ}
      → Vec A n
      → Vec B n
    to
      = map (Retraction.to F)

    from
      : {n : ℕ}
      → Vec B n
      → Vec A n
    from
      = map (Retraction.from F)
  
    to-from
      : {n : ℕ}
      → (ys : Vec B n)
      → to (from ys) ≡ ys
    to-from []
      = refl
    to-from (y ∷ ys)
      = cons-equal (Retraction.to-from F y) (to-from ys)

  retraction
    : {A B : Set}
    → Retraction A B
    → (n : ℕ)
    → Retraction (Vec A n) (Vec B n)
  retraction F _
    = record {VecRetraction F}

  retraction-reverse
    : (A : Set)
    → (n : ℕ)
    → Retraction (Vec A n) (Vec A n)
  retraction-reverse _ _
    = record
    { to
      = reverse
    ; from
      = reverse
    ; to-from
      = reverse-involution
    }

