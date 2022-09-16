module Category.State.List where

open import Category
  using (ChainCategory)
open import Category.Core.List
  using (dependent-associative-list; dependent-compose-equal-list;
    dependent-postcompose-list; dependent-precompose-list;
    dependent-simplify-list)
open import Category.State
  using (DependentStateCategory; StateCategory)
open import Category.State.Lift.List
  using (dependent-state-lift-list)
open import Data.Empty
  using (⊥-elim)
open import Data.Equal
  using (_≡_; refl; sym; trans)
open import Data.Fin
  using (Fin; suc; _≟_fin)
open import Data.Function
  using (_$_)
open import Data.Inspect
  using ([_]; inspect)
open import Data.List
  using (List; _∷_; _!_)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc)
open import Data.Relation
  using (no; yes; τ₁; τ₂; τ₃)
open import Data.Sigma
  using (module Sigma; Σ; _,_)

-- ## Dependent

dependent-state-category-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentStateCategory C
  → DependentStateCategory C
dependent-state-category-list C'
  = record
  { simplify
    = dependent-simplify-list
      (DependentStateCategory.simplify C')
  ; compose-equal
    = dependent-compose-equal-list
      (DependentStateCategory.compose-equal C')
  ; precompose
    = dependent-precompose-list
      (DependentStateCategory.precompose C')
  ; postcompose
    = dependent-postcompose-list
      (DependentStateCategory.postcompose C')
  ; associative
    = dependent-associative-list
      (DependentStateCategory.associative C')
  ; lift
    = dependent-state-lift-list
      (DependentStateCategory.lift C')
  }

-- ## Nondependent

-- ### Function

state-category-list
  : StateCategory
  → StateCategory
state-category-list
  = dependent-state-category-list

-- ### Module

module StateCategoryList
  (C : StateCategory)
  where

  open StateCategory (state-category-list C)

  update-lookup'
    : {y : StateCategory.Object C}
    → (xs : Object)
    → (k : Fin (List.length xs))
    → StateCategory.Arrow C (xs ! k) y
    → (k' : Fin (List.length xs))
    → StateCategory.Arrow C (xs ! k') (List.update xs k y ! k')
  update-lookup' {y = y} xs k f k'
    with k ≟ k' fin
  ... | no ¬p
    = StateCategory.arrow' C refl
      (List.lookup-update-other xs k k' y ¬p)
      (StateCategory.identity' C (xs ! k'))
  ... | yes refl
    = StateCategory.arrow' C refl
      (List.lookup-update xs k y) f

  update-lookup
    : {y : StateCategory.Object C}
    → (xs : Object)
    → (k : Fin (List.length xs))
    → StateCategory.Arrow C (xs ! k) y
    → (k' : Fin (List.length xs))
    → Maybe (l ∈ Fin (List.length (List.update xs k y))
      × StateCategory.Arrow C (xs ! k') (List.update xs k y ! l))
  update-lookup xs k f k'
    = just (k' , update-lookup' xs k f k')

  update-injective
    : {y : StateCategory.Object C}
    → (xs : Object)
    → (k : Fin (List.length xs))
    → (f : StateCategory.Arrow C (xs ! k) y)
    → (k₁' k₂' : Fin (List.length xs))
    → {l : Fin (List.length (List.update xs k y))}
    → {f₁' : StateCategory.Arrow C (xs ! k₁') (List.update xs k y ! l)}
    → {f₂' : StateCategory.Arrow C (xs ! k₂') (List.update xs k y ! l)}
    → update-lookup xs k f k₁' ≡ just (l , f₁')
    → update-lookup xs k f k₂' ≡ just (l , f₂')
    → k₁' ≡ k₂'
  update-injective _ _ _ _ _ refl refl
    = refl

  update
    : {y : StateCategory.Object C}
    → (xs : Object)
    → (k : Fin (List.length xs))
    → StateCategory.Arrow C (xs ! k) y
    → Arrow xs (List.update xs k y)
  update xs k f
    = record
    { lookup
      = update-lookup xs k f
    ; injective
      = update-injective xs k f
    }

  insert-lookup
    : (xs : Object)
    → (k : Fin (suc (List.length xs)))
    → (y : StateCategory.Object C)
    → (k' : Fin (List.length xs))
    → l ∈ Fin (suc (List.length xs))
    × StateCategory.Arrow C (xs ! k') (List.insert xs k y ! l)
  insert-lookup xs k y k'
    with Fin.compare (Fin.lift k') k
  ... | τ₁ p _ _
    = Fin.lift k'
    , StateCategory.arrow' C refl
      (List.lookup-insert-less xs y k' p)
      (StateCategory.identity' C (xs ! k'))
  ... | τ₂ ¬p _ _
    = suc k'
    , StateCategory.arrow' C refl
      (List.lookup-insert-¬less xs k y k' ¬p)
      (StateCategory.identity' C (xs ! k'))
  ... | τ₃ ¬p _ _
    = suc k'
    , StateCategory.arrow' C refl
      (List.lookup-insert-¬less xs k y k' ¬p)
      (StateCategory.identity' C (xs ! k'))

  insert-injective
    : (xs : Object)
    → (k : Fin (suc (List.length xs)))
    → (y : StateCategory.Object C)
    → (k₁' k₂' : Fin (List.length xs))
    → {l : Fin (suc (List.length xs))}
    → {f₁ : StateCategory.Arrow C (xs ! k₁') (List.insert xs k y ! l)}
    → {f₂ : StateCategory.Arrow C (xs ! k₂') (List.insert xs k y ! l)}
    → insert-lookup xs k y k₁' ≡ (l , f₁)
    → insert-lookup xs k y k₂' ≡ (l , f₂)
    → k₁' ≡ k₂'
  insert-injective _ k _ k₁' k₂' p₁ p₂
    with Fin.compare (Fin.lift k₁') k
    | Fin.compare (Fin.lift k₂') k
    | Sigma.comma-injective₁ p₁
    | Sigma.comma-injective₁ p₂

  ... | τ₁ _ _ _ | τ₁ _ _ _ | q₁ | q₂
    = Fin.lift-injective k₁' k₂' (trans q₁ (sym q₂))
  ... | τ₂ _ _ _ | τ₂ _ _ _ | refl | refl
    = refl
  ... | τ₂ _ _ _ | τ₃ _ _ _ | refl | refl
    = refl
  ... | τ₃ _ _ _ | τ₃ _ _ _ | refl | refl
    = refl
  ... | τ₃ _ _ _ | τ₂ _ _ _ | refl | refl
    = refl

  ... | τ₁ r₁ _ _ | τ₂ _ refl _ | refl | q₂
    = ⊥-elim (Fin.<-¬refl' (sym q₂)
      (Fin.<-trans r₁ (Fin.<-suc k₂')))
  ... | τ₁ r₁ _ _ | τ₃ _ _ r₂ | refl | q₂
    = ⊥-elim (Fin.<-¬refl' (sym q₂)
      (Fin.<-trans r₁ (Fin.<-trans r₂ (Fin.<-suc k₂'))))
  ... | τ₂ _ refl _ | τ₁ r₁ _ _ | q₁ | refl
    = ⊥-elim (Fin.<-¬refl' (sym q₁)
      (Fin.<-trans r₁ (Fin.<-suc k₁')))
  ... | τ₃ _ _ r₁ | τ₁ r₂ _ _ | q₁ | refl
    = ⊥-elim (Fin.<-¬refl' (sym q₁)
      (Fin.<-trans r₂ (Fin.<-trans r₁ (Fin.<-suc k₁'))))

  insert
    : (xs : Object)
    → (k : Fin (suc (List.length xs)))
    → (y : StateCategory.Object C)
    → Arrow xs (List.insert xs k y)
  insert xs k y
    = record
    { lookup
      = λ k'
      → just
      $ insert-lookup xs k y k'
    ; injective
      = λ k₁' k₂' p₁ p₂
      → insert-injective xs k y k₁' k₂'
        (Maybe.just-injective p₁)
        (Maybe.just-injective p₂)
    }

  delete-lookup
    : (xs : Object)
    → (k : Fin (List.length xs))
    → (k' : Fin (List.length xs))
    → Maybe (l ∈ Fin (List.length (List.delete xs k))
      × StateCategory.Arrow C (xs ! k') (List.delete xs k ! l))
  delete-lookup (x ∷ xs) k k'
    with Fin.compare k' k
    | Fin.drop k'
    | inspect Fin.drop k'
  ... | τ₁ _ _ _ | nothing | _
    = nothing -- impossible
  ... | τ₁ p _ _ | just k'' | [ q ]
    = just
    $ k''
    , StateCategory.arrow' C refl
      (List.lookup-delete-less x xs q p)
      (StateCategory.identity' C ((x ∷ xs) ! k'))
  ... | τ₂ _ _ _ | _ | _
    = nothing
  delete-lookup (x ∷ xs) k (suc k') | τ₃ p₁ p₂ _ | _ | _
    = just
    $ k'
    , StateCategory.arrow' C refl
      (List.lookup-delete-¬less x xs k k' p₁ p₂)
      (StateCategory.identity' C (xs ! k'))

  delete-injective
    : (xs : Object)
    → (k : Fin (List.length xs))
    → (k₁' k₂' : Fin (List.length xs))
    → {l : Fin (List.length (List.delete xs k))}
    → {f₁ : StateCategory.Arrow C (xs ! k₁') (List.delete xs k ! l)}
    → {f₂ : StateCategory.Arrow C (xs ! k₂') (List.delete xs k ! l)}
    → delete-lookup xs k k₁' ≡ just (l , f₁)
    → delete-lookup xs k k₂' ≡ just (l , f₂)
    → k₁' ≡ k₂'
  delete-injective (_ ∷ _) k k₁' k₂' _ _
    with Fin.compare k₁' k
    | Fin.compare k₂' k
    | Fin.drop k₁'
    | inspect Fin.drop k₁'
    | Fin.drop k₂'
    | inspect Fin.drop k₂'

  delete-injective _ _ k₁' k₂' refl refl
    | τ₁ _ _ _ | τ₁ _ _ _ | just _ | [ q₁ ] | just _ | [ q₂ ]
    = trans (Fin.drop-just k₁' q₁) (sym (Fin.drop-just k₂' q₂))
  delete-injective _ _ (suc _) (suc _) refl refl
    | τ₃ _ _ _ | τ₃ _ _ _ | _ | _ | _ | _
    = refl

  delete-injective _ _ k₁' (suc _) refl refl
    | τ₁ p₁ _ _ | τ₃ _ _ p₂ | just _ | [ q₁ ] | _ | _
    with Fin.drop-just k₁' q₁
  ... | refl
    = ⊥-elim (Fin.<-¬suc p₁ p₂)
  delete-injective _ _ (suc _) k₂' refl refl
    | τ₃ _ _ p₁ | τ₁ p₂ _ _ | _ | _ | just _ | [ q₂ ]
    with Fin.drop-just k₂' q₂
  ... | refl
    = ⊥-elim (Fin.<-¬suc p₂ p₁)

  delete
    : (xs : Object)
    → (k : Fin (List.length xs))
    → Arrow xs (List.delete xs k)
  delete xs k
    = record
    { lookup
      = delete-lookup xs k
    ; injective
      = delete-injective xs k
    }

  swap-lookup
    : (x : StateCategory.Object C)
    → (xs : Object)
    → (k : Fin (List.length xs))
    → (k' : Fin (List.length (x ∷ xs)))
    → l ∈ Fin (List.length (x ∷ xs))
    × StateCategory.Arrow C ((x ∷ xs) ! k') (List.swap x xs k ! l)
  swap-lookup x xs k k'
    with Fin.compare k' (Fin.lift k)
    | Fin.compare k' (suc k)
  ... | τ₁ p _ _ | _
    = k'
    , StateCategory.arrow' C refl
      (List.lookup-swap-less x xs k p)
      (StateCategory.identity' C ((x ∷ xs) ! k'))
  ... | τ₂ _ refl _ | _
    = suc k
    , StateCategory.arrow' C refl
      (List.lookup-swap₂ x xs k)
      (StateCategory.identity' C ((x ∷ xs) ! Fin.lift k))
  ... | _ | τ₂ _ refl _
    = Fin.lift k
    , StateCategory.arrow' C refl
      (List.lookup-swap₁ x xs k)
      (StateCategory.identity' C ((x ∷ xs) ! suc k))
  ... | _ | τ₃ _ _ p
    = k'
    , StateCategory.arrow' C refl
      (List.lookup-swap-greater x xs p)
      (StateCategory.identity' C ((x ∷ xs) ! k'))
  ... | τ₃ _ _ p | τ₁ q _ _
    = ⊥-elim (Fin.<-¬suc p q)

  swap-injective
    : (x : StateCategory.Object C)
    → (xs : Object)
    → (k : Fin (List.length xs))
    → (k₁' k₂' : Fin (List.length (x ∷ xs)))
    → {l : Fin (List.length (x ∷ xs))}
    → {f₁ : StateCategory.Arrow C ((x ∷ xs) ! k₁') (List.swap x xs k ! l)}
    → {f₂ : StateCategory.Arrow C ((x ∷ xs) ! k₂') (List.swap x xs k ! l)}
    → swap-lookup x xs k k₁' ≡ (l , f₁)
    → swap-lookup x xs k k₂' ≡ (l , f₂)
    → k₁' ≡ k₂'
  swap-injective _ _ k k₁' k₂' _ _
    with Fin.compare k₁' (Fin.lift k)
    | Fin.compare k₁' (suc k)
    | Fin.compare k₂' (Fin.lift k)
    | Fin.compare k₂' (suc k)

  swap-injective _ _ _ _ _ refl refl
    | τ₁ _ _ _ | _ | τ₁ _ _ _ | _
    = refl
  swap-injective _ _ k _ _ refl refl
    | τ₁ _ _ ¬p | _ | τ₂ _ refl _ | _
    = ⊥-elim (¬p (Fin.<-suc k))
  swap-injective _ _ _ _ _ refl refl
    | τ₁ _ ¬p _ | _ | τ₃ _ _ _ | τ₂ _ refl _
    = ⊥-elim (¬p refl)
  swap-injective _ _ _ _ _ refl refl
    | τ₁ _ _ _ | _ | τ₃ _ _ _ | τ₃ _ _ _
    = refl
  swap-injective _ _ k _ _ refl refl
    | τ₂ _ refl _ | _ | τ₁ _ _ ¬p | _
    = ⊥-elim (¬p (Fin.<-suc k))
  swap-injective _ _ _ _ _ _ _
    | τ₂ _ refl _ | _ | τ₂ _ refl _ | _
    = refl
  swap-injective _ _ _ _ _ p₁ p₂
    | τ₂ _ refl _ | _ | τ₃ _ _ _ | τ₂ _ refl _
    = trans (Sigma.comma-injective₁ p₂) (Sigma.comma-injective₁ (sym p₁))
  swap-injective _ _ _ _ _ refl refl
    | τ₂ _ refl _ | _ | τ₃ _ _ _ | τ₃ _ ¬p _
    = ⊥-elim (¬p refl)
  swap-injective _ _ _ _ _ refl refl
    | τ₃ _ _ _ | τ₂ _ refl _ | τ₁ _ ¬p _ | _
    = ⊥-elim (¬p refl)
  swap-injective _ _ _ _ _ p₁ p₂
    | τ₃ _ _ _ | τ₂ _ refl _ | τ₂ _ refl _ | _
    = trans (Sigma.comma-injective₁ p₂) (Sigma.comma-injective₁ (sym p₁))
  swap-injective _ _ _ _ _ _ _
    | τ₃ _ _ _ | τ₂ _ refl _ | τ₃ _ _ _ | τ₂ _ refl _
    = refl
  swap-injective _ _ _ _ _ refl refl
    | τ₃ _ _ _ | τ₂ _ refl _ | τ₃ _ ¬p _ | τ₃ _ _ _
    = ⊥-elim (¬p refl)
  swap-injective _ _ _ _ _ refl refl
    | τ₃ _ _ _ | τ₃ _ _ _ | τ₁ _ _ _ | _
    = refl
  swap-injective _ _ _ _ _ refl refl
    | τ₃ _ _ _ | τ₃ _ ¬p _ | τ₂ _ refl _ | _
    = ⊥-elim (¬p refl)
  swap-injective _ _ _ _ _ refl refl
    | τ₃ _ ¬p _ | τ₃ _ _ _ | τ₃ _ _ _ | τ₂ _ refl _
    = ⊥-elim (¬p refl)
  swap-injective _ _ _ _ _ refl refl
    | τ₃ _ _ _ | τ₃ _ _ _ | τ₃ _ _ _ | τ₃ _ _ _
    = refl

  ... | τ₃ _ _ p | τ₁ q _ _ | _ | _
    = ⊥-elim (Fin.<-¬suc p q)
  ... | _ | _ | τ₃ _ _ p | τ₁ q _ _
    = ⊥-elim (Fin.<-¬suc p q)

  swap
    : (x : StateCategory.Object C)
    → (xs : Object)
    → (k : Fin (List.length xs))
    → Arrow (x ∷ xs) (List.swap x xs k)
  swap x xs k
    = record
    { lookup
      = λ k'
      → just
        (swap-lookup x xs k k')
    ; injective
      = λ k₁' k₂' p₁ p₂
      → swap-injective x xs k k₁' k₂'
        (Maybe.just-injective p₁)
        (Maybe.just-injective p₂)
    }

