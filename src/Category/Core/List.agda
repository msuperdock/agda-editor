module Category.Core.List where

open import Category.Core
  using (Arrow'; Associative; ChainObject; Compose; ComposeEqual;
    DependentArrow; DependentAssociative; DependentCompose;
    DependentComposeEqual; DependentIdentity; DependentObject;
    DependentPostcompose; DependentPrecompose; DependentSimplify; Identity;
    Object'; Postcompose; Precompose; Simplify)
open import Data.Any
  using (any)
open import Data.Equal
  using (_≡_; refl)
open import Data.Fin
  using (Fin; suc; zero)
open import Data.Function
  using (_$_; _∘_)
open import Data.Inspect
  using ([_]; inspect)
open import Data.List
  using (List; _∷_; _!_)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Vec
  using (Vec)

-- ## Base

-- ### Object'

object-list
  : Object'
  → Object'
object-list X
  = record
  { Object
    = List
      (Object'.Object X)
  }

-- ### Arrow'

-- #### Function

module _
  {X Y : Object'}
  where

  module ArrowList
    (F : Arrow' X Y)
    where

    record Arrow
      (xs : Object'.Object (object-list X))
      (ys : Object'.Object (object-list Y))
      : Set
      where

      field

        lookup
          : (k : Fin (List.length xs))
          → Maybe (l ∈ Fin (List.length ys)
            × Arrow'.Arrow F (xs ! k) (ys ! l))

        injective
          : (k₁ k₂ : Fin (List.length xs))
          → {l : Fin (List.length ys)}
          → {f₁ : Arrow'.Arrow F (xs ! k₁) (ys ! l)}
          → {f₂ : Arrow'.Arrow F (xs ! k₂) (ys ! l)}
          → lookup k₁ ≡ just (l , f₁)
          → lookup k₂ ≡ just (l , f₂)
          → k₁ ≡ k₂

    data LookupEqual
      (xs : Object'.Object (object-list X))
      (ys : Object'.Object (object-list Y))
      (k : Fin (List.length xs))
      : Maybe (l ∈ Fin (List.length ys)
        × Arrow'.Arrow F (xs ! k) (ys ! l))
      → Maybe (l ∈ Fin (List.length ys)
        × Arrow'.Arrow F (xs ! k) (ys ! l))
      → Set
      where

      nothing
        : LookupEqual xs ys k nothing nothing

      just
        : (l : Fin (List.length ys))
        → {f₁ f₂ : Arrow'.Arrow F (xs ! k) (ys ! l)}
        → Arrow'.ArrowEqual F f₁ f₂
        → LookupEqual xs ys k (just (l , f₁)) (just (l , f₂))

    lookup-refl
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {k : Fin (List.length xs)}
      → {f : Maybe (l ∈ Fin (List.length ys)
        × Arrow'.Arrow F (xs ! k) (ys ! l))}
      → LookupEqual xs ys k f f
    lookup-refl {f = nothing}
      = nothing
    lookup-refl {f = just (l , _)}
      = just l (Arrow'.arrow-refl F)

    lookup-refl'
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {k : Fin (List.length xs)}
      → {f₁ f₂ : Maybe (l ∈ Fin (List.length ys)
        × Arrow'.Arrow F (xs ! k) (ys ! l))}
      → f₁ ≡ f₂
      → LookupEqual xs ys k f₁ f₂
    lookup-refl' refl
      = lookup-refl

    lookup-sym
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {k : Fin (List.length xs)}
      → {f₁ f₂ : Maybe (l ∈ Fin (List.length ys)
        × Arrow'.Arrow F (xs ! k) (ys ! l))}
      → LookupEqual xs ys k f₁ f₂
      → LookupEqual xs ys k f₂ f₁
    lookup-sym nothing
      = nothing
    lookup-sym (just l p)
      = just l (Arrow'.arrow-sym F p)

    lookup-trans
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {k : Fin (List.length xs)}
      → {f₁ f₂ f₃ : Maybe (l ∈ Fin (List.length ys)
        × Arrow'.Arrow F (xs ! k) (ys ! l))}
      → LookupEqual xs ys k f₁ f₂
      → LookupEqual xs ys k f₂ f₃
      → LookupEqual xs ys k f₁ f₃
    lookup-trans nothing nothing
      = nothing
    lookup-trans (just l p₁) (just _ p₂)
      = just l (Arrow'.arrow-trans F p₁ p₂)

    lookup-cons
      : (x : Object'.Object X)
      → {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {k : Fin (List.length xs)}
      → {f₁ f₂ : Maybe (l ∈ Fin (List.length ys)
        × Arrow'.Arrow F (xs ! k) (ys ! l))}
      → LookupEqual xs ys k f₁ f₂
      → LookupEqual (x ∷ xs) ys (suc k) f₁ f₂
    lookup-cons _ nothing
      = nothing
    lookup-cons _ (just l p)
      = just l p

    data LookupEqual'
      {m n : ℕ}
      (xs₁ xs₂ : Vec (Object'.Object X) m)
      (ys₁ ys₂ : Vec (Object'.Object Y) n)
      (k : Fin m)
      : Maybe (l ∈ Fin n
        × Arrow'.Arrow F (Vec.lookup xs₁ k) (Vec.lookup ys₁ l))
      → Maybe (l ∈ Fin n
        × Arrow'.Arrow F (Vec.lookup xs₂ k) (Vec.lookup ys₂ l))
      → Set
      where

      nothing'
        : LookupEqual' xs₁ xs₂ ys₁ ys₂ k nothing nothing

      just'
        : (l : Fin n)
        → {f₁ : Arrow'.Arrow F (Vec.lookup xs₁ k) (Vec.lookup ys₁ l)}
        → {f₂ : Arrow'.Arrow F (Vec.lookup xs₂ k) (Vec.lookup ys₂ l)}
        → Arrow'.ArrowEqual' F f₁ f₂
        → LookupEqual' xs₁ xs₂ ys₁ ys₂ k (just (l , f₁)) (just (l , f₂))

    lookup-equal'
      : {m n : ℕ}
      → {xs : Vec (Object'.Object X) m}
      → {ys : Vec (Object'.Object Y) n}
      → {k : Fin m}
      → {f₁ f₂ : Maybe (l ∈ Fin n
        × Arrow'.Arrow F (Vec.lookup xs k) (Vec.lookup ys l))}
      → LookupEqual' xs xs ys ys k f₁ f₂
      → LookupEqual (any xs) (any ys) k f₁ f₂
    lookup-equal' nothing'
      = nothing
    lookup-equal' (just' l p)
      = just l (Arrow'.arrow-equal' F p)

    record ArrowEqual
      {xs : Object'.Object (object-list X)}
      {ys : Object'.Object (object-list Y)}
      (fs₁ fs₂ : Arrow xs ys)
      : Set
      where

      field

        lookup
          : (k : Fin (List.length xs))
          → LookupEqual xs ys k
            (Arrow.lookup fs₁ k)
            (Arrow.lookup fs₂ k)

    arrow-refl
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {fs : Arrow xs ys}
      → ArrowEqual fs fs
    arrow-refl
      = record
      { lookup
        = λ _ → lookup-refl
      }

    arrow-sym
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {fs₁ fs₂ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual fs₂ fs₁
    arrow-sym ps
      = record
      { lookup
        = λ k → lookup-sym
          (ArrowEqual.lookup ps k)
      }

    arrow-trans
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {fs₁ fs₂ fs₃ : Arrow xs ys}
      → ArrowEqual fs₁ fs₂
      → ArrowEqual fs₂ fs₃
      → ArrowEqual fs₁ fs₃
    arrow-trans ps₁ ps₂
      = record
      { lookup
        = λ k → lookup-trans
          (ArrowEqual.lookup ps₁ k)
          (ArrowEqual.lookup ps₂ k)
      }
    
  arrow-list
    : Arrow' X Y
    → Arrow'
      (object-list X)
      (object-list Y)
  arrow-list F
    = record {ArrowList F}

-- #### Equality

arrow-equal-list
  : {X Y : Object'}
  → (F : Arrow' X Y)
  → {m n : ℕ}
  → {xs₁ xs₂ : Vec (Object'.Object X) m}
  → {ys₁ ys₂ : Vec (Object'.Object Y) n}
  → {fs₁ : Arrow'.Arrow (arrow-list F) (any xs₁) (any ys₁)}
  → {fs₂ : Arrow'.Arrow (arrow-list F) (any xs₂) (any ys₂)}
  → xs₁ ≡ xs₂
  → ys₁ ≡ ys₂
  → ((k : Fin m) → ArrowList.LookupEqual' F xs₁ xs₂ ys₁ ys₂ k
    (ArrowList.Arrow.lookup fs₁ k)
    (ArrowList.Arrow.lookup fs₂ k))
  → Arrow'.ArrowEqual'
    (arrow-list F) fs₁ fs₂
arrow-equal-list F refl refl ps
  = Arrow'.arrow-equal
  $ record
  { lookup
    = λ k → ArrowList.lookup-equal' F (ps k)
  }

-- ### Simplify

module _
  {X Y : Object'}
  {F : Arrow' X Y}
  where

  module SimplifyList
    (s : Simplify F)
    where

    simplify-lookup
      : (xs : Object'.Object (object-list X))
      → (ys : Object'.Object (object-list Y))
      → ((k : Fin (List.length xs))
        → Maybe (l ∈ Fin (List.length ys)
          × Arrow'.Arrow F (xs ! k) (ys ! l)))
      → ((k : Fin (List.length xs))
        → Maybe (l ∈ Fin (List.length ys)
          × Arrow'.Arrow F (xs ! k) (ys ! l)))
    simplify-lookup (_ ∷ xs) ys f
      with f zero
      | simplify-lookup xs ys (f ∘ suc)
    ... | nothing | f'
      = λ
      { zero
        → nothing
      ; (suc k)
        → f' k
      }
    ... | just (l , g) | f'
      = λ
      { zero
        → just (l , Simplify.simplify s g)
      ; (suc k)
        → f' k
      }

    simplify-lookup-equal
      : (xs : Object'.Object (object-list X))
      → (ys : Object'.Object (object-list Y))
      → (f : (k : Fin (List.length xs))
        → Maybe (l ∈ Fin (List.length ys)
          × Arrow'.Arrow F (xs ! k) (ys ! l)))
      → (k : Fin (List.length xs))
      → ArrowList.LookupEqual F xs ys k (simplify-lookup xs ys f k) (f k)
    simplify-lookup-equal (_ ∷ _) _ f zero
      with f zero
    ... | nothing
      = ArrowList.lookup-refl F
    ... | just (l , g)
      = ArrowList.just l (Simplify.simplify-equal s g)
    simplify-lookup-equal (x ∷ xs) ys f (suc k)
      with f zero
    ... | nothing
      = ArrowList.lookup-cons F x (simplify-lookup-equal xs ys (f ∘ suc) k)
    ... | just _
      = ArrowList.lookup-cons F x (simplify-lookup-equal xs ys (f ∘ suc) k)

    simplify-injective
      : (xs : Object'.Object (object-list X))
      → (ys : Object'.Object (object-list Y))
      → (f : (k : Fin (List.length xs))
        → Maybe (l ∈ Fin (List.length ys)
          × Arrow'.Arrow F (xs ! k) (ys ! l)))
      → ((k₁ k₂ : Fin (List.length xs))
        → {l : Fin (List.length ys)}
        → {g₁ : Arrow'.Arrow F (xs ! k₁) (ys ! l)}
        → {g₂ : Arrow'.Arrow F (xs ! k₂) (ys ! l)}
        → f k₁ ≡ just (l , g₁)
        → f k₂ ≡ just (l , g₂)
        → k₁ ≡ k₂)
      → ((k₁ k₂ : Fin (List.length xs))
        → {l : Fin (List.length ys)}
        → {g₁ : Arrow'.Arrow F (xs ! k₁) (ys ! l)}
        → {g₂ : Arrow'.Arrow F (xs ! k₂) (ys ! l)}
        → simplify-lookup xs ys f k₁ ≡ just (l , g₁)
        → simplify-lookup xs ys f k₂ ≡ just (l , g₂)
        → k₁ ≡ k₂)
    simplify-injective xs ys f _ k₁ k₂ _ _
      with f k₁
      | inspect f k₁
      | simplify-lookup xs ys f k₁
      | simplify-lookup-equal xs ys f k₁
      | f k₂
      | inspect f k₂
      | simplify-lookup xs ys f k₂
      | simplify-lookup-equal xs ys f k₂
    simplify-injective _ _ _ p k₁ k₂ refl refl
      | _ | [ q₁ ] | _ | ArrowList.just _ _
      | _ | [ q₂ ] | _ | ArrowList.just _ _
      = p k₁ k₂ q₁ q₂

    simplify
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → Arrow'.Arrow (arrow-list F) xs ys
      → Arrow'.Arrow (arrow-list F) xs ys
    simplify {xs = xs} {ys = ys} fs
      = record
      { lookup
        = simplify-lookup xs ys
          (ArrowList.Arrow.lookup fs)
      ; injective
        = simplify-injective xs ys
          (ArrowList.Arrow.lookup fs)
          (ArrowList.Arrow.injective fs)
      }

    simplify-equal
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → (fs : Arrow'.Arrow (arrow-list F) xs ys)
      → Arrow'.ArrowEqual (arrow-list F) (simplify fs) fs
    simplify-equal {xs = xs} {ys = ys} fs
      = record
      { lookup
        = λ k → simplify-lookup-equal xs ys
          (ArrowList.Arrow.lookup fs) k
      }

  simplify-list
    : Simplify F
    → Simplify
      (arrow-list F)
  simplify-list s
    = record {SimplifyList s}

-- ### Identity

module _
  {X : Object'}
  {F : Arrow' X X}
  where

  module IdentityList
    (i : Identity F)
    where

    identity-lookup
      : (xs : Object'.Object (object-list X))
      → (k : Fin (List.length xs))
      → Maybe (l ∈ Fin (List.length xs)
        × Arrow'.Arrow F (xs ! k) (xs ! l))
    identity-lookup xs k
      = just (k , Identity.identity i (xs ! k))

    identity-injective
      : (xs : Object'.Object (object-list X))
      → (k₁ k₂ : Fin (List.length xs))
      → {l : Fin (List.length xs)}
      → {f₁ : Arrow'.Arrow F (xs ! k₁) (xs ! l)}
      → {f₂ : Arrow'.Arrow F (xs ! k₂) (xs ! l)}
      → identity-lookup xs k₁ ≡ just (l , f₁)
      → identity-lookup xs k₂ ≡ just (l , f₂)
      → k₁ ≡ k₂
    identity-injective _ _ _ refl refl
      = refl

    identity
      : (xs : Object'.Object (object-list X))
      → Arrow'.Arrow (arrow-list F) xs xs
    identity xs
      = record
      { lookup
        = identity-lookup xs
      ; injective
        = identity-injective xs
      }

  identity-list
    : Identity F
    → Identity
      (arrow-list F)
  identity-list i
    = record {IdentityList i}

-- ### Compose

module _
  {X Y Z : Object'}
  {F : Arrow' Y Z}
  {G : Arrow' X Y}
  {H : Arrow' X Z}
  where

  module ComposeList
    (j : Compose F G H)
    where

    compose-lookup'
      : (xs : Object'.Object (object-list X))
      → (ys : Object'.Object (object-list Y))
      → (zs : Object'.Object (object-list Z))
      → ((k : Fin (List.length ys))
        → Maybe (l ∈ Fin (List.length zs)
          × Arrow'.Arrow F (ys ! k) (zs ! l)))
      → ((k : Fin (List.length xs))
        → Maybe (l ∈ Fin (List.length ys)
          × Arrow'.Arrow G (xs ! k) (ys ! l)))
      → ((k : Fin (List.length xs))
        → Maybe (l ∈ Fin (List.length zs)
          × Arrow'.Arrow H (xs ! k) (zs ! l)))
    compose-lookup' _ _ _ fs gs k
      with gs k
    ... | nothing
      = nothing
    ... | just (l , g)
      with fs l
    ... | nothing
      = nothing
    ... | just (m , f)
      = just (m , Compose.compose j f g)

    compose-lookup
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {zs : Object'.Object (object-list Z)}
      → Arrow'.Arrow (arrow-list F) ys zs
      → Arrow'.Arrow (arrow-list G) xs ys
      → (k : Fin (List.length xs))
      → Maybe (l ∈ Fin (List.length zs)
        × Arrow'.Arrow H (xs ! k) (zs ! l))
    compose-lookup {xs = xs} {ys = ys} {zs = zs} fs gs
      = compose-lookup' xs ys zs
        (ArrowList.Arrow.lookup fs)
        (ArrowList.Arrow.lookup gs)

    compose-injective
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {zs : Object'.Object (object-list Z)}
      → (fs : Arrow'.Arrow (arrow-list F) ys zs)
      → (gs : Arrow'.Arrow (arrow-list G) xs ys)
      → (k₁ k₂ : Fin (List.length xs))
      → {l : Fin (List.length zs)}
      → {h₁ : Arrow'.Arrow H (xs ! k₁) (zs ! l)}
      → {h₂ : Arrow'.Arrow H (xs ! k₂) (zs ! l)}
      → compose-lookup fs gs k₁ ≡ just (l , h₁)
      → compose-lookup fs gs k₂ ≡ just (l , h₂)
      → k₁ ≡ k₂
    compose-injective fs gs k₁ k₂ _ _
      with ArrowList.Arrow.lookup gs k₁
      | inspect (ArrowList.Arrow.lookup gs) k₁
      | ArrowList.Arrow.lookup gs k₂
      | inspect (ArrowList.Arrow.lookup gs) k₂
    ... | just (l₁ , _) | _ | just (l₂ , _) | _
      with ArrowList.Arrow.lookup fs l₁
      | inspect (ArrowList.Arrow.lookup fs) l₁
      | ArrowList.Arrow.lookup fs l₂
      | inspect (ArrowList.Arrow.lookup fs) l₂
    compose-injective fs gs k₁ k₂ refl refl
      | just (l₁ , _) | [ p₁ ] | just (l₂ , _) | [ p₂ ]
      | just _ | [ q₁ ] | just _ | [ q₂ ]
      with ArrowList.Arrow.injective fs l₁ l₂ q₁ q₂
    ... | refl
      = ArrowList.Arrow.injective gs k₁ k₂ p₁ p₂

    compose
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {zs : Object'.Object (object-list Z)}
      → Arrow'.Arrow (arrow-list F) ys zs
      → Arrow'.Arrow (arrow-list G) xs ys
      → Arrow'.Arrow (arrow-list H) xs zs
    compose fs gs
      = record
      { lookup
        = compose-lookup fs gs
      ; injective
        = compose-injective fs gs
      }

  compose-list
    : Compose F G H
    → Compose
      (arrow-list F)
      (arrow-list G)
      (arrow-list H)
  compose-list j
    = record {ComposeList j}

-- ### ComposeEqual

module _
  {X Y Z : Object'}
  {F : Arrow' Y Z}
  {G : Arrow' X Y}
  {H : Arrow' X Z}
  {j : Compose F G H}
  where

  module ComposeEqualList
    (p : ComposeEqual j)
    where

    compose-equal-lookup
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {zs : Object'.Object (object-list Z)}
      → {fs₁ fs₂ : Arrow'.Arrow (arrow-list F) ys zs}
      → {gs₁ gs₂ : Arrow'.Arrow (arrow-list G) xs ys}
      → Arrow'.ArrowEqual (arrow-list F) fs₁ fs₂
      → Arrow'.ArrowEqual (arrow-list G) gs₁ gs₂
      → (k : Fin (List.length xs))
      → ArrowList.LookupEqual H xs zs k
        (ComposeList.compose-lookup j fs₁ gs₁ k)
        (ComposeList.compose-lookup j fs₂ gs₂ k)
    compose-equal-lookup {fs₁ = fs₁} {fs₂ = fs₂} {gs₁ = gs₁} {gs₂ = gs₂} qs rs k
      with ArrowList.Arrow.lookup gs₁ k
      | ArrowList.Arrow.lookup gs₂ k
      | ArrowList.ArrowEqual.lookup rs k
    ... | _ | _ | ArrowList.nothing
      = ArrowList.nothing
    ... | _ | _ | ArrowList.just l r'
      with ArrowList.Arrow.lookup fs₁ l
      | ArrowList.Arrow.lookup fs₂ l
      | ArrowList.ArrowEqual.lookup qs l
    ... | _ | _ | ArrowList.nothing
      = ArrowList.nothing
    ... | _ | _ | ArrowList.just m q'
      = ArrowList.just m (ComposeEqual.compose-equal p q' r')

    compose-equal
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {zs : Object'.Object (object-list Z)}
      → {fs₁ fs₂ : Arrow'.Arrow (arrow-list F) ys zs}
      → {gs₁ gs₂ : Arrow'.Arrow (arrow-list G) xs ys}
      → Arrow'.ArrowEqual (arrow-list F) fs₁ fs₂
      → Arrow'.ArrowEqual (arrow-list G) gs₁ gs₂
      → Arrow'.ArrowEqual (arrow-list H)
        (Compose.compose (compose-list j) fs₁ gs₁)
        (Compose.compose (compose-list j) fs₂ gs₂)
    compose-equal qs rs
      = record
      { lookup
        = compose-equal-lookup qs rs
      }

  compose-equal-list
    : ComposeEqual j
    → ComposeEqual
      (compose-list j)
  compose-equal-list p
    = record {ComposeEqualList p}

-- ### Precompose

module _
  {X Y : Object'}
  {F : Arrow' X Y}
  {G : Arrow' X X}
  {i : Identity G}
  {j : Compose F G F}
  where

  module PrecomposeList
    (p : Precompose i j)
    where

    precompose-lookup
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → (fs : Arrow'.Arrow (arrow-list F) xs ys)
      → (k : Fin (List.length xs))
      → ArrowList.LookupEqual F xs ys k
        (ArrowList.Arrow.lookup
          (Compose.compose (compose-list j) fs
            (Identity.identity (identity-list i) xs)) k)
        (ArrowList.Arrow.lookup fs k)
    precompose-lookup fs k
      with ArrowList.Arrow.lookup fs k
    ... | nothing
      = ArrowList.nothing
    ... | just (l , f)
      = ArrowList.just l (Precompose.precompose p f)

    precompose
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → (fs : Arrow'.Arrow (arrow-list F) xs ys)
      → Arrow'.ArrowEqual (arrow-list F)
        (Compose.compose (compose-list j) fs
          (Identity.identity (identity-list i) xs)) fs
    precompose fs
      = record
      { lookup
        = precompose-lookup fs
      }

  precompose-list
    : Precompose i j
    → Precompose
      (identity-list i)
      (compose-list j)
  precompose-list p
    = record {PrecomposeList p}

-- ### Postcompose

module _
  {X Y : Object'}
  {F : Arrow' Y Y}
  {G : Arrow' X Y}
  {i : Identity F}
  {j : Compose F G G}
  where

  module PostcomposeList
    (p : Postcompose i j)
    where

    postcompose-lookup
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → (gs : Arrow'.Arrow (arrow-list G) xs ys)
      → (k : Fin (List.length xs))
      → ArrowList.LookupEqual G xs ys k
        (ArrowList.Arrow.lookup
          (Compose.compose (compose-list j)
            (Identity.identity (identity-list i) ys) gs) k)
        (ArrowList.Arrow.lookup gs k)
    postcompose-lookup fs k
      with ArrowList.Arrow.lookup fs k
    ... | nothing
      = ArrowList.nothing
    ... | just (l , f)
      = ArrowList.just l (Postcompose.postcompose p f)

    postcompose
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → (gs : Arrow'.Arrow (arrow-list G) xs ys)
      → Arrow'.ArrowEqual (arrow-list G)
        (Compose.compose (compose-list j)
          (Identity.identity (identity-list i) ys) gs) gs
    postcompose fs
      = record
      { lookup
        = postcompose-lookup fs
      }

  postcompose-list
    : Postcompose i j
    → Postcompose
      (identity-list i)
      (compose-list j)
  postcompose-list p
    = record {PostcomposeList p}

-- ### Associative

module _
  {W X Y Z : Object'}
  {F : Arrow' Y Z}
  {G : Arrow' X Y}
  {H : Arrow' W X}
  {I : Arrow' X Z}
  {J : Arrow' W Y}
  {K : Arrow' W Z}
  {j : Compose F G I}
  {k : Compose G H J}
  {l : Compose I H K}
  {m : Compose F J K}
  where

  module AssociativeList
    (p : Associative j k l m)
    where

    associative-lookup
      : {ws : Object'.Object (object-list W)}
      → {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {zs : Object'.Object (object-list Z)}
      → (fs : Arrow'.Arrow (arrow-list F) ys zs)
      → (gs : Arrow'.Arrow (arrow-list G) xs ys)
      → (hs : Arrow'.Arrow (arrow-list H) ws xs)
      → (k' : Fin (List.length ws))
      → ArrowList.LookupEqual K ws zs k'
        (ArrowList.Arrow.lookup
          (Compose.compose (compose-list l)
            (Compose.compose (compose-list j) fs gs) hs) k')
        (ArrowList.Arrow.lookup
          (Compose.compose (compose-list m) fs
            (Compose.compose (compose-list k) gs hs)) k')
    associative-lookup fs gs hs k'
      with ArrowList.Arrow.lookup hs k'
    ... | nothing
      = ArrowList.nothing
    ... | just (l' , h)
      with ArrowList.Arrow.lookup gs l'
    ... | nothing
      = ArrowList.nothing
    ... | just (m' , g)
      with ArrowList.Arrow.lookup fs m'
    ... | nothing
      = ArrowList.nothing
    ... | just (n' , f)
      = ArrowList.just n' (Associative.associative p f g h)

    associative
      : {ws : Object'.Object (object-list W)}
      → {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {zs : Object'.Object (object-list Z)}
      → (fs : Arrow'.Arrow (arrow-list F) ys zs)
      → (gs : Arrow'.Arrow (arrow-list G) xs ys)
      → (hs : Arrow'.Arrow (arrow-list H) ws xs)
      → Arrow'.ArrowEqual (arrow-list K)
        (Compose.compose (compose-list l)
          (Compose.compose (compose-list j) fs gs) hs)
        (Compose.compose (compose-list m) fs
          (Compose.compose (compose-list k) gs hs))
    associative fs gs hs
      = record
      { lookup
        = associative-lookup fs gs hs
      }

  associative-list
    : Associative j k l m
    → Associative
      (compose-list j)
      (compose-list k)
      (compose-list l)
      (compose-list m)
  associative-list p
    = record {AssociativeList p}

-- ## Dependent

-- ### DependentObject

dependent-object-list
  : {n : ℕ}
  → {X : ChainObject n}
  → DependentObject X
  → DependentObject X
dependent-object-list {n = zero} X'
  = object-list X'
dependent-object-list {n = suc _} X'
  = record
  { tail
    = λ x → dependent-object-list
      (DependentObject.tail X' x)
  }

-- ### DependentArrow

dependent-arrow-list
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → DependentArrow X' Y'
  → DependentArrow
    (dependent-object-list X')
    (dependent-object-list Y')
dependent-arrow-list {n = zero} F
  = arrow-list F
dependent-arrow-list {n = suc _} F
  = record
  { tail
    = λ x y → dependent-arrow-list
      (DependentArrow.tail F x y)
  }

-- ### DependentSimplify

dependent-simplify-list
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : DependentArrow X' Y'}
  → DependentSimplify F
  → DependentSimplify
    (dependent-arrow-list F)
dependent-simplify-list {n = zero} s
  = simplify-list s
dependent-simplify-list {n = suc _} s
  = record
  { tail
    = λ x y → dependent-simplify-list
      (DependentSimplify.tail s x y)
  }

-- ### DependentIdentity

dependent-identity-list
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : DependentArrow X' X'}
  → DependentIdentity F
  → DependentIdentity
    (dependent-arrow-list F)
dependent-identity-list {n = zero} i
  = identity-list i
dependent-identity-list {n = suc _} i
  = record
  { tail
    = λ x → dependent-identity-list
      (DependentIdentity.tail i x)
  }

-- ### DependentCompose

dependent-compose-list
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {Z' : DependentObject Z}
  → {F : DependentArrow Y' Z'}
  → {G : DependentArrow X' Y'}
  → {H : DependentArrow X' Z'}
  → DependentCompose F G H
  → DependentCompose
    (dependent-arrow-list F)
    (dependent-arrow-list G)
    (dependent-arrow-list H)
dependent-compose-list {n = zero} j
  = compose-list j
dependent-compose-list {n = suc _} j
  = record
  { tail
    = λ x y z → dependent-compose-list
      (DependentCompose.tail j x y z)
  }

-- ### DependentComposeEqual

dependent-compose-equal-list
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {Z' : DependentObject Z}
  → {F : DependentArrow Y' Z'}
  → {G : DependentArrow X' Y'}
  → {H : DependentArrow X' Z'}
  → {j : DependentCompose F G H}
  → DependentComposeEqual j
  → DependentComposeEqual
    (dependent-compose-list j)
dependent-compose-equal-list {n = zero} p
  = compose-equal-list p
dependent-compose-equal-list {n = suc _} p
  = record
  { tail
    = λ x y z → dependent-compose-equal-list
      (DependentComposeEqual.tail p x y z)
  }

-- ### DependentPrecompose

dependent-precompose-list
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : DependentArrow X' Y'}
  → {G : DependentArrow X' X'}
  → {i : DependentIdentity G}
  → {j : DependentCompose F G F}
  → DependentPrecompose i j
  → DependentPrecompose
    (dependent-identity-list i)
    (dependent-compose-list j)
dependent-precompose-list {n = zero} p
  = precompose-list p
dependent-precompose-list {n = suc _} p
  = record
  { tail
    = λ x y → dependent-precompose-list
      (DependentPrecompose.tail p x y)
  }

-- ### DependentPostcompose

dependent-postcompose-list
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : DependentArrow Y' Y'}
  → {G : DependentArrow X' Y'}
  → {i : DependentIdentity F}
  → {j : DependentCompose F G G}
  → DependentPostcompose i j
  → DependentPostcompose
    (dependent-identity-list i)
    (dependent-compose-list j)
dependent-postcompose-list {n = zero} p
  = postcompose-list p
dependent-postcompose-list {n = suc _} p
  = record
  { tail
    = λ x y → dependent-postcompose-list
      (DependentPostcompose.tail p x y)
  }

-- ### DependentAssociative

dependent-associative-list
  : {n : ℕ}
  → {W X Y Z : ChainObject n}
  → {W' : DependentObject W}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {Z' : DependentObject Z}
  → {F : DependentArrow Y' Z'}
  → {G : DependentArrow X' Y'}
  → {H : DependentArrow W' X'}
  → {I : DependentArrow X' Z'}
  → {J : DependentArrow W' Y'}
  → {K : DependentArrow W' Z'}
  → {j : DependentCompose F G I}
  → {k : DependentCompose G H J}
  → {l : DependentCompose I H K}
  → {m : DependentCompose F J K}
  → DependentAssociative j k l m
  → DependentAssociative
    (dependent-compose-list j)
    (dependent-compose-list k)
    (dependent-compose-list l)
    (dependent-compose-list m)
dependent-associative-list {n = zero} p
  = associative-list p
dependent-associative-list {n = suc _} p
  = record
  { tail
    = λ w x y z → dependent-associative-list
      (DependentAssociative.tail p w x y z)
  }

