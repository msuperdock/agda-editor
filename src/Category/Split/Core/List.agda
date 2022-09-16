module Category.Split.Core.List where

open import Category.Core
  using (Arrow'; ChainObject; Compose; ComposeEqual; DependentArrow;
    DependentCompose; DependentComposeEqual; DependentIdentity; DependentObject;
    Identity; Object')
open import Category.Core.List
  using (module ArrowList; module ComposeList; module IdentityList; arrow-list;
    compose-list; dependent-arrow-list; dependent-compose-list;
    dependent-identity-list; dependent-object-list; identity-list; object-list)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitCompose; DependentSplitIdentity;
    DependentSplitMap; SplitBase; SplitCompose; SplitIdentity; SplitMap)
open import Data.Any
  using (any)
open import Data.Equal
  using (_≡_; refl; sub; sym)
open import Data.Fin
  using (Fin)
open import Data.Function
  using (_$_)
open import Data.Inspect
  using ([_]; inspect)
open import Data.List
  using (List; _!_)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Vec
  using (Vec; cons; nil)

-- ## Base

-- ### SplitBase

module _
  {X X' : Object'}
  where

  module SplitBaseList
    (a : SplitBase X X')
    where

    base
      : Object'.Object (object-list X)
      → Maybe (Object'.Object (object-list X'))
    base
      = List.map-maybe
        (SplitBase.base a)

    unbase
      : Object'.Object (object-list X')
      → Object'.Object (object-list X)
    unbase
      = List.map
        (SplitBase.unbase a)

    base-unbase'
      : {n : ℕ}
      → (xs : Vec (Object'.Object X') n)
      → Vec.map-maybe (SplitBase.base a)
        (Vec.map (SplitBase.unbase a) xs)
      ≡ just xs
    base-unbase' nil
      = refl
    base-unbase' (cons x (any xs))
      with SplitBase.base a (SplitBase.unbase a x)
      | SplitBase.base-unbase a x
      | Vec.map-maybe (SplitBase.base a)
        (Vec.map (SplitBase.unbase a) xs)
      | base-unbase' xs
    ... | _ | refl | _ | refl
      = refl

    base-unbase
      : (xs : Object'.Object (object-list X'))
      → base (unbase xs) ≡ just xs
    base-unbase (any xs)
      = sub (Maybe.map any) (base-unbase' xs)

  split-base-list
    : SplitBase X X'
    → SplitBase
      (object-list X)
      (object-list X')
  split-base-list a
    = record {SplitBaseList a}

-- ### SplitMap

module _
  {X Y X' Y' : Object'}
  {F : Arrow' X Y}
  {F' : Arrow' X' Y'}
  {a : SplitBase X X'}
  {b : SplitBase Y Y'}
  where

  module SplitMapList
    (m : SplitMap F F' a b)
    where

    map-lookup
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-list X')}
      → {ys' : Object'.Object (object-list Y')}
      → SplitBase.base (split-base-list a) xs ≡ just xs'
      → SplitBase.base (split-base-list b) ys ≡ just ys'
      → Arrow'.Arrow (arrow-list F) xs ys
      → (k : Fin (List.length xs'))
      → Maybe (l ∈ Fin (List.length ys')
        × Arrow'.Arrow F' (xs' ! k) (ys' ! l))
    map-lookup {xs = any xs} {ys = any ys} _ _ _ _
      with Vec.map-maybe (SplitBase.base a) xs
      | inspect (Vec.map-maybe (SplitBase.base a)) xs
      | Vec.map-maybe (SplitBase.base b) ys
      | inspect (Vec.map-maybe (SplitBase.base b)) ys
    map-lookup {xs = any xs} {ys = any ys} refl refl fs k
      | just _ | [ p ] | just _ | [ q ]
      with ArrowList.Arrow.lookup fs k
    ... | nothing
      = nothing
    ... | just (l , f)
      = just (l , SplitMap.map m p' q' f)
      where
        p' = Vec.lookup-map-just (SplitBase.base a) xs p k
        q' = Vec.lookup-map-just (SplitBase.base b) ys q l

    map-injective
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-list X')}
      → {ys' : Object'.Object (object-list Y')}
      → (p : SplitBase.base (split-base-list a) xs ≡ just xs')
      → (q : SplitBase.base (split-base-list b) ys ≡ just ys')
      → (fs : Arrow'.Arrow (arrow-list F) xs ys)
      → (k₁ k₂ : Fin (List.length xs'))
      → {l : Fin (List.length ys')}
      → {f₁' : Arrow'.Arrow F' (xs' ! k₁) (ys' ! l)}
      → {f₂' : Arrow'.Arrow F' (xs' ! k₂) (ys' ! l)}
      → map-lookup p q fs k₁ ≡ just (l , f₁')
      → map-lookup p q fs k₂ ≡ just (l , f₂')
      → k₁ ≡ k₂
    map-injective {xs = any xs} {ys = any ys} _ _ _ _ _ _ _
      with Vec.map-maybe (SplitBase.base a) xs
      | inspect (Vec.map-maybe (SplitBase.base a)) xs
      | Vec.map-maybe (SplitBase.base b) ys
      | inspect (Vec.map-maybe (SplitBase.base b)) ys
    map-injective refl refl f k₁ k₂ _ _
      | just _ | _ | just _ | _
      with ArrowList.Arrow.lookup f k₁
      | inspect (ArrowList.Arrow.lookup f) k₁
      | ArrowList.Arrow.lookup f k₂
      | inspect (ArrowList.Arrow.lookup f) k₂
    map-injective _ _ f k₁ k₂ refl refl
      | _ | _ | _ | _
      | just _ | [ p₁ ] | just _ | [ p₂ ]
      = ArrowList.Arrow.injective f k₁ k₂ p₁ p₂

    map
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-list X')}
      → {ys' : Object'.Object (object-list Y')}
      → SplitBase.base (split-base-list a) xs ≡ just xs'
      → SplitBase.base (split-base-list b) ys ≡ just ys'
      → Arrow'.Arrow (arrow-list F) xs ys
      → Arrow'.Arrow (arrow-list F') xs' ys'
    map p q fs
      = record
      { lookup
        = map-lookup p q fs
      ; injective
        = map-injective p q fs
      }

    map-equal-lookup
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-list X')}
      → {ys' : Object'.Object (object-list Y')}
      → {fs₁ fs₂ : Arrow'.Arrow (arrow-list F) xs ys}
      → (p : SplitBase.base (split-base-list a) xs ≡ just xs')
      → (q : SplitBase.base (split-base-list b) ys ≡ just ys')
      → Arrow'.ArrowEqual (arrow-list F) fs₁ fs₂
      → (k : Fin (List.length xs'))
      → ArrowList.LookupEqual F' xs' ys' k
        (map-lookup p q fs₁ k)
        (map-lookup p q fs₂ k)
    map-equal-lookup {xs = any xs} {ys = any ys} _ _ _ _
      with Vec.map-maybe (SplitBase.base a) xs
      | inspect (Vec.map-maybe (SplitBase.base a)) xs
      | Vec.map-maybe (SplitBase.base b) ys
      | inspect (Vec.map-maybe (SplitBase.base b)) ys
    map-equal-lookup {xs = any xs} {ys = any ys}
      {fs₁ = fs₁} {fs₂ = fs₂} refl refl rs k
      | just _ | [ p ] | just _ | [ q ]
      with ArrowList.Arrow.lookup fs₁ k
      | ArrowList.Arrow.lookup fs₂ k
      | ArrowList.ArrowEqual.lookup rs k
    ... | _ | _ | ArrowList.nothing
      = ArrowList.nothing
    ... | _ | _ | ArrowList.just l r
      = ArrowList.just l (SplitMap.map-equal m p' q' r)
      where
        p' = Vec.lookup-map-just (SplitBase.base a) xs p k
        q' = Vec.lookup-map-just (SplitBase.base b) ys q l

    map-equal
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {xs' : Object'.Object (object-list X')}
      → {ys' : Object'.Object (object-list Y')}
      → {fs₁ fs₂ : Arrow'.Arrow (arrow-list F) xs ys}
      → (p : SplitBase.base (split-base-list a) xs ≡ just xs')
      → (q : SplitBase.base (split-base-list b) ys ≡ just ys')
      → Arrow'.ArrowEqual (arrow-list F) fs₁ fs₂
      → Arrow'.ArrowEqual (arrow-list F') (map p q fs₁) (map p q fs₂)
    map-equal p q rs
      = record
      { lookup
        = map-equal-lookup p q rs
      }

    unmap-lookup
      : {xs : Object'.Object (object-list X')}
      → {ys : Object'.Object (object-list Y')}
      → Arrow'.Arrow (arrow-list F') xs ys
      → (k : Fin (List.length (SplitBase.unbase (split-base-list a) xs)))
      → Maybe (l ∈ Fin (List.length (SplitBase.unbase (split-base-list b) ys))
        × Arrow'.Arrow F
          (SplitBase.unbase (split-base-list a) xs ! k)
          (SplitBase.unbase (split-base-list b) ys ! l))
    unmap-lookup {xs = any xs} {ys = any ys} fs' k
      with ArrowList.Arrow.lookup fs' k
    ... | nothing
      = nothing
    ... | just (l , f)
      = just (l , (Arrow'.arrow F p q (SplitMap.unmap m f)))
      where
        p = Vec.lookup-map (SplitBase.unbase a) xs k
        q = Vec.lookup-map (SplitBase.unbase b) ys l

    unmap-injective
      : {xs : Object'.Object (object-list X')}
      → {ys : Object'.Object (object-list Y')}
      → (fs' : Arrow'.Arrow (arrow-list F') xs ys)
      → (k₁ k₂ : Fin (List.length (SplitBase.unbase (split-base-list a) xs)))
      → {l : Fin (List.length (SplitBase.unbase (split-base-list b) ys))}
      → {f₁ : Arrow'.Arrow F
        (SplitBase.unbase (split-base-list a) xs ! k₁)
        (SplitBase.unbase (split-base-list b) ys ! l)}
      → {f₂ : Arrow'.Arrow F
        (SplitBase.unbase (split-base-list a) xs ! k₂)
        (SplitBase.unbase (split-base-list b) ys ! l)}
      → unmap-lookup fs' k₁ ≡ just (l , f₁)
      → unmap-lookup fs' k₂ ≡ just (l , f₂)
      → k₁ ≡ k₂
    unmap-injective fs' k₁ k₂ _ _
      with ArrowList.Arrow.lookup fs' k₁
      | inspect (ArrowList.Arrow.lookup fs') k₁
      | ArrowList.Arrow.lookup fs' k₂
      | inspect (ArrowList.Arrow.lookup fs') k₂
    unmap-injective fs' k₁ k₂ refl refl
      | just _ | [ p₁ ] | just _ | [ p₂ ]
      = ArrowList.Arrow.injective fs' k₁ k₂ p₁ p₂

    unmap
      : {xs : Object'.Object (object-list X')}
      → {ys : Object'.Object (object-list Y')}
      → Arrow'.Arrow (arrow-list F') xs ys
      → Arrow'.Arrow (arrow-list F)
        (SplitBase.unbase (split-base-list a) xs)
        (SplitBase.unbase (split-base-list b) ys)
    unmap fs
      = record
      { lookup
        = unmap-lookup fs
      ; injective
        = unmap-injective fs
      }

    unmap-equal-lookup
      : {xs : Object'.Object (object-list X')}
      → {ys : Object'.Object (object-list Y')}
      → {fs₁ fs₂ : Arrow'.Arrow (arrow-list F') xs ys}
      → Arrow'.ArrowEqual (arrow-list F') fs₁ fs₂
      → (k : Fin (List.length xs))
      → ArrowList.LookupEqual F
        (SplitBase.unbase (split-base-list a) xs)
        (SplitBase.unbase (split-base-list b) ys) k
        (unmap-lookup fs₁ k)
        (unmap-lookup fs₂ k)
    unmap-equal-lookup {xs = any xs} {ys = any ys} {fs₁ = fs₁} {fs₂ = fs₂} ps k
      with ArrowList.Arrow.lookup fs₁ k
      | ArrowList.Arrow.lookup fs₂ k
      | ArrowList.ArrowEqual.lookup ps k
    ... | _ | _ | ArrowList.nothing
      = ArrowList.nothing
    ... | _ | _ | ArrowList.just l p
      = ArrowList.just l
      $ Arrow'.arrow-equal'' F q r
        (SplitMap.unmap-equal m p)
      where
        q = Vec.lookup-map (SplitBase.unbase a) xs k
        r = Vec.lookup-map (SplitBase.unbase b) ys l

    unmap-equal
      : {xs : Object'.Object (object-list X')}
      → {ys : Object'.Object (object-list Y')}
      → {fs₁ fs₂ : Arrow'.Arrow (arrow-list F') xs ys}
      → Arrow'.ArrowEqual (arrow-list F') fs₁ fs₂
      → Arrow'.ArrowEqual (arrow-list F) (unmap fs₁) (unmap fs₂)
    unmap-equal ps
      = record
      { lookup
        = unmap-equal-lookup ps
      }

    map-unmap-lookup
      : {xs : Object'.Object (object-list X')}
      → {ys : Object'.Object (object-list Y')}
      → (p : SplitBase.base (split-base-list a)
        (SplitBase.unbase (split-base-list a) xs)
        ≡ just xs)
      → (q : SplitBase.base (split-base-list b)
        (SplitBase.unbase (split-base-list b) ys)
        ≡ just ys)
      → (fs : Arrow'.Arrow (arrow-list F') xs ys)
      → (k : Fin (List.length xs))
      → ArrowList.LookupEqual F' xs ys k
        (map-lookup p q (unmap fs) k)
        (ArrowList.Arrow.lookup fs k)
    map-unmap-lookup {xs = any xs'} {ys = any ys'} _ _ _ _
      with Vec.map-maybe (SplitBase.base a)
        (Vec.map (SplitBase.unbase a) xs')
      | inspect (Vec.map-maybe (SplitBase.base a))
        (Vec.map (SplitBase.unbase a) xs')
      | Vec.map-maybe (SplitBase.base b)
        (Vec.map (SplitBase.unbase b) ys')
      | inspect (Vec.map-maybe (SplitBase.base b))
        (Vec.map (SplitBase.unbase b) ys')
    map-unmap-lookup {xs = any xs'} {ys = any ys'} refl refl fs k
      | just _ | [ p ] | just _ | [ q ]
      with ArrowList.Arrow.lookup fs k
    ... | nothing
      = ArrowList.nothing
    ... | just (l , f)
      = ArrowList.just l
      $ Arrow'.arrow-equal' F'
      $ Arrow'.arrow-trans' F' (SplitMap.map-equal' m p'' p''' q'' q'''
        (Arrow'.arrow-refl'' F p' q'))
      $ SplitMap.map-unmap' m p''' q''' f
      where
        xs = Vec.map (SplitBase.unbase a) xs'
        ys = Vec.map (SplitBase.unbase b) ys'
        p' = Vec.lookup-map (SplitBase.unbase a) xs' k
        q' = Vec.lookup-map (SplitBase.unbase b) ys' l
        p'' = Vec.lookup-map-just (SplitBase.base a) xs p k
        q'' = Vec.lookup-map-just (SplitBase.base b) ys q l
        p''' = SplitBase.base-unbase a (Vec.lookup xs' k)
        q''' = SplitBase.base-unbase b (Vec.lookup ys' l)

    map-unmap
      : {xs : Object'.Object (object-list X')}
      → {ys : Object'.Object (object-list Y')}
      → (p : SplitBase.base (split-base-list a)
        (SplitBase.unbase (split-base-list a) xs)
        ≡ just xs)
      → (q : SplitBase.base (split-base-list b)
        (SplitBase.unbase (split-base-list b) ys)
        ≡ just ys)
      → (fs : Arrow'.Arrow (arrow-list F') xs ys)
      → Arrow'.ArrowEqual (arrow-list F') (map p q (unmap fs)) fs
    map-unmap p q fs
      = record
      { lookup
        = map-unmap-lookup p q fs
      }

  split-map-list
    : SplitMap F F' a b
    → SplitMap
      (arrow-list F)
      (arrow-list F')
      (split-base-list a)
      (split-base-list b)
  split-map-list m
    = record {SplitMapList m}

-- ### SplitIdentity

module _
  {X X' : Object'}
  {F : Arrow' X X}
  {F' : Arrow' X' X'}
  {i : Identity F}
  {i' : Identity F'}
  {a : SplitBase X X'}
  {m : SplitMap F F' a a}
  where

  module SplitIdentityList
    (p : SplitIdentity i i' m)
    where

    map-lookup
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-list X')}
      → (q : SplitBase.base (split-base-list a) xs ≡ just xs')
      → (k : Fin (List.length xs'))
      → ArrowList.LookupEqual F' xs' xs' k
        (SplitMapList.map-lookup m q q
          (Identity.identity (identity-list i) xs) k)
        (IdentityList.identity-lookup i' xs' k)
    map-lookup (any xs) _ _
      with Vec.map-maybe (SplitBase.base a) xs
      | inspect (Vec.map-maybe (SplitBase.base a)) xs
    map-lookup (any xs) refl k | just _ | [ q ]
      = ArrowList.just k (SplitIdentity.map p (Vec.lookup xs k) q')
      where
        q' = Vec.lookup-map-just (SplitBase.base a) xs q k

    map
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-list X')}
      → (q : SplitBase.base (split-base-list a) xs ≡ just xs')
      → Arrow'.ArrowEqual (arrow-list F')
        (SplitMap.map (split-map-list m) q q
          (Identity.identity (identity-list i) xs))
        (Identity.identity (identity-list i') xs')
    map xs q
      = record
      { lookup
        = map-lookup xs q
      }

    unmap-lookup
      : (xs : Object'.Object (object-list X'))
      → (k : Fin (List.length xs))
      → ArrowList.LookupEqual F
        (SplitBase.unbase (split-base-list a) xs)
        (SplitBase.unbase (split-base-list a) xs) k
        (SplitMapList.unmap-lookup m
          (Identity.identity (identity-list i') xs) k)
        (IdentityList.identity-lookup i
          (SplitBase.unbase (split-base-list a) xs) k)
    unmap-lookup (any xs) k
      = ArrowList.just k
      $ Arrow'.arrow-equal' F
      $ Arrow'.arrow-trans' F (Arrow'.arrow-refl'' F q q)
      $ Arrow'.arrow-trans' F (SplitIdentity.unmap' p (Vec.lookup xs k))
      $ Identity.identity-equal i (sym q)
      where
        q = Vec.lookup-map (SplitBase.unbase a) xs k

    unmap
      : (xs : Object'.Object (object-list X'))
      → Arrow'.ArrowEqual (arrow-list F)
        (SplitMap.unmap (split-map-list m)
          (Identity.identity (identity-list i') xs))
        (Identity.identity (identity-list i)
          (SplitBase.unbase (split-base-list a) xs))
    unmap xs
      = record
      { lookup
        = unmap-lookup xs
      }

    normalize-arrow-lookup'
      : {n : ℕ}
      → {xs' : Vec (Object'.Object X') n}
      → (xs : Vec (Object'.Object X) n)
      → Vec.map-maybe (SplitBase.base a) xs ≡ just xs'
      → (k : Fin n)
      → Arrow'.Arrow F
        (Vec.lookup xs k)
        (Vec.lookup (Vec.map (SplitBase.unbase a) xs') k)
    normalize-arrow-lookup' {xs' = xs'} xs q k
      with Vec.lookup (Vec.map (SplitBase.unbase a) xs') k
      | Vec.lookup-map (SplitBase.unbase a) xs' k
    ... | _ | refl
      = SplitIdentity.normalize-arrow p
        (Vec.lookup xs k)
        (Vec.lookup-map-just (SplitBase.base a) xs q k)

    normalize-arrow-lookup
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-list X')}
      → SplitBase.base (split-base-list a) xs ≡ just xs'
      → (k : Fin (List.length xs))
      → Maybe (l ∈ Fin (List.length (SplitBase.unbase (split-base-list a) xs'))
        × Arrow'.Arrow F (xs ! k)
          (SplitBase.unbase (split-base-list a) xs' ! l))
    normalize-arrow-lookup (any xs) _ _
      with Vec.map-maybe (SplitBase.base a) xs
      | inspect (Vec.map-maybe (SplitBase.base a)) xs
    normalize-arrow-lookup (any xs) refl k | just _ | [ q ]
      = just (k , normalize-arrow-lookup' xs q k)

    normalize-arrow-injective
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-list X')}
      → (q : SplitBase.base (split-base-list a) xs ≡ just xs')
      → (k₁ k₂ : Fin (List.length xs))
      → {l : Fin (List.length (SplitBase.unbase (split-base-list a) xs'))}
      → {f₁ : Arrow'.Arrow F (xs ! k₁)
        (SplitBase.unbase (split-base-list a) xs' ! l)}
      → {f₂ : Arrow'.Arrow F (xs ! k₂)
        (SplitBase.unbase (split-base-list a) xs' ! l)}
      → normalize-arrow-lookup xs q k₁ ≡ just (l , f₁)
      → normalize-arrow-lookup xs q k₂ ≡ just (l , f₂)
      → k₁ ≡ k₂
    normalize-arrow-injective (any xs) _ _ _ _ _
      with Vec.map-maybe (SplitBase.base a) xs
      | inspect (Vec.map-maybe (SplitBase.base a)) xs
    normalize-arrow-injective _ refl _ _ refl refl | just _ | _
      = refl

    normalize-arrow
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-list X')}
      → SplitBase.base (split-base-list a) xs ≡ just xs'
      → Arrow'.Arrow (arrow-list F) xs
        (SplitBase.unbase (split-base-list a) xs')
    normalize-arrow xs q
      = record
      { lookup
        = normalize-arrow-lookup xs q
      ; injective
        = normalize-arrow-injective xs q
      }

    normalize-valid-lookup'
      : {n : ℕ}
      → (xs : Vec (Object'.Object X) n)
      → {xs' : Vec (Object'.Object X') n}
      → (q : Vec.map-maybe (SplitBase.base a) xs ≡ just xs')
      → (k : Fin n)
      → Arrow'.ArrowEqual' F
        (normalize-arrow-lookup' xs q k)
        (SplitIdentity.normalize-arrow p
          (Vec.lookup xs k)
          (Vec.lookup-map-just (SplitBase.base a) xs q k))
    normalize-valid-lookup' _ {xs' = xs'} _ k
      with Vec.lookup (Vec.map (SplitBase.unbase a) xs') k
      | Vec.lookup-map (SplitBase.unbase a) xs' k
    ... | _ | refl
      = Arrow'.arrow-refl' F

    normalize-valid-lookup
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-list X')}
      → (q : SplitBase.base (split-base-list a) xs ≡ just xs')
      → (r : SplitBase.base (split-base-list a)
        (SplitBase.unbase (split-base-list a) xs')
        ≡ just xs')
      → (k : Fin (List.length xs'))
      → ArrowList.LookupEqual F' xs' xs' k
        (SplitMapList.map-lookup m q r (normalize-arrow xs q) k)
        (IdentityList.identity-lookup i' xs' k)
    normalize-valid-lookup (any xs) {xs' = any xs'} q _ _
      with normalize-arrow (any xs) q
      | inspect ArrowList.Arrow.lookup (normalize-arrow (any xs) q)
    ... | _ | _
      with Vec.map-maybe (SplitBase.base a) xs
      | inspect (Vec.map-maybe (SplitBase.base a)) xs
      | Vec.map-maybe (SplitBase.base a)
        (Vec.map (SplitBase.unbase a) xs')
      | inspect (Vec.map-maybe (SplitBase.base a))
        (Vec.map (SplitBase.unbase a) xs')
    normalize-valid-lookup (any xs) {xs' = any xs'} refl refl k
      | _ | [ refl ] | just _ | [ q ] | just _ | [ r ]
      = ArrowList.just k
      $ Arrow'.arrow-equal' F'
      $ Arrow'.arrow-trans' F' (SplitMap.map-equal' m q' q' r' s
        (normalize-valid-lookup' xs q k))
      $ SplitIdentity.normalize-valid' p (Vec.lookup xs k) q' q' s
      where
        q' = Vec.lookup-map-just (SplitBase.base a) xs q k
        r' = Vec.lookup-map-just (SplitBase.base a)
          (Vec.map (SplitBase.unbase a) xs') r k
        s = SplitBase.base-unbase a (Vec.lookup xs' k)

    normalize-valid
      : (xs : Object'.Object (object-list X))
      → {xs' : Object'.Object (object-list X')}
      → (q : SplitBase.base (split-base-list a) xs ≡ just xs')
      → (r : SplitBase.base (split-base-list a)
        (SplitBase.unbase (split-base-list a) xs')
        ≡ just xs')
      → Arrow'.ArrowEqual (arrow-list F')
        (SplitMap.map (split-map-list m) q r (normalize-arrow xs q))
        (Identity.identity (identity-list i') xs')
    normalize-valid xs q r
      = record
      { lookup
        = normalize-valid-lookup xs q r
      }

  split-identity-list
    : SplitIdentity i i' m
    → SplitIdentity
      (identity-list i)
      (identity-list i')
      (split-map-list m)
  split-identity-list p
    = record {SplitIdentityList p}

-- ### SplitCompose

module _
  {X Y Z X' Y' Z' : Object'}
  {F : Arrow' Y Z}
  {G : Arrow' X Y}
  {H : Arrow' X Z}
  {F' : Arrow' Y' Z'}
  {G' : Arrow' X' Y'}
  {H' : Arrow' X' Z'}
  {j : Compose F G H}
  {j' : Compose F' G' H'}
  where

  module SplitComposeList
    (p : ComposeEqual j)
    {a : SplitBase X X'}
    {b : SplitBase Y Y'}
    {c : SplitBase Z Z'}
    {m : SplitMap F F' b c}
    {n : SplitMap G G' a b}
    {o : SplitMap H H' a c}
    (q : SplitCompose j j' m n o)
    where

    map-lookup
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {zs : Object'.Object (object-list Z)}
      → {xs' : Object'.Object (object-list X')}
      → {ys' : Object'.Object (object-list Y')}
      → {zs' : Object'.Object (object-list Z')}
      → (r : SplitBase.base (split-base-list a) xs ≡ just xs')
      → (s : SplitBase.base (split-base-list b) ys ≡ just ys')
      → (t : SplitBase.base (split-base-list c) zs ≡ just zs')
      → (fs : Arrow'.Arrow (arrow-list F) ys zs)
      → (gs : Arrow'.Arrow (arrow-list G) xs ys)
      → (k : Fin (List.length xs'))
      → ArrowList.LookupEqual H' xs' zs' k
        (SplitMapList.map-lookup o r t
          (Compose.compose (compose-list j) fs gs) k)
        (ComposeList.compose-lookup j'
          (SplitMap.map (split-map-list m) s t fs)
          (SplitMap.map (split-map-list n) r s gs) k)
    map-lookup {xs = any xs} {ys = any ys} {zs = any zs} _ _ _ _ _ _
      with Vec.map-maybe (SplitBase.base a) xs
      | inspect (Vec.map-maybe (SplitBase.base a)) xs
      | Vec.map-maybe (SplitBase.base b) ys
      | inspect (Vec.map-maybe (SplitBase.base b)) ys
      | Vec.map-maybe (SplitBase.base c) zs
      | inspect (Vec.map-maybe (SplitBase.base c)) zs
    map-lookup {xs = any xs} {ys = any ys} {zs = any zs} refl refl refl fs gs k'
      | just _ | [ r ] | just _ | [ s ] | just _ | [ t ]
      with ArrowList.Arrow.lookup gs k'
    ... | nothing
      = ArrowList.nothing
    ... | just (l' , g)
      with ArrowList.Arrow.lookup fs l'
    ... | nothing
      = ArrowList.nothing
    ... | just (m' , f)
      = ArrowList.just m' (SplitCompose.map q r' s' t' f g)
      where
        r' = Vec.lookup-map-just (SplitBase.base a) xs r k'
        s' = Vec.lookup-map-just (SplitBase.base b) ys s l'
        t' = Vec.lookup-map-just (SplitBase.base c) zs t m'

    map
      : {xs : Object'.Object (object-list X)}
      → {ys : Object'.Object (object-list Y)}
      → {zs : Object'.Object (object-list Z)}
      → {xs' : Object'.Object (object-list X')}
      → {ys' : Object'.Object (object-list Y')}
      → {zs' : Object'.Object (object-list Z')}
      → (r : SplitBase.base (split-base-list a) xs ≡ just xs')
      → (s : SplitBase.base (split-base-list b) ys ≡ just ys')
      → (t : SplitBase.base (split-base-list c) zs ≡ just zs')
      → (fs : Arrow'.Arrow (arrow-list F) ys zs)
      → (gs : Arrow'.Arrow (arrow-list G) xs ys)
      → Arrow'.ArrowEqual (arrow-list H')
        (SplitMap.map (split-map-list o) r t
          (Compose.compose (compose-list j) fs gs))
        (Compose.compose (compose-list j')
          (SplitMap.map (split-map-list m) s t fs)
          (SplitMap.map (split-map-list n) r s gs))
    map r s t fs gs
      = record
      { lookup
        = map-lookup r s t fs gs
      }

    unmap-lookup
      : {xs : Object'.Object (object-list X')}
      → {ys : Object'.Object (object-list Y')}
      → {zs : Object'.Object (object-list Z')}
      → (fs : Arrow'.Arrow (arrow-list F') ys zs)
      → (gs : Arrow'.Arrow (arrow-list G') xs ys)
      → (k : Fin (List.length xs))
      → ArrowList.LookupEqual H
        (SplitBase.unbase (split-base-list a) xs)
        (SplitBase.unbase (split-base-list c) zs) k
        (SplitMapList.unmap-lookup o
          (Compose.compose (compose-list j') fs gs) k)
        (ComposeList.compose-lookup j
          (SplitMapList.unmap m fs)
          (SplitMapList.unmap n gs) k)
    unmap-lookup {xs = any xs} {ys = any ys} {zs = any zs} fs gs k'
      with ArrowList.Arrow.lookup gs k'
    ... | nothing
      = ArrowList.nothing
    ... | just (l' , g)
      with ArrowList.Arrow.lookup fs l'
    ... | nothing
      = ArrowList.nothing
    ... | just (m' , f)
      = ArrowList.just m'
      $ Arrow'.arrow-equal' H
      $ Arrow'.arrow-trans' H (Arrow'.arrow-refl'' H r t)
      $ Arrow'.arrow-trans' H (SplitCompose.unmap' q f g)
      $ Arrow'.arrow-sym' H (ComposeEqual.compose-equal' p
        (Arrow'.arrow-refl'' F s t)
        (Arrow'.arrow-refl'' G r s))
      where
        r = Vec.lookup-map (SplitBase.unbase a) xs k'
        s = Vec.lookup-map (SplitBase.unbase b) ys l'
        t = Vec.lookup-map (SplitBase.unbase c) zs m'

    unmap
      : {xs : Object'.Object (object-list X')}
      → {ys : Object'.Object (object-list Y')}
      → {zs : Object'.Object (object-list Z')}
      → (fs : Arrow'.Arrow (arrow-list F') ys zs)
      → (gs : Arrow'.Arrow (arrow-list G') xs ys)
      → Arrow'.ArrowEqual (arrow-list H)
        (SplitMap.unmap (split-map-list o)
          (Compose.compose (compose-list j') fs gs))
        (Compose.compose (compose-list j)
          (SplitMap.unmap (split-map-list m) fs)
          (SplitMap.unmap (split-map-list n) gs))
    unmap fs gs
      = record
      { lookup
        = unmap-lookup fs gs
      }

  split-compose-list
    : ComposeEqual j
    → {a : SplitBase X X'}
    → {b : SplitBase Y Y'}
    → {c : SplitBase Z Z'}
    → {m : SplitMap F F' b c}
    → {n : SplitMap G G' a b}
    → {o : SplitMap H H' a c}
    → SplitCompose j j' m n o
    → SplitCompose
      (compose-list j)
      (compose-list j')
      (split-map-list m)
      (split-map-list n)
      (split-map-list o)
  split-compose-list p q
    = record {SplitComposeList p q}

-- ## Dependent

-- ### DependentSplitBase

dependent-split-base-list
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → DependentSplitBase X' X''
  → DependentSplitBase
    (dependent-object-list X')
    (dependent-object-list X'')
dependent-split-base-list {n = zero} a
  = split-base-list a
dependent-split-base-list {n = suc _} a
  = record
  { tail
    = λ x → dependent-split-base-list
      (DependentSplitBase.tail a x)
  }

-- ### DependentSplitMap

dependent-split-map-list
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : DependentArrow X' Y'}
  → {F' : DependentArrow X'' Y''}
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → DependentSplitMap F F' a b
  → DependentSplitMap
    (dependent-arrow-list F)
    (dependent-arrow-list F')
    (dependent-split-base-list a)
    (dependent-split-base-list b)
dependent-split-map-list {n = zero} m
  = split-map-list m
dependent-split-map-list {n = suc _} m
  = record
  { tail
    = λ x y → dependent-split-map-list
      (DependentSplitMap.tail m x y)
  }

-- ### DependentSplitIdentity

dependent-split-identity-list
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : DependentArrow X' X'}
  → {F' : DependentArrow X'' X''}
  → {i : DependentIdentity F}
  → {i' : DependentIdentity F'}
  → {a : DependentSplitBase X' X''}
  → {m : DependentSplitMap F F' a a}
  → DependentSplitIdentity i i' m
  → DependentSplitIdentity
    (dependent-identity-list i)
    (dependent-identity-list i')
    (dependent-split-map-list m)
dependent-split-identity-list {n = zero} p
  = split-identity-list p
dependent-split-identity-list {n = suc _} p
  = record
  { tail
    = λ x → dependent-split-identity-list
      (DependentSplitIdentity.tail p x)
  }

-- ### DependentSplitCompose

dependent-split-compose-list
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {Z' Z'' : DependentObject Z}
  → {F : DependentArrow Y' Z'}
  → {G : DependentArrow X' Y'}
  → {H : DependentArrow X' Z'}
  → {F' : DependentArrow Y'' Z''}
  → {G' : DependentArrow X'' Y''}
  → {H' : DependentArrow X'' Z''}
  → {j : DependentCompose F G H}
  → {j' : DependentCompose F' G' H'}
  → DependentComposeEqual j
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → {c : DependentSplitBase Z' Z''}
  → {m : DependentSplitMap F F' b c}
  → {n : DependentSplitMap G G' a b}
  → {o : DependentSplitMap H H' a c}
  → DependentSplitCompose j j' m n o
  → DependentSplitCompose
    (dependent-compose-list j)
    (dependent-compose-list j')
    (dependent-split-map-list m)
    (dependent-split-map-list n)
    (dependent-split-map-list o)
dependent-split-compose-list {n = zero} p q
  = split-compose-list p q
dependent-split-compose-list {n = suc _} p q
  = record
  { tail
    = λ x y z → dependent-split-compose-list
      (DependentComposeEqual.tail p x y z)
      (DependentSplitCompose.tail q x y z)
  }

