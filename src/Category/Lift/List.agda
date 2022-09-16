module Category.Lift.List where

open import Category.Core
  using (Arrow'; ChainArrow; ChainCompose; ChainIdentity; ChainObject; Compose;
    DependentArrow; DependentCompose; DependentIdentity; DependentObject;
    Identity; Object')
open import Category.Core.List
  using (module ArrowList; module ComposeList; module IdentityList; arrow-list;
    compose-list; dependent-arrow-list; dependent-compose-list;
    dependent-identity-list; identity-list; object-list)
open import Category.Lift
  using (ChainLift; ChainPath; DependentLift; DependentPath;
    DependentPathCompose; DependentPathEqual; DependentPathIdentity; Path;
    PathCompose; PathEqual; PathIdentity; tt)
open import Data.Any
  using (any)
open import Data.Equal
  using (_≡_; refl)
open import Data.Fin
  using (Fin)
open import Data.Function
  using (_$_)
open import Data.Inspect
  using ([_]; inspect)
open import Data.List
  using (List; _!_)
open import Data.Maybe
  using (Maybe; just)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (Σ; _,_)
open import Data.Vec
  using (Vec)

-- ## Base

-- ### Path

module _
  {X Y : Object'}
  {F : Arrow' X Y}
  where

  module PathList
    (p : Path F)
    where

    base
      : Object'.Object (object-list X)
      → Maybe (Object'.Object (object-list Y))
    base
      = List.map-maybe
        (Path.base p)

    map-lookup
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → base xs ≡ just ys
      → (k : Fin (List.length xs))
      → Maybe (l ∈ Fin (List.length ys)
        × Arrow'.Arrow F (xs ! k) (ys ! l))
    map-lookup (any xs) _ _
      with Vec.map-maybe (Path.base p) xs
      | inspect (Vec.map-maybe (Path.base p)) xs
    map-lookup (any xs) refl k | just _ | [ q ]
      = just (k , Path.map p x p')
      where
        x = Vec.lookup xs k
        p' = Vec.lookup-map-just (Path.base p) xs q k

    map-lookup-equal
      : {n : ℕ}
      → (xs : Vec (Object'.Object X) n)
      → {ys : Vec (Object'.Object Y) n}
      → (q : base (any xs) ≡ just (any ys))
      → (k : Fin n)
      → map-lookup (any xs) q k
      ≡ just (k , Path.map p (any xs ! k)
        (List.lookup-map-just (Path.base p) xs q k))
    map-lookup-equal xs _ _
      with Vec.map-maybe (Path.base p) xs
      | inspect (Vec.map-maybe (Path.base p)) xs
    map-lookup-equal _ refl _ | just _ | _
      = refl

    map-injective
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → (q : base xs ≡ just ys)
      → (k₁ k₂ : Fin (List.length xs))
      → {l : Fin (List.length ys)}
      → {f₁ : Arrow'.Arrow F (xs ! k₁) (ys ! l)}
      → {f₂ : Arrow'.Arrow F (xs ! k₂) (ys ! l)}
      → map-lookup xs q k₁ ≡ just (l , f₁)
      → map-lookup xs q k₂ ≡ just (l , f₂)
      → k₁ ≡ k₂
    map-injective (any xs) _ _ _ _ _
      with Vec.map-maybe (Path.base p) xs
      | inspect (Vec.map-maybe (Path.base p)) xs
    map-injective _ refl _ _ refl refl | just _ | _
      = refl

    map
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → base xs ≡ just ys
      → Arrow'.Arrow (arrow-list F) xs ys
    map xs q
      = record
      { lookup
        = map-lookup xs q
      ; injective
        = map-injective xs q
      }

  path-list
    : Path F
    → Path
      (arrow-list F)
  path-list p
    = record {PathList p}

-- ### PathEqual

module _
  {X Y : Object'}
  {F : Arrow' X Y}
  {p₁ p₂ : Path F}
  where

  module PathEqualList
    (q : PathEqual p₁ p₂)
    where

    base
      : (xs : Object'.Object (object-list X))
      → Path.base (path-list p₁) xs
        ≡ Path.base (path-list p₂) xs
    base
      = List.map-maybe-equal
        (Path.base p₁)
        (Path.base p₂)
        (PathEqual.base q)

    map-lookup
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → (p₁' : Path.base (path-list p₁) xs ≡ just ys)
      → (p₂' : Path.base (path-list p₂) xs ≡ just ys)
      → (k : Fin (List.length xs))
      → ArrowList.LookupEqual F xs ys k
        (PathList.map-lookup p₁ xs p₁' k)
        (PathList.map-lookup p₂ xs p₂' k)
    map-lookup (any xs) _ _ _
      with Vec.map-maybe (Path.base p₁) xs
      | inspect (Vec.map-maybe (Path.base p₁)) xs
      | Vec.map-maybe (Path.base p₂) xs
      | inspect (Vec.map-maybe (Path.base p₂)) xs
    map-lookup (any xs) refl refl k
      | just _ | [ p₁' ] | just _ | [ p₂' ]
      = ArrowList.just k
      $ PathEqual.map q
        (Vec.lookup xs k)
        (Vec.lookup-map-just (Path.base p₁) xs p₁' k)
        (Vec.lookup-map-just (Path.base p₂) xs p₂' k)

    map
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → (p₁' : Path.base (path-list p₁) xs ≡ just ys)
      → (p₂' : Path.base (path-list p₂) xs ≡ just ys)
      → Arrow'.ArrowEqual (arrow-list F)
        (Path.map (path-list p₁) xs p₁')
        (Path.map (path-list p₂) xs p₂')
    map xs p₁' p₂'
      = record
      { lookup
        = map-lookup xs p₁' p₂'
      }

  path-equal-list
    : PathEqual p₁ p₂
    → PathEqual
      (path-list p₁)
      (path-list p₂)
  path-equal-list q
    = record {PathEqualList q}

-- ### PathIdentity

module _
  {X : Object'}
  {F : Arrow' X X}
  {i : Identity F}
  {p : Path F}
  where

  module PathIdentityList
    (q : PathIdentity i p)
    where

    base
      : (xs : Object'.Object (object-list X))
      → Path.base (path-list p) xs ≡ just xs
    base
      = List.map-maybe-identity
        (Path.base p)
        (PathIdentity.base q)

    map-lookup
      : {xs : Object'.Object (object-list X)}
      → (p' : Path.base (path-list p) xs ≡ just xs)
      → (k : Fin (List.length xs))
      → ArrowList.LookupEqual F xs xs k
        (PathList.map-lookup p xs p' k)
        (IdentityList.identity-lookup i xs k)
    map-lookup {xs = any xs} _ _
      with Vec.map-maybe (Path.base p) xs
      | inspect (Vec.map-maybe (Path.base p)) xs
    map-lookup {xs = any xs} refl k
      | just _ | [ p' ]
      = ArrowList.just k
      $ PathIdentity.map q
        (Vec.lookup-map-just (Path.base p) xs p' k)

    map
      : {xs : Object'.Object (object-list X)}
      → (p' : Path.base (path-list p) xs ≡ just xs)
      → Arrow'.ArrowEqual (arrow-list F)
        (Path.map (path-list p) xs p')
        (Identity.identity (identity-list i) xs)
    map p'
      = record
      { lookup
        = map-lookup p'
      }

  path-identity-list
    : PathIdentity i p
    → PathIdentity
      (identity-list i)
      (path-list p)
  path-identity-list q
    = record {PathIdentityList q}

-- ### PathCompose

module _
  {X Y Z : Object'}
  {F : Arrow' Y Z}
  {G : Arrow' X Y}
  {H : Arrow' X Z}
  {j : Compose F G H}
  {p : Path F}
  {q : Path G}
  {r : Path H}
  where

  module PathComposeList
    (s : PathCompose j p q r)
    where

    base
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → Path.base (path-list q) xs ≡ just ys
      → Path.base (path-list r) xs
        ≡ Path.base (path-list p) ys
    base
      = List.map-maybe-compose
        (Path.base p)
        (Path.base q)
        (Path.base r)
        (PathCompose.base s)

    map-lookup
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → {zs : Object'.Object (object-list Z)}
      → (p' : Path.base (path-list p) ys ≡ just zs)
      → (q' : Path.base (path-list q) xs ≡ just ys)
      → (r' : Path.base (path-list r) xs ≡ just zs)
      → (k : Fin (List.length xs))
      → ArrowList.LookupEqual H xs zs k
        (PathList.map-lookup r xs r' k)
        (ComposeList.compose-lookup j
          (Path.map (path-list p) ys p')
          (Path.map (path-list q) xs q') k)
    map-lookup (any xs) {ys = any ys} _ _ _ _
      with Vec.map-maybe (Path.base p) ys
      | inspect (Vec.map-maybe (Path.base p)) ys
      | Vec.map-maybe (Path.base q) xs
      | inspect (Vec.map-maybe (Path.base q)) xs
      | Vec.map-maybe (Path.base r) xs
      | inspect (Vec.map-maybe (Path.base r)) xs
    map-lookup (any xs) {ys = any ys} refl refl refl k
      | just _ | [ p' ] | just _ | [ q' ] | just _ | [ r' ]
      = ArrowList.just k
      $ PathCompose.map s
        (Vec.lookup xs k)
        (Vec.lookup-map-just (Path.base p) ys p' k)
        (Vec.lookup-map-just (Path.base q) xs q' k)
        (Vec.lookup-map-just (Path.base r) xs r' k)

    map
      : (xs : Object'.Object (object-list X))
      → {ys : Object'.Object (object-list Y)}
      → {zs : Object'.Object (object-list Z)}
      → (p' : Path.base (path-list p) ys ≡ just zs)
      → (q' : Path.base (path-list q) xs ≡ just ys)
      → (r' : Path.base (path-list r) xs ≡ just zs)
      → Arrow'.ArrowEqual (arrow-list H)
        (Path.map (path-list r) xs r')
        (Compose.compose (compose-list j)
          (Path.map (path-list p) ys p')
          (Path.map (path-list q) xs q'))
    map xs p' q' r'
      = record
      { lookup
        = map-lookup xs p' q' r'
      }

  path-compose-list
    : PathCompose j p q r
    → PathCompose
      (compose-list j)
      (path-list p)
      (path-list q)
      (path-list r)
  path-compose-list s
    = record {PathComposeList s}

-- ## Dependent

-- ### DependentPath

dependent-path-list
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {p : ChainPath F}
  → DependentPath F' p
  → DependentPath
    (dependent-arrow-list F') p
dependent-path-list {n = zero} p'
  = path-list p'
dependent-path-list {n = suc _} p'
  = record
  { tail
    = λ x p'' → dependent-path-list
      (DependentPath.tail p' x p'')
  }

-- ### DependentPathEqual

dependent-path-equal-list
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {p₁ p₂ : ChainPath F}
  → {p₁' : DependentPath F' p₁}
  → {p₂' : DependentPath F' p₂}
  → DependentPathEqual p₁' p₂'
  → DependentPathEqual
    (dependent-path-list p₁')
    (dependent-path-list p₂')
dependent-path-equal-list {n = zero} q
  = path-equal-list q
dependent-path-equal-list {n = suc _} q
  = record
  { tail
    = λ x p₁'' p₂'' → dependent-path-equal-list
      (DependentPathEqual.tail q x p₁'' p₂'')
  }

-- ### DependentPathIdentity

dependent-path-identity-list
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {i : DependentIdentity F'}
  → {p : ChainPath F}
  → {p' : DependentPath F' p}
  → DependentPathIdentity i p'
  → DependentPathIdentity
    (dependent-identity-list i)
    (dependent-path-list p')
dependent-path-identity-list {n = zero} q
  = path-identity-list q
dependent-path-identity-list {n = suc _} q
  = record
  { tail
    = λ p'' → dependent-path-identity-list
      (DependentPathIdentity.tail q p'')
  }

-- ### DependentPathCompose

dependent-path-compose-list
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → {Z' : DependentObject Z}
  → {F : ChainArrow Y Z}
  → {G : ChainArrow X Y}
  → {H : ChainArrow X Z}
  → {F' : DependentArrow Y' Z'}
  → {G' : DependentArrow X' Y'}
  → {H' : DependentArrow X' Z'}
  → {j : DependentCompose F' G' H'}
  → {p : ChainPath F}
  → {q : ChainPath G}
  → {r : ChainPath H}
  → {p' : DependentPath F' p}
  → {q' : DependentPath G' q}
  → {r' : DependentPath H' r}
  → DependentPathCompose j p' q' r'
  → DependentPathCompose
    (dependent-compose-list j)
    (dependent-path-list p')
    (dependent-path-list q')
    (dependent-path-list r')
dependent-path-compose-list {n = zero} s
  = path-compose-list s
dependent-path-compose-list {n = suc _} s
  = record
  { tail
    = λ x p'' q'' r'' → dependent-path-compose-list
      (DependentPathCompose.tail s x p'' q'' r'')
  }

-- ### DependentLift

dependent-lift-list
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {i : ChainIdentity F}
  → {i' : DependentIdentity F'}
  → {j : ChainCompose F F F}
  → {j' : DependentCompose F' F' F'}
  → {l : ChainLift F}
  → DependentLift i i' j j' l
  → DependentLift i
    (dependent-identity-list i') j
    (dependent-compose-list j') l
dependent-lift-list {n = zero} _
  = tt
dependent-lift-list {n = suc _} l'
  = record
  { path
    = λ f → dependent-path-list
      (DependentLift.path l' f)
  ; path-equal
    = λ p → dependent-path-equal-list
      (DependentLift.path-equal l' p)
  ; path-identity
    = λ x → dependent-path-identity-list
      (DependentLift.path-identity l' x)
  ; path-compose
    = λ f g → dependent-path-compose-list
      (DependentLift.path-compose l' f g)
  ; tail
    = λ x → dependent-lift-list
      (DependentLift.tail l' x)
  }

