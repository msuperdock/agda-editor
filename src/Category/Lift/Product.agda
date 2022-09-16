module Category.Lift.Product where

open import Category.Core
  using (Arrow'; ChainArrow; ChainCompose; ChainIdentity; ChainObject; Compose;
    DependentArrow; DependentCompose; DependentIdentity; DependentObject;
    Identity; Object')
open import Category.Core.Product
  using (arrow-product; compose-product; dependent-arrow-product;
    dependent-compose-product; dependent-identity-product; identity-product;
    object-product)
open import Category.Lift
  using (ChainLift; ChainPath; DependentLift; DependentPath;
    DependentPathCompose; DependentPathEqual; DependentPathIdentity; Path;
    PathCompose; PathEqual; PathIdentity; tt)
open import Data.Equal
  using (_≡_; refl)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)
open import Data.Sigma
  using (_,_)

-- ## Base

-- ### Path

module _
  {X₁ X₂ Y₁ Y₂ : Object'}
  {F₁ : Arrow' X₁ Y₁}
  {F₂ : Arrow' X₂ Y₂}
  where

  module PathProduct
    (p₁ : Path F₁)
    (p₂ : Path F₂)
    where

    base
      : Object'.Object (object-product X₁ X₂)
      → Maybe (Object'.Object (object-product Y₁ Y₂))
    base (x₁ , x₂)
      with Path.base p₁ x₁
      | Path.base p₂ x₂
    ... | nothing | _
      = nothing
    ... | _ | nothing
      = nothing
    ... | just y₁ | just y₂
      = just (y₁ , y₂)

    map
      : (x : Object'.Object (object-product X₁ X₂))
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → base x ≡ just y
      → Arrow'.Arrow (arrow-product F₁ F₂) x y
    map (x₁ , x₂) _
      with Path.base p₁ x₁
      | inspect (Path.base p₁) x₁
      | Path.base p₂ x₂
      | inspect (Path.base p₂) x₂
    map (x₁ , x₂) refl | just _ | [ p₁' ] | just _ | [ p₂' ]
      = Path.map p₁ x₁ p₁'
      , Path.map p₂ x₂ p₂'

  path-product
    : Path F₁
    → Path F₂
    → Path
      (arrow-product F₁ F₂)
  path-product p₁ p₂
    = record {PathProduct p₁ p₂}

-- ### PathEqual

module _
  {X₁ X₂ Y₁ Y₂ : Object'}
  {F₁ : Arrow' X₁ Y₁}
  {F₂ : Arrow' X₂ Y₂}
  {p₁₁ p₂₁ : Path F₁}
  {p₁₂ p₂₂ : Path F₂}
  where

  module PathEqualProduct
    (q₁ : PathEqual p₁₁ p₂₁)
    (q₂ : PathEqual p₁₂ p₂₂)
    where

    base
      : (x : Object'.Object (object-product X₁ X₂))
      → Path.base (path-product p₁₁ p₁₂) x
        ≡ Path.base (path-product p₂₁ p₂₂) x
    base (x₁ , x₂)
      with Path.base p₁₁ x₁
      | Path.base p₂₁ x₁
      | PathEqual.base q₁ x₁
      | Path.base p₁₂ x₂
      | Path.base p₂₂ x₂
      | PathEqual.base q₂ x₂
    ... | _ | _ | refl | _ | _ | refl
      = refl

    map
      : (x : Object'.Object (object-product X₁ X₂))
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → (p₁' : Path.base (path-product p₁₁ p₁₂) x ≡ just y)
      → (p₂' : Path.base (path-product p₂₁ p₂₂) x ≡ just y)
      → Arrow'.ArrowEqual (arrow-product F₁ F₂)
        (Path.map (path-product p₁₁ p₁₂) x p₁')
        (Path.map (path-product p₂₁ p₂₂) x p₂')
    map (x₁ , x₂) _ _
      with Path.base p₁₁ x₁
      | inspect (Path.base p₁₁) x₁
      | Path.base p₁₂ x₂
      | inspect (Path.base p₁₂) x₂
      | Path.base p₂₁ x₁
      | inspect (Path.base p₂₁) x₁
      | Path.base p₂₂ x₂
      | inspect (Path.base p₂₂) x₂
    map (x₁ , x₂) refl refl
      | just _ | [ p₁₁' ] | just _ | [ p₁₂' ]
      | just _ | [ p₂₁' ] | just _ | [ p₂₂' ]
      = PathEqual.map q₁ x₁ p₁₁' p₂₁'
      , PathEqual.map q₂ x₂ p₁₂' p₂₂'

  path-equal-product
    : PathEqual p₁₁ p₂₁
    → PathEqual p₁₂ p₂₂
    → PathEqual
      (path-product p₁₁ p₁₂)
      (path-product p₂₁ p₂₂)
  path-equal-product q₁ q₂
    = record {PathEqualProduct q₁ q₂}

-- ### PathIdentity

module _
  {X₁ X₂ : Object'}
  {F₁ : Arrow' X₁ X₁}
  {F₂ : Arrow' X₂ X₂}
  {i₁ : Identity F₁}
  {i₂ : Identity F₂}
  {p₁ : Path F₁}
  {p₂ : Path F₂}
  where

  module PathIdentityProduct
    (q₁ : PathIdentity i₁ p₁)
    (q₂ : PathIdentity i₂ p₂)
    where

    base
      : (x : Object'.Object (object-product X₁ X₂))
      → Path.base (path-product p₁ p₂) x ≡ just x
    base (x₁ , x₂)
      with Path.base p₁ x₁
      | PathIdentity.base q₁ x₁
      | Path.base p₂ x₂
      | PathIdentity.base q₂ x₂
    ... | _ | refl | _ | refl
      = refl

    map
      : {x : Object'.Object (object-product X₁ X₂)}
      → (p' : Path.base (path-product p₁ p₂) x ≡ just x)
      → Arrow'.ArrowEqual (arrow-product F₁ F₂)
        (Path.map (path-product p₁ p₂) x p')
        (Identity.identity (identity-product i₁ i₂) x)
    map {x = (x₁ , x₂)} _
      with Path.base p₁ x₁
      | inspect (Path.base p₁) x₁
      | Path.base p₂ x₂
      | inspect (Path.base p₂) x₂
    map refl | just _ | [ p₁' ] | just _ | [ p₂' ]
      = PathIdentity.map q₁ p₁'
      , PathIdentity.map q₂ p₂'

  path-identity-product
    : PathIdentity i₁ p₁
    → PathIdentity i₂ p₂
    → PathIdentity
      (identity-product i₁ i₂)
      (path-product p₁ p₂)
  path-identity-product q₁ q₂
    = record {PathIdentityProduct q₁ q₂}

-- ### PathCompose

module _
  {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Object'}
  {F₁ : Arrow' Y₁ Z₁}
  {F₂ : Arrow' Y₂ Z₂}
  {G₁ : Arrow' X₁ Y₁}
  {G₂ : Arrow' X₂ Y₂}
  {H₁ : Arrow' X₁ Z₁}
  {H₂ : Arrow' X₂ Z₂}
  {j₁ : Compose F₁ G₁ H₁}
  {j₂ : Compose F₂ G₂ H₂}
  {p₁ : Path F₁}
  {p₂ : Path F₂}
  {q₁ : Path G₁}
  {q₂ : Path G₂}
  {r₁ : Path H₁}
  {r₂ : Path H₂}
  where

  module PathComposeProduct
    (s₁ : PathCompose j₁ p₁ q₁ r₁)
    (s₂ : PathCompose j₂ p₂ q₂ r₂)
    where

    base
      : (x : Object'.Object (object-product X₁ X₂))
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → Path.base (path-product q₁ q₂) x ≡ just y
      → Path.base (path-product r₁ r₂) x
        ≡ Path.base (path-product p₁ p₂) y
    base (x₁ , x₂) _
      with Path.base q₁ x₁
      | inspect (Path.base q₁) x₁
      | Path.base q₂ x₂
      | inspect (Path.base q₂) x₂
    base (x₁ , x₂) refl
      | just y₁ | [ q₁' ] | just y₂ | [ q₂' ]
      with Path.base r₁ x₁
      | Path.base p₁ y₁
      | PathCompose.base s₁ x₁ q₁'
      | Path.base r₂ x₂
      | Path.base p₂ y₂
      | PathCompose.base s₂ x₂ q₂'
    ... | nothing | _ | refl | _ | _ | refl
      = refl
    ... | just _ | _ | refl | nothing | _ | refl
      = refl
    ... | just _ | _ | refl | just _ | _ | refl
      = refl

    map
      : (x : Object'.Object (object-product X₁ X₂))
      → {y : Object'.Object (object-product Y₁ Y₂)}
      → {z : Object'.Object (object-product Z₁ Z₂)}
      → (p' : Path.base (path-product p₁ p₂) y ≡ just z)
      → (q' : Path.base (path-product q₁ q₂) x ≡ just y)
      → (r' : Path.base (path-product r₁ r₂) x ≡ just z)
      → Arrow'.ArrowEqual (arrow-product H₁ H₂)
        (Path.map (path-product r₁ r₂) x r')
        (Compose.compose (compose-product j₁ j₂)
          (Path.map (path-product p₁ p₂) y p')
          (Path.map (path-product q₁ q₂) x q'))
    map (x₁ , x₂) _ _ _
      with Path.base q₁ x₁
      | inspect (Path.base q₁) x₁
      | Path.base q₂ x₂
      | inspect (Path.base q₂) x₂
    map (x₁ , x₂) _ refl _
      | just y₁ | _ | just y₂ | _
      with Path.base r₁ x₁
      | inspect (Path.base r₁) x₁
      | Path.base r₂ x₂
      | inspect (Path.base r₂) x₂
      | Path.base p₁ y₁
      | inspect (Path.base p₁) y₁
      | Path.base p₂ y₂
      | inspect (Path.base p₂) y₂
    map (x₁ , x₂) refl _ refl
      | _ | [ q₁' ] | _ | [ q₂' ]
      | just _ | [ r₁' ] | just _ | [ r₂' ]
      | just _ | [ p₁' ] | just _ | [ p₂' ]
      = PathCompose.map s₁ x₁ p₁' q₁' r₁'
      , PathCompose.map s₂ x₂ p₂' q₂' r₂'

  path-compose-product
    : PathCompose j₁ p₁ q₁ r₁
    → PathCompose j₂ p₂ q₂ r₂
    → PathCompose
      (compose-product j₁ j₂)
      (path-product p₁ p₂)
      (path-product q₁ q₂)
      (path-product r₁ r₂)
  path-compose-product s₁ s₂
    = record {PathComposeProduct s₁ s₂}

-- ## Dependent

-- ### DependentPath

dependent-path-product
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {Y₁' Y₂' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F₁' : DependentArrow X₁' Y₁'}
  → {F₂' : DependentArrow X₂' Y₂'}
  → {p : ChainPath F}
  → DependentPath F₁' p
  → DependentPath F₂' p
  → DependentPath
    (dependent-arrow-product F₁' F₂') p
dependent-path-product {n = zero} p₁' p₂'
  = path-product p₁' p₂'
dependent-path-product {n = suc _} p₁' p₂'
  = record
  { tail
    = λ x p' → dependent-path-product
      (DependentPath.tail p₁' x p')
      (DependentPath.tail p₂' x p')
  }

-- ### DependentPathEqual

dependent-path-equal-product
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {Y₁' Y₂' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F₁' : DependentArrow X₁' Y₁'}
  → {F₂' : DependentArrow X₂' Y₂'}
  → {p₁ p₂ : ChainPath F}
  → {p₁₁' : DependentPath F₁' p₁}
  → {p₂₁' : DependentPath F₁' p₂}
  → {p₁₂' : DependentPath F₂' p₁}
  → {p₂₂' : DependentPath F₂' p₂}
  → DependentPathEqual p₁₁' p₂₁'
  → DependentPathEqual p₁₂' p₂₂'
  → DependentPathEqual
    (dependent-path-product p₁₁' p₁₂')
    (dependent-path-product p₂₁' p₂₂')
dependent-path-equal-product {n = zero} q₁ q₂
  = path-equal-product q₁ q₂
dependent-path-equal-product {n = suc _} q₁ q₂
  = record
  { tail
    = λ x p₁'' p₂'' → dependent-path-equal-product
      (DependentPathEqual.tail q₁ x p₁'' p₂'')
      (DependentPathEqual.tail q₂ x p₁'' p₂'')
  }

-- ### DependentPathIdentity

dependent-path-identity-product
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {F : ChainArrow X X}
  → {F₁' : DependentArrow X₁' X₁'}
  → {F₂' : DependentArrow X₂' X₂'}
  → {i₁ : DependentIdentity F₁'}
  → {i₂ : DependentIdentity F₂'}
  → {p : ChainPath F}
  → {p₁' : DependentPath F₁' p}
  → {p₂' : DependentPath F₂' p}
  → DependentPathIdentity i₁ p₁'
  → DependentPathIdentity i₂ p₂'
  → DependentPathIdentity
    (dependent-identity-product i₁ i₂)
    (dependent-path-product p₁' p₂')
dependent-path-identity-product {n = zero} q₁ q₂
  = path-identity-product q₁ q₂
dependent-path-identity-product {n = suc _} q₁ q₂
  = record
  { tail
    = λ p' → dependent-path-identity-product
      (DependentPathIdentity.tail q₁ p')
      (DependentPathIdentity.tail q₂ p')
  }

-- ### DependentPathCompose

dependent-path-compose-product
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {Y₁' Y₂' : DependentObject Y}
  → {Z₁' Z₂' : DependentObject Z}
  → {F : ChainArrow Y Z}
  → {G : ChainArrow X Y}
  → {H : ChainArrow X Z}
  → {F₁' : DependentArrow Y₁' Z₁'}
  → {F₂' : DependentArrow Y₂' Z₂'}
  → {G₁' : DependentArrow X₁' Y₁'}
  → {G₂' : DependentArrow X₂' Y₂'}
  → {H₁' : DependentArrow X₁' Z₁'}
  → {H₂' : DependentArrow X₂' Z₂'}
  → {j₁ : DependentCompose F₁' G₁' H₁'}
  → {j₂ : DependentCompose F₂' G₂' H₂'}
  → {p : ChainPath F}
  → {q : ChainPath G}
  → {r : ChainPath H}
  → {p₁' : DependentPath F₁' p}
  → {p₂' : DependentPath F₂' p}
  → {q₁' : DependentPath G₁' q}
  → {q₂' : DependentPath G₂' q}
  → {r₁' : DependentPath H₁' r}
  → {r₂' : DependentPath H₂' r}
  → DependentPathCompose j₁ p₁' q₁' r₁'
  → DependentPathCompose j₂ p₂' q₂' r₂'
  → DependentPathCompose
    (dependent-compose-product j₁ j₂)
    (dependent-path-product p₁' p₂')
    (dependent-path-product q₁' q₂')
    (dependent-path-product r₁' r₂')
dependent-path-compose-product {n = zero} s₁ s₂
  = path-compose-product s₁ s₂
dependent-path-compose-product {n = suc _} s₁ s₂
  = record
  { tail
    = λ x p' q' r' → dependent-path-compose-product
      (DependentPathCompose.tail s₁ x p' q' r')
      (DependentPathCompose.tail s₂ x p' q' r')
  }

-- ### DependentLift

dependent-lift-product
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' X₂' : DependentObject X}
  → {F : ChainArrow X X}
  → {F₁' : DependentArrow X₁' X₁'}
  → {F₂' : DependentArrow X₂' X₂'}
  → {i : ChainIdentity F}
  → {i₁' : DependentIdentity F₁'}
  → {i₂' : DependentIdentity F₂'}
  → {j : ChainCompose F F F}
  → {j₁' : DependentCompose F₁' F₁' F₁'}
  → {j₂' : DependentCompose F₂' F₂' F₂'}
  → {l : ChainLift F}
  → DependentLift i i₁' j j₁' l
  → DependentLift i i₂' j j₂' l
  → DependentLift i
    (dependent-identity-product i₁' i₂') j
    (dependent-compose-product j₁' j₂') l
dependent-lift-product {n = zero} _ _
  = tt
dependent-lift-product {n = suc _} l₁' l₂'
  = record
  { path
    = λ f → dependent-path-product
      (DependentLift.path l₁' f)
      (DependentLift.path l₂' f)
  ; path-equal
    = λ p → dependent-path-equal-product
      (DependentLift.path-equal l₁' p)
      (DependentLift.path-equal l₂' p)
  ; path-identity
    = λ x → dependent-path-identity-product
      (DependentLift.path-identity l₁' x)
      (DependentLift.path-identity l₂' x)
  ; path-compose
    = λ f g → dependent-path-compose-product
      (DependentLift.path-compose l₁' f g)
      (DependentLift.path-compose l₂' f g)
  ; tail
    = λ x → dependent-lift-product
      (DependentLift.tail l₁' x)
      (DependentLift.tail l₂' x)
  }

