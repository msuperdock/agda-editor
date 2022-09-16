module Category.Lift.Sigma where

open import Category.Core
  using (Arrow'; ChainArrow; ChainCompose; ChainIdentity; ChainObject; Compose;
    DependentArrow; DependentArrow₁; DependentCompose; DependentCompose₁;
    DependentIdentity; DependentIdentity₁; DependentObject; DependentObject₁;
    Identity; Object')
open import Category.Core.Sigma
  using (module ArrowSigma; arrow-sigma; compose-sigma; dependent-arrow-sigma;
    dependent-compose-sigma; dependent-identity-sigma; identity-sigma;
    object-sigma)
open import Category.Core.Snoc
  using (chain-compose-snoc; chain-identity-snoc; chain-object-snoc)
open import Category.Lift
  using (ChainLift; ChainPath; DependentLift; DependentPath; DependentPath₁;
    DependentPathCompose; DependentPathCompose₁; DependentPathEqual;
    DependentPathEqual₁; DependentPathIdentity; DependentPathIdentity₁; Path;
    PathCompose; PathEqual; PathIdentity; tt)
open import Category.Lift.Snoc
  using (chain-lift-snoc; chain-path-snoc)
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
  {X₁ Y₁ : Object'}
  {X₂ : DependentObject₁ X₁}
  {Y₂ : DependentObject₁ Y₁}
  {F₁ : Arrow' X₁ Y₁}
  {F₂ : DependentArrow₁ X₂ Y₂}
  {p₁ : Path F₁}
  where

  module PathSigma
    (p₂ : DependentPath₁ F₂ p₁)
    where

    base
      : Object'.Object (object-sigma X₂)
      → Maybe (Object'.Object (object-sigma Y₂))
    base (x₁ , x₂)
      with Path.base p₁ x₁
      | inspect (Path.base p₁) x₁
    ... | nothing | _
      = nothing
    ... | just y₁ | [ p₁' ]
      with DependentPath₁.base p₂ p₁' x₂
    ... | nothing
      = nothing
    ... | just y₂
      = just (y₁ , y₂)

    map
      : (x : Object'.Object (object-sigma X₂))
      → {y : Object'.Object (object-sigma Y₂)}
      → base x ≡ just y
      → Arrow'.Arrow (arrow-sigma F₁ F₂) x y
    map (x₁ , x₂) _
      with Path.base p₁ x₁
      | inspect (Path.base p₁) x₁
    ... | just _ | [ p₁' ]
      with DependentPath₁.base p₂ p₁' x₂
      | inspect (DependentPath₁.base p₂ p₁') x₂
    map (x₁ , x₂) refl | _ | [ p₁' ] | just _ | [ p₂' ]
      = ArrowSigma.arrow₂
        (Path.map p₁ x₁ p₁')
        (DependentPath₁.map p₂ p₁' x₂ p₂')

  path-sigma
    : DependentPath₁ F₂ p₁
    → Path
      (arrow-sigma F₁ F₂)
  path-sigma p₂
    = record {PathSigma p₂}

-- ### PathEqual

module _
  {X₁ Y₁ : Object'}
  {X₂ : DependentObject₁ X₁}
  {Y₂ : DependentObject₁ Y₁}
  {F₁ : Arrow' X₁ Y₁}
  {F₂ : DependentArrow₁ X₂ Y₂}
  {p₁₁ p₂₁ : Path F₁}
  {p₁₂ : DependentPath₁ F₂ p₁₁}
  {p₂₂ : DependentPath₁ F₂ p₂₁}
  where

  module PathEqualSigma
    (q₁ : PathEqual p₁₁ p₂₁)
    (q₂ : DependentPathEqual₁ p₁₂ p₂₂)
    where

    base
      : (x : Object'.Object (object-sigma X₂))
      → Path.base (path-sigma p₁₂) x
        ≡ Path.base (path-sigma p₂₂) x
    base (x₁ , x₂)
      with Path.base p₁₁ x₁
      | inspect (Path.base p₁₁) x₁
      | Path.base p₂₁ x₁
      | inspect (Path.base p₂₁) x₁
      | PathEqual.base q₁ x₁
    ... | nothing | _ | _ | _ | refl
      = refl
    ... | just _ | [ p₁₁' ] | _ | [ p₂₁' ] | refl
      with DependentPath₁.base p₁₂ p₁₁' x₂
      | DependentPath₁.base p₂₂ p₂₁' x₂
      | DependentPathEqual₁.base q₂ p₁₁' p₂₁' x₂
    ... | nothing | _ | refl
      = refl
    ... | just _ | _ | refl
      = refl

    map
      : (x : Object'.Object (object-sigma X₂))
      → {y : Object'.Object (object-sigma Y₂)}
      → (p₁' : Path.base (path-sigma p₁₂) x ≡ just y)
      → (p₂' : Path.base (path-sigma p₂₂) x ≡ just y)
      → Arrow'.ArrowEqual (arrow-sigma F₁ F₂)
        (Path.map (path-sigma p₁₂) x p₁')
        (Path.map (path-sigma p₂₂) x p₂')
    map (x₁ , x₂) _ _
      with Path.base p₁₁ x₁
      | inspect (Path.base p₁₁) x₁
      | Path.base p₂₁ x₁
      | inspect (Path.base p₂₁) x₁
    ... | just _ | [ p₁₁' ] | just _ | [ p₂₁' ]
      with DependentPath₁.base p₁₂ p₁₁' x₂
      | inspect (DependentPath₁.base p₁₂ p₁₁') x₂
      | DependentPath₁.base p₂₂ p₂₁' x₂
      | inspect (DependentPath₁.base p₂₂ p₂₁') x₂
    map (x₁ , x₂) refl refl
      | _ | [ p₁₁' ] | _ | [ p₂₁' ]
      | just _ | [ p₁₂' ] | just _ | [ p₂₂' ]
      = ArrowSigma.arrow₂
        (PathEqual.map q₁ x₁ p₁₁' p₂₁')
        (DependentPathEqual₁.map q₂ p₁₁' p₂₁' x₂ p₁₂' p₂₂')

  path-equal-sigma
    : PathEqual p₁₁ p₂₁
    → DependentPathEqual₁ p₁₂ p₂₂
    → PathEqual
      (path-sigma p₁₂)
      (path-sigma p₂₂)
  path-equal-sigma q₁ q₂
    = record {PathEqualSigma q₁ q₂}

-- ### PathIdentity

module _
  {X₁ : Object'}
  {X₂ : DependentObject₁ X₁}
  {F₁ : Arrow' X₁ X₁}
  {F₂ : DependentArrow₁ X₂ X₂}
  {i₁ : Identity F₁}
  {i₂ : DependentIdentity₁ F₂}
  {p₁ : Path F₁}
  {p₂ : DependentPath₁ F₂ p₁}
  where

  module PathIdentitySigma
    (q₁ : PathIdentity i₁ p₁)
    (q₂ : DependentPathIdentity₁ i₂ p₂)
    where

    base
      : (x : Object'.Object (object-sigma X₂))
      → Path.base (path-sigma p₂) x ≡ just x
    base (x₁ , x₂)
      with Path.base p₁ x₁
      | inspect (Path.base p₁) x₁
      | PathIdentity.base q₁ x₁
    ... | _ | [ p₁' ] | refl
      with DependentPath₁.base p₂ p₁' x₂
      | DependentPathIdentity₁.base q₂ p₁' x₂
    ... | _ | refl
      = refl

    map
      : {x : Object'.Object (object-sigma X₂)}
      → (p' : Path.base (path-sigma p₂) x ≡ just x)
      → Arrow'.ArrowEqual (arrow-sigma F₁ F₂)
        (Path.map (path-sigma p₂) x p')
        (Identity.identity (identity-sigma i₁ i₂) x)
    map {x = (x₁ , x₂)} _
      with Path.base p₁ x₁
      | inspect (Path.base p₁) x₁
      | PathIdentity.base q₁ x₁
    ... | _ | [ p₁' ] | refl
      with DependentPath₁.base p₂ p₁' x₂
      | inspect (DependentPath₁.base p₂ p₁') x₂
      | DependentPathIdentity₁.base q₂ p₁' x₂
    map refl | _ | [ p₁' ] | _ | _ | [ p₂' ] | refl
      = ArrowSigma.arrow₂
        (PathIdentity.map q₁ p₁')
        (DependentPathIdentity₁.map q₂ p₁' p₂')

  path-identity-sigma
    : PathIdentity i₁ p₁
    → DependentPathIdentity₁ i₂ p₂
    → PathIdentity
      (identity-sigma i₁ i₂)
      (path-sigma p₂)
  path-identity-sigma q₁ q₂
    = record {PathIdentitySigma q₁ q₂}

-- ### PathCompose

module _
  {X₁ Y₁ Z₁ : Object'}
  {X₂ : DependentObject₁ X₁}
  {Y₂ : DependentObject₁ Y₁}
  {Z₂ : DependentObject₁ Z₁}
  {F₁ : Arrow' Y₁ Z₁}
  {G₁ : Arrow' X₁ Y₁}
  {H₁ : Arrow' X₁ Z₁}
  {F₂ : DependentArrow₁ Y₂ Z₂}
  {G₂ : DependentArrow₁ X₂ Y₂}
  {H₂ : DependentArrow₁ X₂ Z₂}
  {j₁ : Compose F₁ G₁ H₁}
  {j₂ : DependentCompose₁ F₂ G₂ H₂}
  {p₁ : Path F₁}
  {q₁ : Path G₁}
  {r₁ : Path H₁}
  {p₂ : DependentPath₁ F₂ p₁}
  {q₂ : DependentPath₁ G₂ q₁}
  {r₂ : DependentPath₁ H₂ r₁}
  where

  module PathComposeSigma
    (s₁ : PathCompose j₁ p₁ q₁ r₁)
    (s₂ : DependentPathCompose₁ j₂ p₂ q₂ r₂)
    where

    base
      : (x : Object'.Object (object-sigma X₂))
      → {y : Object'.Object (object-sigma Y₂)}
      → Path.base (path-sigma q₂) x ≡ just y
      → Path.base (path-sigma r₂) x
        ≡ Path.base (path-sigma p₂) y
    base (x₁ , x₂) _
      with Path.base q₁ x₁
      | inspect (Path.base q₁) x₁
    ... | just _ | [ q₁' ]
      with DependentPath₁.base q₂ q₁' x₂
      | inspect (DependentPath₁.base q₂ q₁') x₂
    base (x₁ , x₂) refl | just y₁ | [ q₁' ] | just y₂ | [ q₂' ]
      with Path.base p₁ y₁
      | inspect (Path.base p₁) y₁
      | Path.base r₁ x₁
      | inspect (Path.base r₁) x₁
      | PathCompose.base s₁ x₁ q₁'
    ... | nothing | _ | _ | _ | refl
      = refl
    ... | just _ | [ p₁' ] | _ | [ r₁' ] | refl
      with DependentPath₁.base p₂ p₁' y₂
      | inspect (DependentPath₁.base p₂ p₁') y₂
      | DependentPath₁.base r₂ r₁' x₂
      | inspect (DependentPath₁.base r₂ r₁') x₂
      | DependentPathCompose₁.base s₂ p₁' q₁' r₁' x₂ q₂'
    ... | nothing | _ | _ | _ | refl
      = refl
    ... | just _ | _ | _ | _ | refl
      = refl

    map
      : (x : Object'.Object (object-sigma X₂))
      → {y : Object'.Object (object-sigma Y₂)}
      → {z : Object'.Object (object-sigma Z₂)}
      → (p' : Path.base (path-sigma p₂) y ≡ just z)
      → (q' : Path.base (path-sigma q₂) x ≡ just y)
      → (r' : Path.base (path-sigma r₂) x ≡ just z)
      → Arrow'.ArrowEqual (arrow-sigma H₁ H₂)
        (Path.map (path-sigma r₂) x r')
        (Compose.compose (compose-sigma j₁ j₂)
          (Path.map (path-sigma p₂) y p')
          (Path.map (path-sigma q₂) x q'))
    map (x₁ , x₂) {y = (y₁ , y₂)} _ _ _
      with Path.base p₁ y₁
      | inspect (Path.base p₁) y₁
      | Path.base q₁ x₁
      | inspect (Path.base q₁) x₁
      | Path.base r₁ x₁
      | inspect (Path.base r₁) x₁
    ... | just _ | [ p₁' ] | just _ | [ q₁' ] | just _ | [ r₁' ]
      with DependentPath₁.base p₂ p₁' y₂
      | inspect (DependentPath₁.base p₂ p₁') y₂
      | DependentPath₁.base q₂ q₁' x₂
      | inspect (DependentPath₁.base q₂ q₁') x₂
      | DependentPath₁.base r₂ r₁' x₂
      | inspect (DependentPath₁.base r₂ r₁') x₂
    map (x₁ , x₂) refl refl refl
      | _ | [ p₁' ] | _ | [ q₁' ] | _ | [ r₁' ]
      | just _ | [ p₂' ] | just _ | [ q₂' ] | just _ | [ r₂' ]
      = ArrowSigma.arrow₂
        (PathCompose.map s₁ x₁ p₁' q₁' r₁')
        (DependentPathCompose₁.map s₂ p₁' q₁' r₁' x₂ p₂' q₂' r₂')

  path-compose-sigma
    : PathCompose j₁ p₁ q₁ r₁
    → DependentPathCompose₁ j₂ p₂ q₂ r₂
    → PathCompose
      (compose-sigma j₁ j₂)
      (path-sigma p₂)
      (path-sigma q₂)
      (path-sigma r₂)
  path-compose-sigma s₁ s₂
    = record {PathComposeSigma s₁ s₂}

-- ## Dependent

-- ### DependentPath

dependent-path-sigma
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' : DependentObject X}
  → {Y₁' : DependentObject Y}
  → {X₂' : DependentObject (chain-object-snoc X₁')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁')}
  → {F : ChainArrow X Y}
  → {F₁' : DependentArrow X₁' Y₁'}
  → {F₂' : DependentArrow X₂' Y₂'}
  → {p : ChainPath F}
  → {p₁' : DependentPath F₁' p}
  → DependentPath F₂' (chain-path-snoc p₁')
  → DependentPath
    (dependent-arrow-sigma F₁' F₂') p
dependent-path-sigma {n = zero} p₂'
  = path-sigma p₂'
dependent-path-sigma {n = suc _} p₂'
  = record
  { tail
    = λ x p' → dependent-path-sigma
      (DependentPath.tail p₂' x p')
  }

-- ### DependentPathEqual

dependent-path-equal-sigma
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X₁' : DependentObject X}
  → {Y₁' : DependentObject Y}
  → {X₂' : DependentObject (chain-object-snoc X₁')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁')}
  → {F : ChainArrow X Y}
  → {F₁' : DependentArrow X₁' Y₁'}
  → {F₂' : DependentArrow X₂' Y₂'}
  → {p₁ p₂ : ChainPath F}
  → {p₁₁' : DependentPath F₁' p₁}
  → {p₂₁' : DependentPath F₁' p₂}
  → {p₁₂' : DependentPath F₂' (chain-path-snoc p₁₁')}
  → {p₂₂' : DependentPath F₂' (chain-path-snoc p₂₁')}
  → DependentPathEqual p₁₁' p₂₁'
  → DependentPathEqual p₁₂' p₂₂'
  → DependentPathEqual
    (dependent-path-sigma p₁₂')
    (dependent-path-sigma p₂₂')
dependent-path-equal-sigma {n = zero} q₁ q₂
  = path-equal-sigma q₁ q₂
dependent-path-equal-sigma {n = suc _} q₁ q₂
  = record
  { tail
    = λ x p₁'' p₂'' → dependent-path-equal-sigma
      (DependentPathEqual.tail q₁ x p₁'' p₂'')
      (DependentPathEqual.tail q₂ x p₁'' p₂'')
  }

-- ### DependentPathIdentity

dependent-path-identity-sigma
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' : DependentObject X}
  → {X₂' : DependentObject (chain-object-snoc X₁')}
  → {F : ChainArrow X X}
  → {F₁' : DependentArrow X₁' X₁'}
  → {F₂' : DependentArrow X₂' X₂'}
  → {i₁ : DependentIdentity F₁'}
  → {i₂ : DependentIdentity F₂'}
  → {p : ChainPath F}
  → {p₁' : DependentPath F₁' p}
  → {p₂' : DependentPath F₂' (chain-path-snoc p₁')}
  → DependentPathIdentity i₁ p₁'
  → DependentPathIdentity i₂ p₂'
  → DependentPathIdentity
    (dependent-identity-sigma i₁ i₂)
    (dependent-path-sigma p₂')
dependent-path-identity-sigma {n = zero} q₁ q₂
  = path-identity-sigma q₁ q₂
dependent-path-identity-sigma {n = suc _} q₁ q₂
  = record
  { tail
    = λ p' → dependent-path-identity-sigma
      (DependentPathIdentity.tail q₁ p')
      (DependentPathIdentity.tail q₂ p')
  }

-- ### DependentPathCompose

dependent-path-compose-sigma
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X₁' : DependentObject X}
  → {Y₁' : DependentObject Y}
  → {Z₁' : DependentObject Z}
  → {X₂' : DependentObject (chain-object-snoc X₁')}
  → {Y₂' : DependentObject (chain-object-snoc Y₁')}
  → {Z₂' : DependentObject (chain-object-snoc Z₁')}
  → {F : ChainArrow Y Z}
  → {G : ChainArrow X Y}
  → {H : ChainArrow X Z}
  → {F₁' : DependentArrow Y₁' Z₁'}
  → {G₁' : DependentArrow X₁' Y₁'}
  → {H₁' : DependentArrow X₁' Z₁'}
  → {F₂' : DependentArrow Y₂' Z₂'}
  → {G₂' : DependentArrow X₂' Y₂'}
  → {H₂' : DependentArrow X₂' Z₂'}
  → {j₁ : DependentCompose F₁' G₁' H₁'}
  → {j₂ : DependentCompose F₂' G₂' H₂'}
  → {p : ChainPath F}
  → {q : ChainPath G}
  → {r : ChainPath H}
  → {p₁' : DependentPath F₁' p}
  → {q₁' : DependentPath G₁' q}
  → {r₁' : DependentPath H₁' r}
  → {p₂' : DependentPath F₂' (chain-path-snoc p₁')}
  → {q₂' : DependentPath G₂' (chain-path-snoc q₁')}
  → {r₂' : DependentPath H₂' (chain-path-snoc r₁')}
  → DependentPathCompose j₁ p₁' q₁' r₁'
  → DependentPathCompose j₂ p₂' q₂' r₂'
  → DependentPathCompose
    (dependent-compose-sigma j₁ j₂)
    (dependent-path-sigma p₂')
    (dependent-path-sigma q₂')
    (dependent-path-sigma r₂')
dependent-path-compose-sigma {n = zero} s₁ s₂
  = path-compose-sigma s₁ s₂
dependent-path-compose-sigma {n = suc _} s₁ s₂
  = record
  { tail
    = λ x p' q' r' → dependent-path-compose-sigma
      (DependentPathCompose.tail s₁ x p' q' r')
      (DependentPathCompose.tail s₂ x p' q' r')
  }

-- ### DependentLift

dependent-lift-sigma
  : {n : ℕ}
  → {X : ChainObject n}
  → {X₁' : DependentObject X}
  → {X₂' : DependentObject (chain-object-snoc X₁')}
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
  → {l₁' : DependentLift i i₁' j j₁' l}
  → DependentLift
    (chain-identity-snoc i i₁') i₂'
    (chain-compose-snoc j j₁') j₂'
    (chain-lift-snoc l₁')
  → DependentLift i
    (dependent-identity-sigma i₁' i₂') j
    (dependent-compose-sigma j₁' j₂') l
dependent-lift-sigma {n = zero} _
  = tt
dependent-lift-sigma {n = suc _} {l₁' = l₁'} l₂'
  = record
  { path
    = λ f → dependent-path-sigma
      (DependentLift.path l₂' f)
  ; path-equal
    = λ p → dependent-path-equal-sigma
      (DependentLift.path-equal l₁' p)
      (DependentLift.path-equal l₂' p)
  ; path-identity
    = λ x → dependent-path-identity-sigma
      (DependentLift.path-identity l₁' x)
      (DependentLift.path-identity l₂' x)
  ; path-compose
    = λ f g → dependent-path-compose-sigma
      (DependentLift.path-compose l₁' f g)
      (DependentLift.path-compose l₂' f g)
  ; tail
    = λ x → dependent-lift-sigma
      (DependentLift.tail l₂' x)
  }

