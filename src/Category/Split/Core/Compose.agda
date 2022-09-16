module Category.Split.Core.Compose where

open import Category.Core
  using (Arrow'; ChainObject; Compose; ComposeEqual; DependentArrow;
    DependentCompose; DependentComposeEqual; DependentIdentity; DependentObject;
    DependentPrecompose; Identity; Object'; Precompose)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitCompose; DependentSplitIdentity;
    DependentSplitMap; SplitBase; SplitCompose; SplitIdentity; SplitMap)
open import Data.Equal
  using (_≡_; refl)
open import Data.Function
  using (_$_; _∘_)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### SplitBase

module _
  {X X' X'' : Object'}
  where

  module SplitBaseCompose
    (a' : SplitBase X' X'')
    (a : SplitBase X X')
    where

    base
      : Object'.Object X
      → Maybe (Object'.Object X'')
    base x
      with SplitBase.base a x
    ... | nothing
      = nothing
    ... | just x'
      = SplitBase.base a' x'

    unbase
      : Object'.Object X''
      → Object'.Object X
    unbase
      = SplitBase.unbase a
      ∘ SplitBase.unbase a'

    base-unbase
      : (x : Object'.Object X'')
      → base (unbase x) ≡ just x
    base-unbase x
      with SplitBase.base a (SplitBase.unbase a (SplitBase.unbase a' x))
      | SplitBase.base-unbase a (SplitBase.unbase a' x)
    ... | _ | refl
      = SplitBase.base-unbase a' x

  split-base-compose
    : SplitBase X' X''
    → SplitBase X X'
    → SplitBase X X''
  split-base-compose a' a
    = record {SplitBaseCompose a' a}

-- ### SplitMap

module _
  {X Y X' Y' X'' Y'' : Object'}
  {F : Arrow' X Y}
  {F' : Arrow' X' Y'}
  {F'' : Arrow' X'' Y''}
  {a' : SplitBase X' X''}
  {b' : SplitBase Y' Y''}
  {a : SplitBase X X'}
  {b : SplitBase Y Y'}
  where

  module SplitMapCompose
    (m' : SplitMap F' F'' a' b')
    (m : SplitMap F F' a b)
    where

    map
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → {x' : Object'.Object X''}
      → {y' : Object'.Object Y''}
      → SplitBase.base (split-base-compose a' a) x ≡ just x'
      → SplitBase.base (split-base-compose b' b) y ≡ just y'
      → Arrow'.Arrow F x y
      → Arrow'.Arrow F'' x' y'
    map {x = x} {y = y} p' q'
      with SplitBase.base a x
      | inspect (SplitBase.base a) x
      | SplitBase.base b y
      | inspect (SplitBase.base b) y
    ... | just _ | [ p ] | just _ | [ q ]
      = SplitMap.map m' p' q'
      ∘ SplitMap.map m p q

    map-equal
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → {x' : Object'.Object X''}
      → {y' : Object'.Object Y''}
      → {f₁ f₂ : Arrow'.Arrow F x y}
      → (p : SplitBase.base (split-base-compose a' a) x ≡ just x')
      → (q : SplitBase.base (split-base-compose b' b) y ≡ just y')
      → Arrow'.ArrowEqual F f₁ f₂
      → Arrow'.ArrowEqual F'' (map p q f₁) (map p q f₂)
    map-equal {x = x} {y = y} p' q'
      with SplitBase.base a x
      | inspect (SplitBase.base a) x
      | SplitBase.base b y
      | inspect (SplitBase.base b) y
    ... | just _ | [ p ] | just _ | [ q ]
      = SplitMap.map-equal m' p' q'
      ∘ SplitMap.map-equal m p q

    unmap
      : {x : Object'.Object X''}
      → {y : Object'.Object Y''}
      → Arrow'.Arrow F'' x y
      → Arrow'.Arrow F
        (SplitBase.unbase (split-base-compose a' a) x)
        (SplitBase.unbase (split-base-compose b' b) y)
    unmap
      = SplitMap.unmap m
      ∘ SplitMap.unmap m'

    unmap-equal
      : {x : Object'.Object X''}
      → {y : Object'.Object Y''}
      → {f₁ f₂ : Arrow'.Arrow F'' x y}
      → Arrow'.ArrowEqual F'' f₁ f₂
      → Arrow'.ArrowEqual F (unmap f₁) (unmap f₂)
    unmap-equal
      = SplitMap.unmap-equal m
      ∘ SplitMap.unmap-equal m'

    map-unmap
      : {x : Object'.Object X''}
      → {y : Object'.Object Y''}
      → (p : SplitBase.base (split-base-compose a' a)
        (SplitBase.unbase (split-base-compose a' a) x)
        ≡ just x)
      → (q : SplitBase.base (split-base-compose b' b)
        (SplitBase.unbase (split-base-compose b' b) y)
        ≡ just y)
      → (f : Arrow'.Arrow F'' x y)
      → Arrow'.ArrowEqual F'' (map p q (unmap f)) f
    map-unmap {x = x} {y = y} p' q' f
      with SplitBase.base a (SplitBase.unbase a (SplitBase.unbase a' x))
      | inspect (SplitBase.base a) (SplitBase.unbase a (SplitBase.unbase a' x))
      | SplitBase.base-unbase a (SplitBase.unbase a' x)
      | SplitBase.base b (SplitBase.unbase b (SplitBase.unbase b' y))
      | inspect (SplitBase.base b) (SplitBase.unbase b (SplitBase.unbase b' y))
      | SplitBase.base-unbase b (SplitBase.unbase b' y)
    ... | just _ | [ p ] | refl | just _ | [ q ] | refl
      = Arrow'.arrow-trans F'' (SplitMap.map-equal m' p' q'
        (SplitMap.map-unmap m p q (SplitMap.unmap m' f)))
      $ SplitMap.map-unmap m' p' q' f

  split-map-compose
    : SplitMap F' F'' a' b'
    → SplitMap F F' a b
    → SplitMap F F''
      (split-base-compose a' a)
      (split-base-compose b' b)
  split-map-compose m' m
    = record {SplitMapCompose m' m}

-- ### SplitIdentity

module _
  {X X' X'' : Object'}
  {F : Arrow' X X}
  {F' : Arrow' X' X'}
  {F'' : Arrow' X'' X''}
  {i : Identity F}
  {i' : Identity F'}
  {i'' : Identity F''}
  {j : Compose F F F}
  {j' : Compose F' F' F'}
  where

  module SplitIdentityCompose
    (p : ComposeEqual j')
    (q : Precompose i' j')
    {a' : SplitBase X' X''}
    {a : SplitBase X X'}
    {m' : SplitMap F' F'' a' a'}
    {m : SplitMap F F' a a}
    (r' : SplitIdentity i' i'' m')
    (r : SplitIdentity i i' m)
    (s : SplitCompose j j' m m m)
    where

    map
      : (x : Object'.Object X)
      → {x' : Object'.Object X''}
      → (t : SplitBase.base (split-base-compose a' a) x ≡ just x')
      → Arrow'.ArrowEqual F''
        (SplitMap.map (split-map-compose m' m) t t
          (Identity.identity i x))
        (Identity.identity i'' x')
    map x t'
      with SplitBase.base a x
      | inspect (SplitBase.base a) x
    ... | just x' | [ t ]
      = Arrow'.arrow-trans F'' (SplitMap.map-equal m' t' t'
        (SplitIdentity.map r x t))
      $ SplitIdentity.map r' x' t'

    unmap
      : (x : Object'.Object X'')
      → Arrow'.ArrowEqual F
        (SplitMap.unmap (split-map-compose m' m)
          (Identity.identity i'' x))
        (Identity.identity i
          (SplitBase.unbase (split-base-compose a' a) x))
    unmap x
      = Arrow'.arrow-trans F (SplitMap.unmap-equal m
        (SplitIdentity.unmap r' x))
      $ SplitIdentity.unmap r (SplitBase.unbase a' x)

    normalize-arrow
      : (x : Object'.Object X)
      → {x' : Object'.Object X''}
      → SplitBase.base (split-base-compose a' a) x ≡ just x'
      → Arrow'.Arrow F x
        (SplitBase.unbase (split-base-compose a' a) x')
    normalize-arrow x t'
      with SplitBase.base a x
      | inspect (SplitBase.base a) x
    ... | just x' | [ t ]
      = Compose.compose j (SplitMap.unmap m
        (SplitIdentity.normalize-arrow r' x' t'))
      $ SplitIdentity.normalize-arrow r x t

    normalize-valid
      : (x : Object'.Object X)
      → {x' : Object'.Object X''}
      → (t : SplitBase.base (split-base-compose a' a) x ≡ just x')
      → (u : SplitBase.base (split-base-compose a' a)
        (SplitBase.unbase (split-base-compose a' a) x')
        ≡ just x')
      → Arrow'.ArrowEqual F''
        (SplitMap.map (split-map-compose m' m) t u (normalize-arrow x t))
        (Identity.identity i'' x')
    normalize-valid x {x' = x''} t' v'
      with SplitBase.base a x
      | inspect (SplitBase.base a) x
      | SplitBase.base a (SplitBase.unbase a
        (SplitBase.unbase a' x''))
      | inspect (SplitBase.base a) (SplitBase.unbase a
        (SplitBase.unbase a' x''))
      | SplitBase.base-unbase a
        (SplitBase.unbase a' x'')
    ... | just x' | [ t ] | just _ | [ v ] | refl
      = Arrow'.arrow-trans F'' (SplitMap.map-equal m' t' v'
        (SplitCompose.map s t u v (SplitMap.unmap m f') f))
      $ Arrow'.arrow-trans F'' (SplitMap.map-equal m' t' v'
        (ComposeEqual.compose-equal p (SplitMap.map-unmap m u v f') w))
      $ Arrow'.arrow-trans F'' (SplitMap.map-equal m' t' v'
        (Precompose.precompose q f'))
      $ w'
      where
        u = SplitBase.base-unbase a x'
        f = SplitIdentity.normalize-arrow r x t
        f' = SplitIdentity.normalize-arrow r' x' t'
        w = SplitIdentity.normalize-valid r x t u
        w' = SplitIdentity.normalize-valid r' x' t' v'

  split-identity-compose
    : ComposeEqual j'
    → Precompose i' j'
    → {a' : SplitBase X' X''}
    → {a : SplitBase X X'}
    → {m' : SplitMap F' F'' a' a'}
    → {m : SplitMap F F' a a}
    → SplitIdentity i' i'' m'
    → SplitIdentity i i' m
    → SplitCompose j j' m m m
    → SplitIdentity i i''
      (split-map-compose m' m)
  split-identity-compose p q r' r s
    = record {SplitIdentityCompose p q r' r s}

-- ### SplitCompose

module _
  {X Y Z X' Y' Z' X'' Y'' Z'' : Object'}
  {F : Arrow' Y Z}
  {G : Arrow' X Y}
  {H : Arrow' X Z}
  {F' : Arrow' Y' Z'}
  {G' : Arrow' X' Y'}
  {H' : Arrow' X' Z'}
  {F'' : Arrow' Y'' Z''}
  {G'' : Arrow' X'' Y''}
  {H'' : Arrow' X'' Z''}
  {j : Compose F G H}
  {j' : Compose F' G' H'}
  {j'' : Compose F'' G'' H''}
  {a' : SplitBase X' X''}
  {b' : SplitBase Y' Y''}
  {c' : SplitBase Z' Z''}
  {a : SplitBase X X'}
  {b : SplitBase Y Y'}
  {c : SplitBase Z Z'}
  {m' : SplitMap F' F'' b' c'}
  {n' : SplitMap G' G'' a' b'}
  {o' : SplitMap H' H'' a' c'}
  {m : SplitMap F F' b c}
  {n : SplitMap G G' a b}
  {o : SplitMap H H' a c}
  where

  module SplitComposeCompose
    (p' : SplitCompose j' j'' m' n' o')
    (p : SplitCompose j j' m n o)
    where

    map
      : {x : Object'.Object X}
      → {y : Object'.Object Y}
      → {z : Object'.Object Z}
      → {x' : Object'.Object X''}
      → {y' : Object'.Object Y''}
      → {z' : Object'.Object Z''}
      → (q : SplitBase.base (split-base-compose a' a) x ≡ just x')
      → (r : SplitBase.base (split-base-compose b' b) y ≡ just y')
      → (s : SplitBase.base (split-base-compose c' c) z ≡ just z')
      → (f : Arrow'.Arrow F y z)
      → (g : Arrow'.Arrow G x y)
      → Arrow'.ArrowEqual H''
        (SplitMap.map (split-map-compose o' o) q s
          (Compose.compose j f g))
        (Compose.compose j''
          (SplitMap.map (split-map-compose m' m) r s f)
          (SplitMap.map (split-map-compose n' n) q r g))
    map {x = x} {y = y} {z = z} q' r' s' f g
      with SplitBase.base a x
      | inspect (SplitBase.base a) x
      | SplitBase.base b y
      | inspect (SplitBase.base b) y
      | SplitBase.base c z
      | inspect (SplitBase.base c) z
    ... | just _ | [ q ] | just _ | [ r ] | just _ | [ s ]
      = Arrow'.arrow-trans H'' (SplitMap.map-equal o' q' s'
        (SplitCompose.map p q r s f g))
      $ SplitCompose.map p' q' r' s' f' g'
      where
        f' = SplitMap.map m r s f
        g' = SplitMap.map n q r g

    unmap
      : {x : Object'.Object X''}
      → {y : Object'.Object Y''}
      → {z : Object'.Object Z''}
      → (f : Arrow'.Arrow F'' y z)
      → (g : Arrow'.Arrow G'' x y)
      → Arrow'.ArrowEqual H
        (SplitMap.unmap (split-map-compose o' o)
          (Compose.compose j'' f g))
        (Compose.compose j
          (SplitMap.unmap (split-map-compose m' m) f)
          (SplitMap.unmap (split-map-compose n' n) g))
    unmap f' g'
      = Arrow'.arrow-trans H (SplitMap.unmap-equal o
        (SplitCompose.unmap p' f' g'))
      $ SplitCompose.unmap p f g
      where
        f = SplitMap.unmap m' f'
        g = SplitMap.unmap n' g'

  split-compose-compose
    : SplitCompose j' j'' m' n' o'
    → SplitCompose j j' m n o
    → SplitCompose j j''
      (split-map-compose m' m)
      (split-map-compose n' n)
      (split-map-compose o' o)
  split-compose-compose p' p
    = record {SplitComposeCompose p' p}

-- ## Dependent

-- ### DependentSplitBase

dependent-split-base-compose
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' X''' : DependentObject X}
  → DependentSplitBase X'' X'''
  → DependentSplitBase X' X''
  → DependentSplitBase X' X'''
dependent-split-base-compose {n = zero} a' a
  = split-base-compose a' a
dependent-split-base-compose {n = suc _} a' a
  = record
  { tail
    = λ x → dependent-split-base-compose
      (DependentSplitBase.tail a' x)
      (DependentSplitBase.tail a x)
  }

-- ### DependentSplitMap

dependent-split-map-compose
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' X''' : DependentObject X}
  → {Y' Y'' Y''' : DependentObject Y}
  → {F : DependentArrow X' Y'}
  → {F' : DependentArrow X'' Y''}
  → {F'' : DependentArrow X''' Y'''}
  → {a' : DependentSplitBase X'' X'''}
  → {b' : DependentSplitBase Y'' Y'''}
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → DependentSplitMap F' F'' a' b'
  → DependentSplitMap F F' a b
  → DependentSplitMap F F''
    (dependent-split-base-compose a' a)
    (dependent-split-base-compose b' b)
dependent-split-map-compose {n = zero} m' m
  = split-map-compose m' m
dependent-split-map-compose {n = suc _} m' m
  = record
  { tail
    = λ x y → dependent-split-map-compose
      (DependentSplitMap.tail m' x y)
      (DependentSplitMap.tail m x y)
  }

-- ### DependentSplitIdentity

dependent-split-identity-compose
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' X''' : DependentObject X}
  → {F : DependentArrow X' X'}
  → {F' : DependentArrow X'' X''}
  → {F'' : DependentArrow X''' X'''}
  → {i : DependentIdentity F}
  → {i' : DependentIdentity F'}
  → {i'' : DependentIdentity F''}
  → {j : DependentCompose F F F}
  → {j' : DependentCompose F' F' F'}
  → DependentComposeEqual j'
  → DependentPrecompose i' j'
  → {a' : DependentSplitBase X'' X'''}
  → {a : DependentSplitBase X' X''}
  → {m' : DependentSplitMap F' F'' a' a'}
  → {m : DependentSplitMap F F' a a}
  → DependentSplitIdentity i' i'' m'
  → DependentSplitIdentity i i' m
  → DependentSplitCompose j j' m m m
  → DependentSplitIdentity i i''
    (dependent-split-map-compose m' m)
dependent-split-identity-compose {n = zero} p q r' r s
  = split-identity-compose p q r' r s
dependent-split-identity-compose {n = suc _} p q r' r s
  = record
  { tail
    = λ x → dependent-split-identity-compose
      (DependentComposeEqual.tail p x x x)
      (DependentPrecompose.tail q x x)
      (DependentSplitIdentity.tail r' x)
      (DependentSplitIdentity.tail r x)
      (DependentSplitCompose.tail s x x x)
  }

-- ### DependentSplitCompose

dependent-split-compose-compose
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' X'' X''' : DependentObject X}
  → {Y' Y'' Y''' : DependentObject Y}
  → {Z' Z'' Z''' : DependentObject Z}
  → {F : DependentArrow Y' Z'}
  → {G : DependentArrow X' Y'}
  → {H : DependentArrow X' Z'}
  → {F' : DependentArrow Y'' Z''}
  → {G' : DependentArrow X'' Y''}
  → {H' : DependentArrow X'' Z''}
  → {F'' : DependentArrow Y''' Z'''}
  → {G'' : DependentArrow X''' Y'''}
  → {H'' : DependentArrow X''' Z'''}
  → {j : DependentCompose F G H}
  → {j' : DependentCompose F' G' H'}
  → {j'' : DependentCompose F'' G'' H''}
  → {a' : DependentSplitBase X'' X'''}
  → {b' : DependentSplitBase Y'' Y'''}
  → {c' : DependentSplitBase Z'' Z'''}
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → {c : DependentSplitBase Z' Z''}
  → {m' : DependentSplitMap F' F'' b' c'}
  → {n' : DependentSplitMap G' G'' a' b'}
  → {o' : DependentSplitMap H' H'' a' c'}
  → {m : DependentSplitMap F F' b c}
  → {n : DependentSplitMap G G' a b}
  → {o : DependentSplitMap H H' a c}
  → DependentSplitCompose j' j'' m' n' o'
  → DependentSplitCompose j j' m n o
  → DependentSplitCompose j j''
    (dependent-split-map-compose m' m)
    (dependent-split-map-compose n' n)
    (dependent-split-map-compose o' o)
dependent-split-compose-compose {n = zero} p' p
  = split-compose-compose p' p
dependent-split-compose-compose {n = suc _} p' p
  = record
  { tail
    = λ x y z → dependent-split-compose-compose
      (DependentSplitCompose.tail p' x y z)
      (DependentSplitCompose.tail p x y z)
  }

