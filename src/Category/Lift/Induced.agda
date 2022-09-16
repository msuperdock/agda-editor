module Category.Lift.Induced where

open import Category.Core
  using (Arrow'; ChainArrow; ChainCompose; ChainIdentity; ChainObject; Compose;
    ComposeEqual; DependentArrow; DependentCompose; DependentComposeEqual;
    DependentIdentity; DependentObject; Identity; Object')
open import Category.Core.Induced
  using (compose-equal-induced)
open import Category.Lift
  using (ChainLift; ChainPath; DependentLift; DependentPath;
    DependentPathCompose; DependentPathEqual; DependentPathIdentity;
    DependentPrelift; DependentPrelift'; Path; PathCompose; PathEqual;
    PathIdentity; tt)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitCompose; DependentSplitIdentity;
    DependentSplitMap; SplitBase; SplitCompose; SplitIdentity; SplitMap)
open import Category.Split.Lift
  using (DependentSplitPath; DependentSplitPath'; DependentSplitPrelift;
    DependentSplitPrelift'; SplitPath; SplitPath')
open import Category.State.Lift
  using (DependentStateLift; DependentStatePath; DependentStatePathEqual;
    DependentStatePathIdentity; StatePath; StatePathEqual; StatePathIdentity)
open import Data.Equal
  using (_≡_; refl; sub; sym; trans)
open import Data.Function
  using (_$_)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### PathEqual

module _
  {X Y X' Y' : Object'}
  {F : Arrow' X Y}
  {F' : Arrow' X' Y'}
  {p₁ p₂ : StatePath F}
  {p₁' p₂' : Path F'}
  where

  module PathEqualInduced
    (q : StatePathEqual p₁ p₂)
    {a : SplitBase X X'}
    {b : SplitBase Y Y'}
    {m : SplitMap F F' a b}
    (r₁ : SplitPath p₁ p₁' m)
    (r₂ : SplitPath p₂ p₂' m)
    where

    base
      : (x : Object'.Object X')
      → Path.base p₁' x
        ≡ Path.base p₂' x
    base x'
      = trans (sym (SplitPath.base r₁ x s))
      $ trans (sub (SplitBase.base b)
        (StatePathEqual.base q x))
      $ SplitPath.base r₂ x s
      where
        x = SplitBase.unbase a x'
        s = SplitBase.base-unbase a x'

    map
      : (x : Object'.Object X')
      → {y : Object'.Object Y'}
      → (p₁'' : Path.base p₁' x ≡ just y)
      → (p₂'' : Path.base p₂' x ≡ just y)
      → Arrow'.ArrowEqual F'
        (Path.map p₁' x p₁'')
        (Path.map p₂' x p₂'')
    map x' {y = y'} p₁'' p₂''
      = Arrow'.arrow-equal' F'
      $ Arrow'.arrow-trans' F' (Arrow'.arrow-sym' F'
        (SplitPath.map' r₁ x p₁'' s u₁))
      $ Arrow'.arrow-trans' F' (SplitMap.map-equal' m s s u₁ u₂
        (StatePathEqual.map q x))
      $ SplitPath.map' r₂ x p₂'' s u₂
      where
        x = SplitBase.unbase a x'
        s = SplitBase.base-unbase a x'
        t = SplitBase.base-unbase b y'
        u₁ = trans (sym (sub (SplitBase.base b)
          (SplitPath.unbase r₁ x' p₁''))) t
        u₂ = trans (sym (sub (SplitBase.base b)
          (SplitPath.unbase r₂ x' p₂''))) t

  path-equal-induced
    : StatePathEqual p₁ p₂
    → {a : SplitBase X X'}
    → {b : SplitBase Y Y'}
    → {m : SplitMap F F' a b}
    → SplitPath p₁ p₁' m
    → SplitPath p₂ p₂' m
    → PathEqual p₁' p₂'
  path-equal-induced q r₁ r₂
    = record {PathEqualInduced q r₁ r₂}

-- ### PathEqual'

module _
  {X Y X' Y' : Object'}
  {F : Arrow' X Y}
  {F' : Arrow' X' Y'}
  {p₁ p₂ : Path F}
  {p₁' p₂' : Path F'}
  where

  module PathEqualInduced'
    (q : PathEqual p₁ p₂)
    {a : SplitBase X X'}
    {b : SplitBase Y Y'}
    {m : SplitMap F F' a b}
    (r₁ : SplitPath' p₁ p₁' m)
    (r₂ : SplitPath' p₂ p₂' m)
    where

    base
      : (x : Object'.Object X')
      → Path.base p₁' x
        ≡ Path.base p₂' x
    base x'
      with Path.base p₁ (SplitBase.unbase a x')
      | inspect (Path.base p₁) (SplitBase.unbase a x')
      | Path.base p₂ (SplitBase.unbase a x')
      | inspect (Path.base p₂) (SplitBase.unbase a x')
      | PathEqual.base q (SplitBase.unbase a x')
    ... | nothing | [ p₁'' ] | _ | [ p₂'' ] | refl
      = trans (SplitPath'.base-nothing r₁ x p₁'' s)
      $ sym (SplitPath'.base-nothing r₂ x p₂'' s)
      where
        x = SplitBase.unbase a x'
        s = SplitBase.base-unbase a x'
        
    ... | just _ | [ p₁'' ] | _ | [ p₂'' ] | refl
      = trans (sym (SplitPath'.base-just r₁ x p₁'' s))
      $ SplitPath'.base-just r₂ x p₂'' s
      where
        x = SplitBase.unbase a x'
        s = SplitBase.base-unbase a x'

    map
      : (x : Object'.Object X')
      → {y : Object'.Object Y'}
      → (p₁'' : Path.base p₁' x ≡ just y)
      → (p₂'' : Path.base p₂' x ≡ just y)
      → Arrow'.ArrowEqual F'
        (Path.map p₁' x p₁'')
        (Path.map p₂' x p₂'')
    map x' {y = y'} p₁'' p₂''
      = Arrow'.arrow-trans F' (Arrow'.arrow-sym F'
        (SplitPath'.map r₁ x u₁ p₁'' s t))
      $ Arrow'.arrow-trans F' (SplitMap.map-equal m s t
        (PathEqual.map q x u₁ u₂))
      $ SplitPath'.map r₂ x u₂ p₂'' s t
      where
        x = SplitBase.unbase a x'
        s = SplitBase.base-unbase a x'
        t = SplitBase.base-unbase b y'
        u₁ = SplitPath'.unbase' r₁ x' p₁''
        u₂ = SplitPath'.unbase' r₂ x' p₂''

  path-equal-induced'
    : PathEqual p₁ p₂
    → {a : SplitBase X X'}
    → {b : SplitBase Y Y'}
    → {m : SplitMap F F' a b}
    → SplitPath' p₁ p₁' m
    → SplitPath' p₂ p₂' m
    → PathEqual p₁' p₂'
  path-equal-induced' q r₁ r₂
    = record {PathEqualInduced' q r₁ r₂}

-- ### PathIdentity

module _
  {X X' : Object'}
  {F : Arrow' X X}
  {F' : Arrow' X' X'}
  {i : Identity F}
  {i' : Identity F'}
  {p : StatePath F}
  {p' : Path F'}
  where

  module PathIdentityInduced
    (q : StatePathIdentity i p)
    {a : SplitBase X X'}
    {m : SplitMap F F' a a}
    (r : SplitIdentity i i' m)
    (s : SplitPath p p' m)
    where

    base'
      : (x : Object'.Object X')
      → SplitBase.base a
        (StatePath.base p
          (SplitBase.unbase a x))
      ≡ just x
    base' x
      = trans (sub (SplitBase.base a) (StatePathIdentity.base q
        (SplitBase.unbase a x)))
      $ SplitBase.base-unbase a x

    base
      : (x : Object'.Object X')
      → Path.base p' x ≡ just x
    base x
      = trans (sym (SplitPath.base s (SplitBase.unbase a x)
        (SplitBase.base-unbase a x)))
      $ base' x
        
    map
      : {x : Object'.Object X'}
      → (p'' : Path.base p' x ≡ just x)
      → Arrow'.ArrowEqual F'
        (Path.map p' x p'')
        (Identity.identity i' x)
    map {x = x'} p''
      = Arrow'.arrow-equal' F'
      $ Arrow'.arrow-trans' F' (Arrow'.arrow-sym' F'
        (SplitPath.map' s x p'' t u))
      $ Arrow'.arrow-trans' F' (SplitMap.map-equal' m t t u t
        (StatePathIdentity.map q x))
      $ SplitIdentity.map' r x t
      where
        x = SplitBase.unbase a x'
        t = SplitBase.base-unbase a x'
        u = base' x'

  path-identity-induced
    : StatePathIdentity i p
    → {a : SplitBase X X'}
    → {m : SplitMap F F' a a}
    → SplitIdentity i i' m
    → SplitPath p p' m
    → PathIdentity i' p'
  path-identity-induced q r s
    = record {PathIdentityInduced q r s}

-- ### PathIdentity'

module _
  {X X' : Object'}
  {F : Arrow' X X}
  {F' : Arrow' X' X'}
  {i : Identity F}
  {i' : Identity F'}
  {p : Path F}
  {p' : Path F'}
  where

  module PathIdentityInduced'
    (q : PathIdentity i p)
    {a : SplitBase X X'}
    {m : SplitMap F F' a a}
    (r : SplitIdentity i i' m)
    (s : SplitPath' p p' m)
    where

    base
      : (x : Object'.Object X')
      → Path.base p' x ≡ just x
    base x'
      = trans (sym (SplitPath'.base-just s
        (SplitBase.unbase a x')
        (PathIdentity.base q
          (SplitBase.unbase a x'))
        (SplitBase.base-unbase a x')))
      $ SplitBase.base-unbase a x'

    map
      : {x : Object'.Object X'}
      → (p'' : Path.base p' x ≡ just x)
      → Arrow'.ArrowEqual F'
        (Path.map p' x p'')
        (Identity.identity i' x)
    map {x = x'} p''
      = Arrow'.arrow-trans F' (Arrow'.arrow-sym F'
        (SplitPath'.map s x u p'' t t))
      $ Arrow'.arrow-trans F' (SplitMap.map-equal m t t
        (PathIdentity.map q u))
      $ SplitIdentity.map r x t
      where
        x = SplitBase.unbase a x'
        t = SplitBase.base-unbase a x'
        u = SplitPath'.unbase' s x' p''

  path-identity-induced'
    : PathIdentity i p
    → {a : SplitBase X X'}
    → {m : SplitMap F F' a a}
    → SplitIdentity i i' m
    → SplitPath' p p' m
    → PathIdentity i' p'
  path-identity-induced' q r s
    = record {PathIdentityInduced' q r s}

-- ### PathCompose'

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

  module PathComposeInduced'
    (j'' : ComposeEqual j)
    {p : Path F}
    {q : Path G}
    {r : Path H}
    {p' : Path F'}
    {q' : Path G'}
    {r' : Path H'}
    (s : PathCompose j p q r)
    {a : SplitBase X X'}
    {b : SplitBase Y Y'}
    {c : SplitBase Z Z'}
    {m : SplitMap F F' b c}
    {n : SplitMap G G' a b}
    {o : SplitMap H H' a c}
    (t : SplitCompose j j' m n o)
    (u : SplitPath' p p' m)
    (v : SplitPath' q q' n)
    (w : SplitPath' r r' o)
    where

    base
      : (x : Object'.Object X')
      → {y : Object'.Object Y'}
      → Path.base q' x ≡ just y
      → Path.base r' x
        ≡ Path.base p' y
    base x {y = y} q''
      with Path.base p (SplitBase.unbase b y)
      | inspect (Path.base p) (SplitBase.unbase b y)
    ... | nothing | [ p'' ]
      = trans (SplitPath'.base-nothing w
        (SplitBase.unbase a x)
        (trans (PathCompose.base s
          (SplitBase.unbase a x)
          (SplitPath'.unbase' v x q'')) p'')
        (SplitBase.base-unbase a x))
      $ sym (SplitPath'.base-nothing u
        (SplitBase.unbase b y) p''
        (SplitBase.base-unbase b y))
    ... | just _ | [ p'' ]
      = trans (sym (SplitPath'.base-just w
        (SplitBase.unbase a x)
        (trans (PathCompose.base s
          (SplitBase.unbase a x)
          (SplitPath'.unbase' v x q'')) p'')
          (SplitBase.base-unbase a x)))
      $ SplitPath'.base-just u
        (SplitBase.unbase b y) p''
        (SplitBase.base-unbase b y)

    map
      : (x : Object'.Object X')
      → {y : Object'.Object Y'}
      → {z : Object'.Object Z'}
      → (p'' : Path.base p' y ≡ just z)
      → (q'' : Path.base q' x ≡ just y)
      → (r'' : Path.base r' x ≡ just z)
      → Arrow'.ArrowEqual H'
        (Path.map r' x r'')
        (Compose.compose j'
          (Path.map p' y p'')
          (Path.map q' x q''))
    map x' {y = y'} {z = z'} p''' q''' r'''
      = Arrow'.arrow-trans H' (Arrow'.arrow-sym H'
        (SplitPath'.map w x r'' r''' a' c'))
      $ Arrow'.arrow-trans H' (SplitMap.map-equal o a' c'
        (PathCompose.map s x p'' q'' r''))
      $ Arrow'.arrow-trans H' (SplitCompose.map t a' b' c' f g)
      $ ComposeEqual.compose-equal (compose-equal-induced j'' t)
        (SplitPath'.map u y p'' p''' b' c')
        (SplitPath'.map v x q'' q''' a' b')
      where
        x = SplitBase.unbase a x'
        y = SplitBase.unbase b y'
        p'' = SplitPath'.unbase' u y' p'''
        q'' = SplitPath'.unbase' v x' q'''
        r'' = SplitPath'.unbase' w x' r'''
        f = Path.map p y p''
        g = Path.map q x q''
        a' = SplitBase.base-unbase a x'
        b' = SplitBase.base-unbase b y'
        c' = SplitBase.base-unbase c z'

  path-compose-induced'
    : ComposeEqual j
    → {p : Path F}
    → {q : Path G}
    → {r : Path H}
    → {p' : Path F'}
    → {q' : Path G'}
    → {r' : Path H'}
    → PathCompose j p q r
    → {a : SplitBase X X'}
    → {b : SplitBase Y Y'}
    → {c : SplitBase Z Z'}
    → {m : SplitMap F F' b c}
    → {n : SplitMap G G' a b}
    → {o : SplitMap H H' a c}
    → SplitCompose j j' m n o
    → SplitPath' p p' m
    → SplitPath' q q' n
    → SplitPath' r r' o
    → PathCompose j' p' q' r'
  path-compose-induced' j'' s t u v w
    = record {PathComposeInduced' j'' s t u v w}

-- ## Dependent

-- ### DependentPathEqual

dependent-path-equal-induced
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {F'' : DependentArrow X'' Y''}
  → {p₁ p₂ : ChainPath F}
  → {p₁' : DependentStatePath F' p₁}
  → {p₂' : DependentStatePath F' p₂}
  → {p₁'' : DependentPath F'' p₁}
  → {p₂'' : DependentPath F'' p₂}
  → DependentStatePathEqual p₁' p₂'
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → {m : DependentSplitMap F' F'' a b}
  → DependentSplitPath p₁' p₁'' m
  → DependentSplitPath p₂' p₂'' m
  → DependentPathEqual p₁'' p₂''
dependent-path-equal-induced {n = zero} q r₁ r₂
  = path-equal-induced q r₁ r₂
dependent-path-equal-induced {n = suc _} q r₁ r₂
  = record
  { tail
    = λ x p₁''' p₂''' → dependent-path-equal-induced
      (DependentStatePathEqual.tail q x p₁''' p₂''')
      (DependentSplitPath.tail r₁ x p₁''')
      (DependentSplitPath.tail r₂ x p₂''')
  }

-- ### DependentPathEqual'

dependent-path-equal-induced'
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {F'' : DependentArrow X'' Y''}
  → {p₁ p₂ : ChainPath F}
  → {p₁' : DependentPath F' p₁}
  → {p₂' : DependentPath F' p₂}
  → {p₁'' : DependentPath F'' p₁}
  → {p₂'' : DependentPath F'' p₂}
  → DependentPathEqual p₁' p₂'
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → {m : DependentSplitMap F' F'' a b}
  → DependentSplitPath' p₁' p₁'' m
  → DependentSplitPath' p₂' p₂'' m
  → DependentPathEqual p₁'' p₂''
dependent-path-equal-induced' {n = zero} q r₁ r₂
  = path-equal-induced' q r₁ r₂
dependent-path-equal-induced' {n = suc _} q r₁ r₂
  = record
  { tail
    = λ x p₁''' p₂''' → dependent-path-equal-induced'
      (DependentPathEqual.tail q x p₁''' p₂''')
      (DependentSplitPath'.tail r₁ x p₁''')
      (DependentSplitPath'.tail r₂ x p₂''')
  }

-- ### DependentPathIdentity

dependent-path-identity-induced
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {F'' : DependentArrow X'' X''}
  → {i : DependentIdentity F'}
  → {i' : DependentIdentity F''}
  → {p : ChainPath F}
  → {p' : DependentStatePath F' p}
  → {p'' : DependentPath F'' p}
  → DependentStatePathIdentity i p'
  → {a : DependentSplitBase X' X''}
  → {m : DependentSplitMap F' F'' a a}
  → DependentSplitIdentity i i' m
  → DependentSplitPath p' p'' m
  → DependentPathIdentity i' p''
dependent-path-identity-induced {n = zero} q r s
  = path-identity-induced q r s
dependent-path-identity-induced {n = suc _} q r s
  = record
  { tail
    = λ {x} p'' → dependent-path-identity-induced
      (DependentStatePathIdentity.tail q p'')
      (DependentSplitIdentity.tail r x)
      (DependentSplitPath.tail s x p'')
  }

-- ### DependentPathIdentity'

dependent-path-identity-induced'
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {F'' : DependentArrow X'' X''}
  → {i : DependentIdentity F'}
  → {i' : DependentIdentity F''}
  → {p : ChainPath F}
  → {p' : DependentPath F' p}
  → {p'' : DependentPath F'' p}
  → DependentPathIdentity i p'
  → {a : DependentSplitBase X' X''}
  → {m : DependentSplitMap F' F'' a a}
  → DependentSplitIdentity i i' m
  → DependentSplitPath' p' p'' m
  → DependentPathIdentity i' p''
dependent-path-identity-induced' {n = zero} q r s
  = path-identity-induced' q r s
dependent-path-identity-induced' {n = suc _} q r s
  = record
  { tail
    = λ {x} p'' → dependent-path-identity-induced'
      (DependentPathIdentity.tail q p'')
      (DependentSplitIdentity.tail r x)
      (DependentSplitPath'.tail s x p'')
  }

-- ### DependentPathCompose'

dependent-path-compose-induced'
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {Z' Z'' : DependentObject Z}
  → {F : ChainArrow Y Z}
  → {G : ChainArrow X Y}
  → {H : ChainArrow X Z}
  → {F' : DependentArrow Y' Z'}
  → {G' : DependentArrow X' Y'}
  → {H' : DependentArrow X' Z'}
  → {F'' : DependentArrow Y'' Z''}
  → {G'' : DependentArrow X'' Y''}
  → {H'' : DependentArrow X'' Z''}
  → {j : DependentCompose F' G' H'}
  → {j' : DependentCompose F'' G'' H''}
  → DependentComposeEqual j
  → {p : ChainPath F}
  → {q : ChainPath G}
  → {r : ChainPath H}
  → {p' : DependentPath F' p}
  → {q' : DependentPath G' q}
  → {r' : DependentPath H' r}
  → {p'' : DependentPath F'' p}
  → {q'' : DependentPath G'' q}
  → {r'' : DependentPath H'' r}
  → DependentPathCompose j p' q' r'
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → {c : DependentSplitBase Z' Z''}
  → {m : DependentSplitMap F' F'' b c}
  → {n : DependentSplitMap G' G'' a b}
  → {o : DependentSplitMap H' H'' a c}
  → DependentSplitCompose j j' m n o
  → DependentSplitPath' p' p'' m
  → DependentSplitPath' q' q'' n
  → DependentSplitPath' r' r'' o
  → DependentPathCompose j' p'' q'' r''
dependent-path-compose-induced' {n = zero} j'' s t u v w
  = path-compose-induced' j'' s t u v w
dependent-path-compose-induced' {n = suc _} j'' s t u v w
  = record
  { tail
    = λ x {y} {z} p'' q'' r'' → dependent-path-compose-induced'
      (DependentComposeEqual.tail j'' x y z)
      (DependentPathCompose.tail s x p'' q'' r'')
      (DependentSplitCompose.tail t x y z)
      (DependentSplitPath'.tail u y p'')
      (DependentSplitPath'.tail v x q'')
      (DependentSplitPath'.tail w x r'')
  }

-- ### DependentLift

dependent-lift-induced
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {F'' : DependentArrow X'' X''}
  → {i : ChainIdentity F}
  → {i' : DependentIdentity F'}
  → {i'' : DependentIdentity F''}
  → {j : ChainCompose F F F}
  → {j'' : DependentCompose F'' F'' F''}
  → {l : ChainLift F}
  → {l' : DependentStateLift i i' l}
  → {l'' : DependentPrelift j j'' l}
  → {a : DependentSplitBase X' X''}
  → {m : DependentSplitMap F' F'' a a}
  → DependentSplitIdentity i' i'' m
  → DependentSplitPrelift l' l'' m
  → DependentLift i i'' j j'' l
dependent-lift-induced {n = zero} _ _
  = tt
dependent-lift-induced {n = suc _}
  {i = i} {l' = l'} {l'' = l''} p q
  = record
  { DependentPrelift l''
  ; path-equal
    = λ {_} {_} {f₁} {f₂} r → dependent-path-equal-induced
      (DependentStateLift.path-equal l' r)
      (DependentSplitPrelift.path q f₁)
      (DependentSplitPrelift.path q f₂)
  ; path-identity
    = λ x → dependent-path-identity-induced
      (DependentStateLift.path-identity l' x)
      (DependentSplitIdentity.tail p x)
      (DependentSplitPrelift.path q
        (ChainIdentity.identity i x))
  ; tail
    = λ x → dependent-lift-induced
      (DependentSplitIdentity.tail p x)
      (DependentSplitPrelift.tail q x)
  }

-- ### DependentLift'

dependent-lift-induced'
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {F'' : DependentArrow X'' X''}
  → {i : ChainIdentity F}
  → {i' : DependentIdentity F'}
  → {i'' : DependentIdentity F''}
  → {j : ChainCompose F F F}
  → {j' : DependentCompose F' F' F'}
  → {j'' : DependentCompose F'' F'' F''}
  → DependentComposeEqual j'
  → {l : ChainLift F}
  → {l' : DependentLift i i' j j' l}
  → {l'' : DependentPrelift' F'' l}
  → {a : DependentSplitBase X' X''}
  → {m : DependentSplitMap F' F'' a a}
  → DependentSplitIdentity i' i'' m
  → DependentSplitCompose j' j'' m m m
  → DependentSplitPrelift' l' l'' m
  → DependentLift i i'' j j'' l
dependent-lift-induced' {n = zero} _ _ _ _
  = tt
dependent-lift-induced' {n = suc _}
  {i = i} {j = j} p
  {l' = l'} {l'' = l''} q r s
  = record
  { DependentPrelift' l''
  ; path-equal
    = λ {_} {_} {f₁} {f₂} t → dependent-path-equal-induced'
      (DependentLift.path-equal l' t)
      (DependentSplitPrelift'.path s f₁)
      (DependentSplitPrelift'.path s f₂)
  ; path-identity
    = λ x → dependent-path-identity-induced'
      (DependentLift.path-identity l' x)
      (DependentSplitIdentity.tail q x)
      (DependentSplitPrelift'.path s
        (ChainIdentity.identity i x))
  ; path-compose
    = λ {x} {y} {z} f g → dependent-path-compose-induced'
      (DependentComposeEqual.tail p x y z)
      (DependentLift.path-compose l' f g)
      (DependentSplitCompose.tail r x y z)
      (DependentSplitPrelift'.path s f)
      (DependentSplitPrelift'.path s g)
      (DependentSplitPrelift'.path s
        (ChainCompose.compose j f g))
  ; tail
    = λ x → dependent-lift-induced'
      (DependentComposeEqual.tail p x x x)
      (DependentSplitIdentity.tail q x)
      (DependentSplitCompose.tail r x x x)
      (DependentSplitPrelift'.tail s x)
  }

