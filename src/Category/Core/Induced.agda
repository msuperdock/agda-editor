module Category.Core.Induced where

open import Category.Core
  using (Arrow'; Associative; ChainObject; Compose; ComposeEqual;
    DependentArrow; DependentAssociative; DependentCompose;
    DependentComposeEqual; DependentIdentity; DependentObject;
    DependentPostcompose; DependentPrecompose; Identity; Object'; Postcompose;
    Precompose)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitCompose; DependentSplitIdentity;
    DependentSplitMap; SplitBase; SplitCompose; SplitIdentity; SplitMap)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### ComposeEqual

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

  module ComposeEqualInduced
    (p : ComposeEqual j)
    {a : SplitBase X X'}
    {b : SplitBase Y Y'}
    {c : SplitBase Z Z'}
    {m : SplitMap F F' b c}
    {n : SplitMap G G' a b}
    {o : SplitMap H H' a c}
    (q : SplitCompose j j' m n o)
    where

    compose-equal
      : {x : Object'.Object X'}
      → {y : Object'.Object Y'}
      → {z : Object'.Object Z'}
      → {f₁ f₂ : Arrow'.Arrow F' y z}
      → {g₁ g₂ : Arrow'.Arrow G' x y}
      → Arrow'.ArrowEqual F' f₁ f₂
      → Arrow'.ArrowEqual G' g₁ g₂
      → Arrow'.ArrowEqual H'
        (Compose.compose j' f₁ g₁)
        (Compose.compose j' f₂ g₂)
    compose-equal {x = x} {z = z} {f₁ = f₁} {f₂ = f₂} {g₁ = g₁} {g₂ = g₂} r' s'
      = Arrow'.arrow-trans H' (Arrow'.arrow-sym H'
        (SplitMap.map-unmap o t u (Compose.compose j' f₁ g₁)))
      $ Arrow'.arrow-trans H' (SplitMap.map-equal o t u
        (SplitCompose.unmap q f₁ g₁))
      $ Arrow'.arrow-trans H' (SplitMap.map-equal o t u
        (ComposeEqual.compose-equal p r s))
      $ Arrow'.arrow-trans H' (Arrow'.arrow-sym H' (SplitMap.map-equal o t u
        (SplitCompose.unmap q f₂ g₂)))
      $ SplitMap.map-unmap o t u (Compose.compose j' f₂ g₂)
      where
        r = SplitMap.unmap-equal m r'
        s = SplitMap.unmap-equal n s'
        t = SplitBase.base-unbase a x
        u = SplitBase.base-unbase c z

  compose-equal-induced
    : ComposeEqual j
    → {a : SplitBase X X'}
    → {b : SplitBase Y Y'}
    → {c : SplitBase Z Z'}
    → {m : SplitMap F F' b c}
    → {n : SplitMap G G' a b}
    → {o : SplitMap H H' a c}
    → SplitCompose j j' m n o
    → ComposeEqual j'
  compose-equal-induced p q
    = record {ComposeEqualInduced p q}

-- ### Precompose

module _
  {X Y X' Y' : Object'}
  {F : Arrow' X Y}
  {G : Arrow' X X}
  {F' : Arrow' X' Y'}
  {G' : Arrow' X' X'}
  {i : Identity G}
  {i' : Identity G'}
  {j : Compose F G F}
  {j' : Compose F' G' F'}
  where

  module PrecomposeInduced
    (p : ComposeEqual j)
    (q : Precompose i j)
    {a : SplitBase X X'}
    {b : SplitBase Y Y'}
    {m : SplitMap F F' a b}
    {n : SplitMap G G' a a}
    (r : SplitIdentity i i' n)
    (s : SplitCompose j j' m n m)
    where

    precompose
      : {x : Object'.Object X'}
      → {y : Object'.Object Y'}
      → (f : Arrow'.Arrow F' x y)
      → Arrow'.ArrowEqual F'
        (Compose.compose j' f
          (Identity.identity i' x)) f
    precompose {x = x} {y = y} f'
      = Arrow'.arrow-trans F' (Arrow'.arrow-sym F'
        (SplitMap.map-unmap m t u (Compose.compose j' f' g')))
      $ Arrow'.arrow-trans F' (SplitMap.map-equal m t u
        (SplitCompose.unmap s f' g'))
      $ Arrow'.arrow-trans F' (SplitMap.map-equal m t u
        (ComposeEqual.compose-equal₂ p (SplitIdentity.unmap r x)))
      $ Arrow'.arrow-trans F' (SplitMap.map-equal m t u
        (Precompose.precompose q f))
      $ SplitMap.map-unmap m t u f'
      where
        f = SplitMap.unmap m f'
        g' = Identity.identity i' x
        t = SplitBase.base-unbase a x
        u = SplitBase.base-unbase b y

  precompose-induced
    : ComposeEqual j
    → Precompose i j
    → {a : SplitBase X X'}
    → {b : SplitBase Y Y'}
    → {m : SplitMap F F' a b}
    → {n : SplitMap G G' a a}
    → SplitIdentity i i' n
    → SplitCompose j j' m n m
    → Precompose i' j'
  precompose-induced p q r s
    = record {PrecomposeInduced p q r s}

-- ### Postcompose

module _
  {X Y X' Y' : Object'}
  {F : Arrow' Y Y}
  {G : Arrow' X Y}
  {F' : Arrow' Y' Y'}
  {G' : Arrow' X' Y'}
  {i : Identity F}
  {i' : Identity F'}
  {j : Compose F G G}
  {j' : Compose F' G' G'}
  where

  module PostcomposeInduced
    (p : ComposeEqual j)
    (q : Postcompose i j)
    {a : SplitBase X X'}
    {b : SplitBase Y Y'}
    {m : SplitMap F F' b b}
    {n : SplitMap G G' a b}
    (r : SplitIdentity i i' m)
    (s : SplitCompose j j' m n n)
    where

    postcompose
      : {x : Object'.Object X'}
      → {y : Object'.Object Y'}
      → (g : Arrow'.Arrow G' x y)
      → Arrow'.ArrowEqual G'
        (Compose.compose j'
          (Identity.identity i' y) g) g
    postcompose {x = x} {y = y} g'
      = Arrow'.arrow-trans G' (Arrow'.arrow-sym G'
        (SplitMap.map-unmap n t u (Compose.compose j' f' g')))
      $ Arrow'.arrow-trans G' (SplitMap.map-equal n t u
        (SplitCompose.unmap s f' g'))
      $ Arrow'.arrow-trans G' (SplitMap.map-equal n t u
        (ComposeEqual.compose-equal₁ p (SplitIdentity.unmap r y)))
      $ Arrow'.arrow-trans G' (SplitMap.map-equal n t u
        (Postcompose.postcompose q g))
      $ SplitMap.map-unmap n t u g'
      where
        g = SplitMap.unmap n g'
        f' = Identity.identity i' y
        t = SplitBase.base-unbase a x
        u = SplitBase.base-unbase b y

  postcompose-induced
    : ComposeEqual j
    → Postcompose i j
    → {a : SplitBase X X'}
    → {b : SplitBase Y Y'}
    → {m : SplitMap F F' b b}
    → {n : SplitMap G G' a b}
    → SplitIdentity i i' m
    → SplitCompose j j' m n n
    → Postcompose i' j'
  postcompose-induced p q r s
    = record {PostcomposeInduced p q r s}

-- ### Associative

module _
  {W X Y Z W' X' Y' Z' : Object'}
  {F : Arrow' Y Z}
  {G : Arrow' X Y}
  {H : Arrow' W X}
  {I : Arrow' X Z}
  {J : Arrow' W Y}
  {K : Arrow' W Z}
  {F' : Arrow' Y' Z'}
  {G' : Arrow' X' Y'}
  {H' : Arrow' W' X'}
  {I' : Arrow' X' Z'}
  {J' : Arrow' W' Y'}
  {K' : Arrow' W' Z'}
  {j : Compose F G I}
  {k : Compose G H J}
  {l : Compose I H K}
  {m : Compose F J K}
  {j' : Compose F' G' I'}
  {k' : Compose G' H' J'}
  {l' : Compose I' H' K'}
  {m' : Compose F' J' K'}
  where

  module AssociativeInduced
    (p : ComposeEqual l)
    (q : ComposeEqual m)
    (r : Associative j k l m)
    {a : SplitBase W W'}
    {b : SplitBase X X'}
    {c : SplitBase Y Y'}
    {d : SplitBase Z Z'}
    {m'' : SplitMap F F' c d}
    {n'' : SplitMap G G' b c}
    {o'' : SplitMap H H' a b}
    {p'' : SplitMap I I' b d}
    {q'' : SplitMap J J' a c}
    {r'' : SplitMap K K' a d}
    (s : SplitCompose j j' m'' n'' p'')
    (t : SplitCompose k k' n'' o'' q'')
    (u : SplitCompose l l' p'' o'' r'')
    (v : SplitCompose m m' m'' q'' r'')
    where

    associative
      : {w : Object'.Object W'}
      → {x : Object'.Object X'}
      → {y : Object'.Object Y'}
      → {z : Object'.Object Z'}
      → (f : Arrow'.Arrow F' y z)
      → (g : Arrow'.Arrow G' x y)
      → (h : Arrow'.Arrow H' w x)
      → Arrow'.ArrowEqual K'
        (Compose.compose l'
          (Compose.compose j' f g) h)
        (Compose.compose m' f
          (Compose.compose k' g h))
    associative {w = w'} {z = z'} f' g' h'
      = Arrow'.arrow-trans K' (Arrow'.arrow-sym K'
        (SplitMap.map-unmap r'' w x (Compose.compose l' i'' h')))
      $ Arrow'.arrow-trans K' (SplitMap.map-equal r'' w x
        (SplitCompose.unmap u i'' h'))
      $ Arrow'.arrow-trans K' (SplitMap.map-equal r'' w x
        (ComposeEqual.compose-equal₁ p (SplitCompose.unmap s f' g')))
      $ Arrow'.arrow-trans K' (SplitMap.map-equal r'' w x
        (Associative.associative r f g h))
      $ Arrow'.arrow-trans K' (Arrow'.arrow-sym K' (SplitMap.map-equal r'' w x
        (ComposeEqual.compose-equal₂ q (SplitCompose.unmap t g' h'))))
      $ Arrow'.arrow-trans K' (Arrow'.arrow-sym K' (SplitMap.map-equal r'' w x
        (SplitCompose.unmap v f' j'')))
      $ SplitMap.map-unmap r'' w x (Compose.compose m' f' j'')
      where
        f = SplitMap.unmap m'' f'
        g = SplitMap.unmap n'' g'
        h = SplitMap.unmap o'' h'
        i'' = Compose.compose j' f' g'
        j'' = Compose.compose k' g' h'
        w = SplitBase.base-unbase a w'
        x = SplitBase.base-unbase d z'

  associative-induced
    : ComposeEqual l
    → ComposeEqual m
    → Associative j k l m
    → {a : SplitBase W W'}
    → {b : SplitBase X X'}
    → {c : SplitBase Y Y'}
    → {d : SplitBase Z Z'}
    → {m'' : SplitMap F F' c d}
    → {n'' : SplitMap G G' b c}
    → {o'' : SplitMap H H' a b}
    → {p'' : SplitMap I I' b d}
    → {q'' : SplitMap J J' a c}
    → {r'' : SplitMap K K' a d}
    → SplitCompose j j' m'' n'' p''
    → SplitCompose k k' n'' o'' q''
    → SplitCompose l l' p'' o'' r''
    → SplitCompose m m' m'' q'' r''
    → Associative j' k' l' m'
  associative-induced p q r s t u v
    = record {AssociativeInduced p q r s t u v}

-- ## Dependent

-- ### DependentComposeEqual

dependent-compose-equal-induced
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
  → DependentComposeEqual j'
dependent-compose-equal-induced {n = zero} p q
  = compose-equal-induced p q
dependent-compose-equal-induced {n = suc _} p q
  = record
  { tail
    = λ x y z → dependent-compose-equal-induced
      (DependentComposeEqual.tail p x y z)
      (DependentSplitCompose.tail q x y z)
  }

-- ### DependentPrecompose

dependent-precompose-induced
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : DependentArrow X' Y'}
  → {G : DependentArrow X' X'}
  → {F' : DependentArrow X'' Y''}
  → {G' : DependentArrow X'' X''}
  → {i : DependentIdentity G}
  → {i' : DependentIdentity G'}
  → {j : DependentCompose F G F}
  → {j' : DependentCompose F' G' F'}
  → DependentComposeEqual j
  → DependentPrecompose i j
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → {m : DependentSplitMap F F' a b}
  → {n : DependentSplitMap G G' a a}
  → DependentSplitIdentity i i' n
  → DependentSplitCompose j j' m n m
  → DependentPrecompose i' j'
dependent-precompose-induced {n = zero} p q r s
  = precompose-induced p q r s
dependent-precompose-induced {n = suc _} p q r s
  = record
  { tail
    = λ x y → dependent-precompose-induced
      (DependentComposeEqual.tail p x x y)
      (DependentPrecompose.tail q x y)
      (DependentSplitIdentity.tail r x)
      (DependentSplitCompose.tail s x x y)
  }

-- ### DependentPostcompose

dependent-postcompose-induced
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : DependentArrow Y' Y'}
  → {G : DependentArrow X' Y'}
  → {F' : DependentArrow Y'' Y''}
  → {G' : DependentArrow X'' Y''}
  → {i : DependentIdentity F}
  → {i' : DependentIdentity F'}
  → {j : DependentCompose F G G}
  → {j' : DependentCompose F' G' G'}
  → DependentComposeEqual j
  → DependentPostcompose i j
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → {m : DependentSplitMap F F' b b}
  → {n : DependentSplitMap G G' a b}
  → DependentSplitIdentity i i' m
  → DependentSplitCompose j j' m n n
  → DependentPostcompose i' j'
dependent-postcompose-induced {n = zero} p q r s
  = postcompose-induced p q r s
dependent-postcompose-induced {n = suc _} p q r s
  = record
  { tail
    = λ x y → dependent-postcompose-induced
      (DependentComposeEqual.tail p x y y)
      (DependentPostcompose.tail q x y)
      (DependentSplitIdentity.tail r y)
      (DependentSplitCompose.tail s x y y)
  }

-- ### DependentAssociative

dependent-associative-induced
  : {n : ℕ}
  → {W X Y Z : ChainObject n}
  → {W' W'' : DependentObject W}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {Z' Z'' : DependentObject Z}
  → {F : DependentArrow Y' Z'}
  → {G : DependentArrow X' Y'}
  → {H : DependentArrow W' X'}
  → {I : DependentArrow X' Z'}
  → {J : DependentArrow W' Y'}
  → {K : DependentArrow W' Z'}
  → {F' : DependentArrow Y'' Z''}
  → {G' : DependentArrow X'' Y''}
  → {H' : DependentArrow W'' X''}
  → {I' : DependentArrow X'' Z''}
  → {J' : DependentArrow W'' Y''}
  → {K' : DependentArrow W'' Z''}
  → {j : DependentCompose F G I}
  → {k : DependentCompose G H J}
  → {l : DependentCompose I H K}
  → {m : DependentCompose F J K}
  → {j' : DependentCompose F' G' I'}
  → {k' : DependentCompose G' H' J'}
  → {l' : DependentCompose I' H' K'}
  → {m' : DependentCompose F' J' K'}
  → DependentComposeEqual l
  → DependentComposeEqual m
  → DependentAssociative j k l m
  → {a : DependentSplitBase W' W''}
  → {b : DependentSplitBase X' X''}
  → {c : DependentSplitBase Y' Y''}
  → {d : DependentSplitBase Z' Z''}
  → {m'' : DependentSplitMap F F' c d}
  → {n'' : DependentSplitMap G G' b c}
  → {o'' : DependentSplitMap H H' a b}
  → {p'' : DependentSplitMap I I' b d}
  → {q'' : DependentSplitMap J J' a c}
  → {r'' : DependentSplitMap K K' a d}
  → DependentSplitCompose j j' m'' n'' p''
  → DependentSplitCompose k k' n'' o'' q''
  → DependentSplitCompose l l' p'' o'' r''
  → DependentSplitCompose m m' m'' q'' r''
  → DependentAssociative j' k' l' m'
dependent-associative-induced {n = zero} p q r s t u v
  = associative-induced p q r s t u v
dependent-associative-induced {n = suc _} p q r s t u v
  = record
  { tail
    = λ w x y z → dependent-associative-induced
      (DependentComposeEqual.tail p w x z)
      (DependentComposeEqual.tail q w y z)
      (DependentAssociative.tail r w x y z)
      (DependentSplitCompose.tail s x y z)
      (DependentSplitCompose.tail t w x y)
      (DependentSplitCompose.tail u w x z)
      (DependentSplitCompose.tail v w y z)
  }

