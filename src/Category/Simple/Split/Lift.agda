module Category.Simple.Split.Lift where

open import Category.Core
  using (Arrow'; ChainArrow; ChainArrow₀; ChainCompose; ChainCompose₀;
    ChainIdentity; ChainIdentity₀; ChainObject; ChainObject₀; DependentArrow;
    DependentCompose; DependentIdentity; DependentObject; Object')
open import Category.Lift
  using (ChainLift; ChainLift₀; ChainPath; DependentLift; DependentPath; Path)
open import Category.Simple.Lift
  using (DependentSimpleLift; DependentSimplePath; DependentSimplePrelift;
    DependentSimplePrelift'; SimplePath; dependent-lift-simple;
    dependent-path-simple; path-simple)
open import Category.Simple.State.Lift
  using (DependentSimpleStateLift; DependentSimpleStatePath; SimpleStatePath;
    dependent-state-lift-simple; dependent-state-path-simple; state-path-simple)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitMap; SplitBase; SplitMap)
open import Category.Split.Lift
  using (DependentSplitLift; DependentSplitLift'; DependentSplitPath;
    DependentSplitPath'; SplitPath; SplitPath')
open import Category.State.Lift
  using (DependentStateLift; DependentStatePath; StatePath)
open import Data.Equal
  using (_≡_)
open import Data.Maybe
  using (just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### SimpleSplitPath

-- #### Definition

record SimpleSplitPath
  {X Y X' Y' : Object'}
  (p : SimpleStatePath X Y)
  (p' : SimplePath X' Y')
  (a : SplitBase X X')
  (b : SplitBase Y Y')
  : Set
  where

  field

    base
      : (x : Object'.Object X)
      → {x' : Object'.Object X'}
      → SplitBase.base a x ≡ just x'
      → SplitBase.base b
        (SimpleStatePath.base p x)
      ≡ SimplePath.base p' x'

    unbase
      : (x : Object'.Object X')
      → {y : Object'.Object Y'}
      → SimplePath.base p' x ≡ just y
      → SplitBase.unbase b y
      ≡ SimpleStatePath.base p
        (SplitBase.unbase a x)

-- #### Conversion

split-path-simple
  : {X Y X' Y' : Object'}
  → {F : Arrow' X Y}
  → {F' : Arrow' X' Y'}
  → {p : StatePath F}
  → {p' : Path F'}
  → {a : SplitBase X X'}
  → {b : SplitBase Y Y'}
  → {m : SplitMap F F' a b}
  → SplitPath p p' m
  → SimpleSplitPath
    (state-path-simple p)
    (path-simple p') a b
split-path-simple q
  = record {SplitPath q}

-- ### SimpleSplitPath'

-- #### Definition

record SimpleSplitPath'
  {X Y X' Y' : Object'}
  (p : SimplePath X Y)
  (p' : SimplePath X' Y')
  (a : SplitBase X X')
  (b : SplitBase Y Y')
  : Set
  where

  field

    base-nothing
      : (x : Object'.Object X)
      → {x' : Object'.Object X'}
      → SimplePath.base p x ≡ nothing
      → SplitBase.base a x ≡ just x'
      → SimplePath.base p' x' ≡ nothing

    base-just
      : (x : Object'.Object X)
      → {y : Object'.Object Y}
      → {x' : Object'.Object X'}
      → SimplePath.base p x ≡ just y
      → SplitBase.base a x ≡ just x'
      → SplitBase.base b y
        ≡ SimplePath.base p' x'

    unbase
      : {y : Object'.Object Y}
      → (x' : Object'.Object X')
      → {y' : Object'.Object Y'}
      → SimplePath.base p
        (SplitBase.unbase a x')
        ≡ just y
      → SimplePath.base p' x' ≡ just y'
      → SplitBase.unbase b y' ≡ y

-- #### Conversion

split-path-simple'
  : {X Y X' Y' : Object'}
  → {F : Arrow' X Y}
  → {F' : Arrow' X' Y'}
  → {p : Path F}
  → {p' : Path F'}
  → {a : SplitBase X X'}
  → {b : SplitBase Y Y'}
  → {m : SplitMap F F' a b}
  → SplitPath' p p' m
  → SimpleSplitPath'
    (path-simple p)
    (path-simple p') a b
split-path-simple' q
  = record {SplitPath' q}

-- ## Dependent

-- ### DependentSimpleSplitPath

-- #### Types

DependentSimpleSplitPath
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {p : ChainPath F}
  → DependentSimpleStatePath X' Y' p
  → DependentSimplePath X'' Y'' p
  → DependentSplitBase X' X''
  → DependentSplitBase Y' Y''
  → Set

record DependentSimpleSplitPath''
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {Y' Y'' : DependentObject Y}
  {F : ChainArrow X Y}
  {p : ChainPath F}
  (p' : DependentSimpleStatePath X' Y' p)
  (p'' : DependentSimplePath X'' Y'' p)
  (a : DependentSplitBase X' X'')
  (b : DependentSplitBase Y' Y'')
  : Set

-- #### Definitions

DependentSimpleSplitPath {n = zero}
  = SimpleSplitPath
DependentSimpleSplitPath {n = suc _}
  = DependentSimpleSplitPath''

record DependentSimpleSplitPath'' {_ X Y _ _ _ _ _ p} p' p'' a b where

  inductive

  field

    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → (p''' : ChainPath.base p x ≡ just y)
      → DependentSimpleSplitPath
        (DependentSimpleStatePath.tail p' x p''')
        (DependentSimplePath.tail p'' x p''')
        (DependentSplitBase.tail a x)
        (DependentSplitBase.tail b y)

module DependentSimpleSplitPath
  = DependentSimpleSplitPath''

-- #### Conversion

dependent-split-path-simple
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {F'' : DependentArrow X'' Y''}
  → {p : ChainPath F}
  → {p' : DependentStatePath F' p}
  → {p'' : DependentPath F'' p}
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → {m : DependentSplitMap F' F'' a b}
  → DependentSplitPath p' p'' m
  → DependentSimpleSplitPath
    (dependent-state-path-simple p')
    (dependent-path-simple p'') a b
dependent-split-path-simple {n = zero} q
  = split-path-simple q
dependent-split-path-simple {n = suc _} q
  = record
  { tail
    = λ x p''' → dependent-split-path-simple
      (DependentSplitPath.tail q x p''')
  }

-- ### DependentSimpleSplitPath'

-- #### Types

DependentSimpleSplitPath'
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {p : ChainPath F}
  → DependentSimplePath X' Y' p
  → DependentSimplePath X'' Y'' p
  → DependentSplitBase X' X''
  → DependentSplitBase Y' Y''
  → Set

record DependentSimpleSplitPath'''
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {Y' Y'' : DependentObject Y}
  {F : ChainArrow X Y}
  {p : ChainPath F}
  (p' : DependentSimplePath X' Y' p)
  (p'' : DependentSimplePath X'' Y'' p)
  (a : DependentSplitBase X' X'')
  (b : DependentSplitBase Y' Y'')
  : Set

-- #### Definitions

DependentSimpleSplitPath' {n = zero}
  = SimpleSplitPath'
DependentSimpleSplitPath' {n = suc _}
  = DependentSimpleSplitPath'''

record DependentSimpleSplitPath''' {_ X Y _ _ _ _ _ p} p' p'' a b where

  inductive

  field

    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → (p''' : ChainPath.base p x ≡ just y)
      → DependentSimpleSplitPath'
        (DependentSimplePath.tail p' x p''')
        (DependentSimplePath.tail p'' x p''')
        (DependentSplitBase.tail a x)
        (DependentSplitBase.tail b y)

module DependentSimpleSplitPath'
  = DependentSimpleSplitPath'''

-- #### Conversion

dependent-split-path-simple'
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {F'' : DependentArrow X'' Y''}
  → {p : ChainPath F}
  → {p' : DependentPath F' p}
  → {p'' : DependentPath F'' p}
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → {m : DependentSplitMap F' F'' a b}
  → DependentSplitPath' p' p'' m
  → DependentSimpleSplitPath'
    (dependent-path-simple p')
    (dependent-path-simple p'') a b
dependent-split-path-simple' {n = zero} q
  = split-path-simple' q
dependent-split-path-simple' {n = suc _} q
  = record
  { tail
    = λ x p''' → dependent-split-path-simple'
      (DependentSplitPath'.tail q x p''')
  }

-- ### DependentSimpleSplitPrelift

-- #### Base

record DependentSimpleSplitPrelift₀
  {X : ChainObject₀}
  {X' X'' : DependentObject X}
  {F : ChainArrow₀ X X}
  {i : ChainIdentity₀ F}
  {j : ChainCompose₀ F F F}
  {l : ChainLift₀ F}
  (l' : DependentSimpleStateLift X' i l)
  (l'' : DependentSimplePrelift X'' j l)
  (a : DependentSplitBase X' X'')
  : Set
  where

  constructor

    tt

-- #### Types

DependentSimpleSplitPrelift
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {j : ChainCompose F F F}
  → {l : ChainLift F}
  → DependentSimpleStateLift X' i l
  → DependentSimplePrelift X'' j l
  → DependentSplitBase X' X''
  → Set

record DependentSimpleSplitPrelift''
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {F : ChainArrow X X}
  {i : ChainIdentity F}
  {j : ChainCompose F F F}
  {l : ChainLift F}
  (l' : DependentSimpleStateLift X' i l)
  (l'' : DependentSimplePrelift X'' j l)
  (a : DependentSplitBase X' X'')
  : Set

-- #### Definitions

DependentSimpleSplitPrelift {n = zero}
  = DependentSimpleSplitPrelift₀
DependentSimpleSplitPrelift {n = suc _}
  = DependentSimpleSplitPrelift''

record DependentSimpleSplitPrelift'' {_ X _ _ F} l' l'' a where

  inductive

  field
  
    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentSimpleSplitPath
        (DependentSimpleStateLift.path l' f)
        (DependentSimplePrelift.path l'' f)
        (DependentSplitBase.tail a x)
        (DependentSplitBase.tail a y)

    tail
      : (x : ChainObject.Object X)
      → DependentSimpleSplitPrelift
        (DependentSimpleStateLift.tail l' x)
        (DependentSimplePrelift.tail l'' x)
        (DependentSplitBase.tail a x)

module DependentSimpleSplitPrelift
  = DependentSimpleSplitPrelift''

-- ### DependentSimpleSplitPrelift'

-- #### Base

record DependentSimpleSplitPrelift₀'
  {X : ChainObject₀}
  {X' X'' : DependentObject X}
  {F : ChainArrow₀ X X}
  {i : ChainIdentity₀ F}
  {j : ChainCompose₀ F F F}
  {l : ChainLift₀ F}
  (l' : DependentSimpleLift X' i j l)
  (l'' : DependentSimplePrelift' X'' l)
  (a : DependentSplitBase X' X'')
  : Set
  where

  constructor

    tt

-- #### Types

DependentSimpleSplitPrelift'
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {j : ChainCompose F F F}
  → {l : ChainLift F}
  → DependentSimpleLift X' i j l
  → DependentSimplePrelift' X'' l
  → DependentSplitBase X' X''
  → Set

record DependentSimpleSplitPrelift'''
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {F : ChainArrow X X}
  {i : ChainIdentity F}
  {j : ChainCompose F F F}
  {l : ChainLift F}
  (l' : DependentSimpleLift X' i j l)
  (l'' : DependentSimplePrelift' X'' l)
  (a : DependentSplitBase X' X'')
  : Set

-- #### Definitions

DependentSimpleSplitPrelift' {n = zero}
  = DependentSimpleSplitPrelift₀'
DependentSimpleSplitPrelift' {n = suc _}
  = DependentSimpleSplitPrelift'''

record DependentSimpleSplitPrelift''' {_ X _ _ F} l' l'' a where

  inductive

  field
  
    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentSimpleSplitPath'
        (DependentSimpleLift.path l' f)
        (DependentSimplePrelift'.path l'' f)
        (DependentSplitBase.tail a x)
        (DependentSplitBase.tail a y)

    tail
      : (x : ChainObject.Object X)
      → DependentSimpleSplitPrelift'
        (DependentSimpleLift.tail l' x)
        (DependentSimplePrelift'.tail l'' x)
        (DependentSplitBase.tail a x)

module DependentSimpleSplitPrelift'
  = DependentSimpleSplitPrelift'''

-- ### DependentSimpleSplitLift

-- #### Base

record DependentSimpleSplitLift₀
  {X : ChainObject₀}
  {X' X'' : DependentObject X}
  {F : ChainArrow₀ X X}
  {i : ChainIdentity₀ F}
  {j : ChainCompose₀ F F F}
  {l : ChainLift₀ F}
  (l' : DependentSimpleStateLift X' i l)
  (l'' : DependentSimpleLift X'' i j l)
  (a : DependentSplitBase X' X'')
  : Set
  where

  constructor

    tt

-- #### Types

DependentSimpleSplitLift
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {j : ChainCompose F F F}
  → {l : ChainLift F}
  → DependentSimpleStateLift X' i l
  → DependentSimpleLift X'' i j l
  → DependentSplitBase X' X''
  → Set

record DependentSimpleSplitLift''
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {F : ChainArrow X X}
  {i : ChainIdentity F}
  {j : ChainCompose F F F}
  {l : ChainLift F}
  (l' : DependentSimpleStateLift X' i l)
  (l'' : DependentSimpleLift X'' i j l)
  (a : DependentSplitBase X' X'')
  : Set

-- #### Definitions

DependentSimpleSplitLift {n = zero}
  = DependentSimpleSplitLift₀
DependentSimpleSplitLift {n = suc _}
  = DependentSimpleSplitLift''

record DependentSimpleSplitLift'' {_ X _ _ F} l' l'' a where

  inductive

  field
  
    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentSimpleSplitPath
        (DependentSimpleStateLift.path l' f)
        (DependentSimpleLift.path l'' f)
        (DependentSplitBase.tail a x)
        (DependentSplitBase.tail a y)

    tail
      : (x : ChainObject.Object X)
      → DependentSimpleSplitLift
        (DependentSimpleStateLift.tail l' x)
        (DependentSimpleLift.tail l'' x)
        (DependentSplitBase.tail a x)

module DependentSimpleSplitLift
  = DependentSimpleSplitLift''

-- #### Conversion

dependent-split-lift-simple
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
  → {l'' : DependentLift i i'' j j'' l}
  → {a : DependentSplitBase X' X''}
  → {m : DependentSplitMap F' F'' a a}
  → DependentSplitLift l' l'' m
  → DependentSimpleSplitLift
    (dependent-state-lift-simple l')
    (dependent-lift-simple l'') a
dependent-split-lift-simple {n = zero} _
  = tt
dependent-split-lift-simple {n = suc _} p
  = record
  { path
    = λ f → dependent-split-path-simple
      (DependentSplitLift.path p f)
  ; tail
    = λ x → dependent-split-lift-simple
      (DependentSplitLift.tail p x)
  }

-- ### DependentSimpleSplitLift'

-- #### Base

record DependentSimpleSplitLift₀'
  {X : ChainObject₀}
  {X' X'' : DependentObject X}
  {F : ChainArrow₀ X X}
  {i : ChainIdentity₀ F}
  {j : ChainCompose₀ F F F}
  {l : ChainLift₀ F}
  (l' : DependentSimpleLift X' i j l)
  (l'' : DependentSimpleLift X'' i j l)
  (a : DependentSplitBase X' X'')
  : Set
  where

  constructor

    tt

-- #### Types

DependentSimpleSplitLift'
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {j : ChainCompose F F F}
  → {l : ChainLift F}
  → DependentSimpleLift X' i j l
  → DependentSimpleLift X'' i j l
  → DependentSplitBase X' X''
  → Set

record DependentSimpleSplitLift'''
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {F : ChainArrow X X}
  {i : ChainIdentity F}
  {j : ChainCompose F F F}
  {l : ChainLift F}
  (l' : DependentSimpleLift X' i j l)
  (l'' : DependentSimpleLift X'' i j l)
  (a : DependentSplitBase X' X'')
  : Set

-- #### Definitions

DependentSimpleSplitLift' {n = zero}
  = DependentSimpleSplitLift₀'
DependentSimpleSplitLift' {n = suc _}
  = DependentSimpleSplitLift'''

record DependentSimpleSplitLift''' {_ X _ _ F} l' l'' a where

  inductive

  field
  
    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentSimpleSplitPath'
        (DependentSimpleLift.path l' f)
        (DependentSimpleLift.path l'' f)
        (DependentSplitBase.tail a x)
        (DependentSplitBase.tail a y)

    tail
      : (x : ChainObject.Object X)
      → DependentSimpleSplitLift'
        (DependentSimpleLift.tail l' x)
        (DependentSimpleLift.tail l'' x)
        (DependentSplitBase.tail a x)

module DependentSimpleSplitLift'
  = DependentSimpleSplitLift'''

-- #### Conversion

dependent-split-lift-simple'
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
  → {l : ChainLift F}
  → {l' : DependentLift i i' j j' l}
  → {l'' : DependentLift i i'' j j'' l}
  → {a : DependentSplitBase X' X''}
  → {m : DependentSplitMap F' F'' a a}
  → DependentSplitLift' l' l'' m
  → DependentSimpleSplitLift'
    (dependent-lift-simple l')
    (dependent-lift-simple l'') a
dependent-split-lift-simple' {n = zero} _
  = tt
dependent-split-lift-simple' {n = suc _} p
  = record
  { path
    = λ f → dependent-split-path-simple'
      (DependentSplitLift'.path p f)
  ; tail
    = λ x → dependent-split-lift-simple'
      (DependentSplitLift'.tail p x)
  }

