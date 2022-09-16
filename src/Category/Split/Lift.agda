module Category.Split.Lift where

open import Category.Core
  using (Arrow'; ChainArrow; ChainArrow₀; ChainCompose; ChainCompose₀;
    ChainIdentity; ChainIdentity₀; ChainObject; ChainObject₀; DependentArrow;
    DependentArrow₁; DependentCompose; DependentIdentity; DependentObject;
    DependentObject₁; Object')
open import Category.Lift
  using (ChainLift; ChainLift₀; ChainPath; DependentLift; DependentPath;
    DependentPath₁; DependentPrelift; DependentPrelift'; Path)
open import Category.Split.Core
  using (DependentSplitBase; DependentSplitBase₁; DependentSplitMap;
    DependentSplitMap₁; SplitBase; SplitMap)
open import Category.State.Lift
  using (DependentStateLift; DependentStatePath; DependentStatePath₁; StatePath)
open import Data.Empty
  using (⊥-elim)
open import Data.Equal
  using (_≡_; sub; sym; trans)
open import Data.Function
  using (_$_)
open import Data.Inspect
  using ([_]; inspect)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### SplitPath

record SplitPath
  {X Y X' Y' : Object'}
  {F : Arrow' X Y}
  {F' : Arrow' X' Y'}
  (p : StatePath F)
  (p' : Path F')
  {a : SplitBase X X'}
  {b : SplitBase Y Y'}
  (m : SplitMap F F' a b)
  : Set
  where

  field

    base
      : (x : Object'.Object X)
      → {x' : Object'.Object X'}
      → SplitBase.base a x ≡ just x'
      → SplitBase.base b
        (StatePath.base p x)
      ≡ Path.base p' x'

    map
      : (x : Object'.Object X)
      → {x' : Object'.Object X'}
      → {y' : Object'.Object Y'}
      → (q : Path.base p' x' ≡ just y')
      → (r : SplitBase.base a x ≡ just x')
      → (s : SplitBase.base b
        (StatePath.base p x)
        ≡ just y')
      → Arrow'.ArrowEqual F'
        (SplitMap.map m r s
          (StatePath.map p x))
        (Path.map p' x' q)
    
    unmap
      : (x : Object'.Object X')
      → {y : Object'.Object Y'}
      → (q : Path.base p' x ≡ just y)
      → Arrow'.ArrowEqual' F
        (SplitMap.unmap m
          (Path.map p' x q))
        (StatePath.map p
          (SplitBase.unbase a x))

  map'
    : (x : Object'.Object X)
    → {x' : Object'.Object X'}
    → {y' : Object'.Object Y'}
    → (q : Path.base p' x' ≡ just y')
    → (r : SplitBase.base a x ≡ just x')
    → (s : SplitBase.base b
      (StatePath.base p x)
      ≡ just y')
    → Arrow'.ArrowEqual' F'
      (SplitMap.map m r s
        (StatePath.map p x))
      (Path.map p' x' q)
  map' x q r s
    = Arrow'.arrow-equal (map x q r s)
    
  unbase
    : (x : Object'.Object X')
    → {y : Object'.Object Y'}
    → Path.base p' x ≡ just y
    → SplitBase.unbase b y
    ≡ StatePath.base p
      (SplitBase.unbase a x)
  unbase x q
    = Arrow'.arrow-codomain F (unmap x q)

-- ### SplitPath'

record SplitPath'
  {X Y X' Y' : Object'}
  {F : Arrow' X Y}
  {F' : Arrow' X' Y'}
  (p : Path F)
  (p' : Path F')
  {a : SplitBase X X'}
  {b : SplitBase Y Y'}
  (m : SplitMap F F' a b)
  : Set
  where

  field

    base-nothing
      : (x : Object'.Object X)
      → {x' : Object'.Object X'}
      → Path.base p x ≡ nothing
      → SplitBase.base a x ≡ just x'
      → Path.base p' x' ≡ nothing

    base-just
      : (x : Object'.Object X)
      → {y : Object'.Object Y}
      → {x' : Object'.Object X'}
      → Path.base p x ≡ just y
      → SplitBase.base a x ≡ just x'
      → SplitBase.base b y
        ≡ Path.base p' x'

    map
      : (x : Object'.Object X)
      → {y : Object'.Object Y}
      → {x' : Object'.Object X'}
      → {y' : Object'.Object Y'}
      → (q : Path.base p x ≡ just y)
      → (q' : Path.base p' x' ≡ just y')
      → (r : SplitBase.base a x ≡ just x')
      → (s : SplitBase.base b y ≡ just y')
      → Arrow'.ArrowEqual F'
        (SplitMap.map m r s
          (Path.map p x q))
        (Path.map p' x' q')
    
    unmap
      : (x' : Object'.Object X')
      → {y : Object'.Object Y}
      → {y' : Object'.Object Y'}
      → (q : Path.base p
        (SplitBase.unbase a x')
        ≡ just y)
      → (q' : Path.base p' x' ≡ just y')
      → Arrow'.ArrowEqual' F
        (SplitMap.unmap m
          (Path.map p' x' q'))
        (Path.map p
          (SplitBase.unbase a x') q)

  unbase
    : {y : Object'.Object Y}
    → (x' : Object'.Object X')
    → {y' : Object'.Object Y'}
    → Path.base p
      (SplitBase.unbase a x')
      ≡ just y
    → Path.base p' x' ≡ just y'
    → SplitBase.unbase b y' ≡ y
  unbase x' q q'
    = Arrow'.arrow-codomain F (unmap x' q q')

  unbase'
    : (x : Object'.Object X')
    → {y : Object'.Object Y'}
    → Path.base p' x ≡ just y
    → Path.base p
      (SplitBase.unbase a x)
    ≡ just (SplitBase.unbase b y)
  unbase' x q'
    with Path.base p (SplitBase.unbase a x)
    | inspect (Path.base p) (SplitBase.unbase a x)
  ... | nothing | [ q ]
    = ⊥-elim
    ( Maybe.just≢nothing
    $ trans (sym q')
    $ base-nothing
      (SplitBase.unbase a x) q
      (SplitBase.base-unbase a x)
    )
  ... | just _ | [ q ]
    = sym (sub just (unbase x q q'))

-- ## Dependent

-- ### DependentSplitPath

-- #### Types

DependentSplitPath
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {F'' : DependentArrow X'' Y''}
  → {p : ChainPath F}
  → DependentStatePath F' p
  → DependentPath F'' p
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → DependentSplitMap F' F'' a b
  → Set

record DependentSplitPath''
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {Y' Y'' : DependentObject Y}
  {F : ChainArrow X Y}
  {F' : DependentArrow X' Y'}
  {F'' : DependentArrow X'' Y''}
  {p : ChainPath F}
  (p' : DependentStatePath F' p)
  (p'' : DependentPath F'' p)
  {a : DependentSplitBase X' X''}
  {b : DependentSplitBase Y' Y''}
  (m : DependentSplitMap F' F'' a b)
  : Set

-- #### Definitions

DependentSplitPath {n = zero}
  = SplitPath
DependentSplitPath {n = suc _}
  = DependentSplitPath''

record DependentSplitPath'' {_ X Y _ _ _ _ _ _ _ p} p' p'' m where

  inductive

  field

    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → (p''' : ChainPath.base p x ≡ just y)
      → DependentSplitPath
        (DependentStatePath.tail p' x p''')
        (DependentPath.tail p'' x p''')
        (DependentSplitMap.tail m x y)

module DependentSplitPath
  = DependentSplitPath''

-- ### DependentSplitPath'

-- #### Types

DependentSplitPath'
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {F' : DependentArrow X' Y'}
  → {F'' : DependentArrow X'' Y''}
  → {p : ChainPath F}
  → DependentPath F' p
  → DependentPath F'' p
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → DependentSplitMap F' F'' a b
  → Set

record DependentSplitPath'''
  {n : ℕ}
  {X Y : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {Y' Y'' : DependentObject Y}
  {F : ChainArrow X Y}
  {F' : DependentArrow X' Y'}
  {F'' : DependentArrow X'' Y''}
  {p : ChainPath F}
  (p' : DependentPath F' p)
  (p'' : DependentPath F'' p)
  {a : DependentSplitBase X' X''}
  {b : DependentSplitBase Y' Y''}
  (m : DependentSplitMap F' F'' a b)
  : Set

-- #### Definitions

DependentSplitPath' {n = zero}
  = SplitPath'
DependentSplitPath' {n = suc _}
  = DependentSplitPath'''

record DependentSplitPath''' {_ X Y _ _ _ _ _ _ _ p} p' p'' m where

  inductive

  field

    tail
      : (x : ChainObject.Object X)
      → {y : ChainObject.Object Y}
      → (p''' : ChainPath.base p x ≡ just y)
      → DependentSplitPath'
        (DependentPath.tail p' x p''')
        (DependentPath.tail p'' x p''')
        (DependentSplitMap.tail m x y)

module DependentSplitPath'
  = DependentSplitPath'''

-- ### DependentSplitPrelift

-- #### Base

record DependentSplitPrelift₀
  {X : ChainObject₀}
  {X' X'' : DependentObject X}
  {F : ChainArrow₀ X X}
  {F' : DependentArrow X' X'}
  {F'' : DependentArrow X'' X''}
  {i : ChainIdentity₀ F}
  {i' : DependentIdentity F'}
  {j : ChainCompose₀ F F F}
  {j'' : DependentCompose F'' F'' F''}
  {l : ChainLift₀ F}
  (l' : DependentStateLift i i' l)
  (l'' : DependentPrelift j j'' l)
  {a : DependentSplitBase X' X''}
  (m : DependentSplitMap F' F'' a a)
  : Set
  where

  constructor
  
    tt

-- #### Types

DependentSplitPrelift
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {F'' : DependentArrow X'' X''}
  → {i : ChainIdentity F}
  → {i' : DependentIdentity F'}
  → {j : ChainCompose F F F}
  → {j'' : DependentCompose F'' F'' F''}
  → {l : ChainLift F}
  → DependentStateLift i i' l
  → DependentPrelift j j'' l
  → {a : DependentSplitBase X' X''}
  → DependentSplitMap F' F'' a a
  → Set

record DependentSplitPrelift''
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {F : ChainArrow X X}
  {F' : DependentArrow X' X'}
  {F'' : DependentArrow X'' X''}
  {i : ChainIdentity F}
  {i' : DependentIdentity F'}
  {j : ChainCompose F F F}
  {j'' : DependentCompose F'' F'' F''}
  {l : ChainLift F}
  (l' : DependentStateLift i i' l)
  (l'' : DependentPrelift j j'' l)
  {a : DependentSplitBase X' X''}
  (m : DependentSplitMap F' F'' a a)
  : Set

-- #### Definitions

DependentSplitPrelift {n = zero}
  = DependentSplitPrelift₀
DependentSplitPrelift {n = suc _}
  = DependentSplitPrelift''

record DependentSplitPrelift'' {_ X _ _ F} l' l'' m where

  inductive

  field

    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentSplitPath
        (DependentStateLift.path l' f)
        (DependentPrelift.path l'' f)
        (DependentSplitMap.tail m x y)

    tail
      : (x : ChainObject.Object X)
      → DependentSplitPrelift
        (DependentStateLift.tail l' x)
        (DependentPrelift.tail l'' x)
        (DependentSplitMap.tail m x x)

module DependentSplitPrelift
  = DependentSplitPrelift''

-- ### DependentSplitPrelift'

-- #### Base

record DependentSplitPrelift₀'
  {X : ChainObject₀}
  {X' X'' : DependentObject X}
  {F : ChainArrow₀ X X}
  {F' : DependentArrow X' X'}
  {F'' : DependentArrow X'' X''}
  {i : ChainIdentity₀ F}
  {i' : DependentIdentity F'}
  {j : ChainCompose₀ F F F}
  {j' : DependentCompose F' F' F'}
  {l : ChainLift₀ F}
  (l' : DependentLift i i' j j' l)
  (l'' : DependentPrelift' F'' l)
  {a : DependentSplitBase X' X''}
  (m : DependentSplitMap F' F'' a a)
  : Set
  where

  constructor
  
    tt

-- #### Types

DependentSplitPrelift'
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → {F'' : DependentArrow X'' X''}
  → {i : ChainIdentity F}
  → {i' : DependentIdentity F'}
  → {j : ChainCompose F F F}
  → {j' : DependentCompose F' F' F'}
  → {l : ChainLift F}
  → DependentLift i i' j j' l
  → DependentPrelift' F'' l
  → {a : DependentSplitBase X' X''}
  → DependentSplitMap F' F'' a a
  → Set

record DependentSplitPrelift'''
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {F : ChainArrow X X}
  {F' : DependentArrow X' X'}
  {F'' : DependentArrow X'' X''}
  {i : ChainIdentity F}
  {i' : DependentIdentity F'}
  {j : ChainCompose F F F}
  {j' : DependentCompose F' F' F'}
  {l : ChainLift F}
  (l' : DependentLift i i' j j' l)
  (l'' : DependentPrelift' F'' l)
  {a : DependentSplitBase X' X''}
  (m : DependentSplitMap F' F'' a a)
  : Set

-- #### Definitions

DependentSplitPrelift' {n = zero}
  = DependentSplitPrelift₀'
DependentSplitPrelift' {n = suc _}
  = DependentSplitPrelift'''

record DependentSplitPrelift''' {_ X _ _ F} l' l'' m where

  inductive

  field

    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentSplitPath'
        (DependentLift.path l' f)
        (DependentPrelift'.path l'' f)
        (DependentSplitMap.tail m x y)

    tail
      : (x : ChainObject.Object X)
      → DependentSplitPrelift'
        (DependentLift.tail l' x)
        (DependentPrelift'.tail l'' x)
        (DependentSplitMap.tail m x x)

module DependentSplitPrelift'
  = DependentSplitPrelift'''

-- ### DependentSplitLift

-- #### Base

record DependentSplitLift₀
  {X : ChainObject₀}
  {X' X'' : DependentObject X}
  {F : ChainArrow₀ X X}
  {F' : DependentArrow X' X'}
  {F'' : DependentArrow X'' X''}
  {i : ChainIdentity₀ F}
  {i' : DependentIdentity F'}
  {i'' : DependentIdentity F''}
  {j : ChainCompose₀ F F F}
  {j'' : DependentCompose F'' F'' F''}
  {l : ChainLift₀ F}
  (l' : DependentStateLift i i' l)
  (l'' : DependentLift i i'' j j'' l)
  {a : DependentSplitBase X' X''}
  (m : DependentSplitMap F' F'' a a)
  : Set
  where

  constructor
  
    tt

-- #### Types

DependentSplitLift
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
  → DependentStateLift i i' l
  → DependentLift i i'' j j'' l
  → {a : DependentSplitBase X' X''}
  → DependentSplitMap F' F'' a a
  → Set

record DependentSplitLift''
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {F : ChainArrow X X}
  {F' : DependentArrow X' X'}
  {F'' : DependentArrow X'' X''}
  {i : ChainIdentity F}
  {i' : DependentIdentity F'}
  {i'' : DependentIdentity F''}
  {j : ChainCompose F F F}
  {j'' : DependentCompose F'' F'' F''}
  {l : ChainLift F}
  (l' : DependentStateLift i i' l)
  (l'' : DependentLift i i'' j j'' l)
  {a : DependentSplitBase X' X''}
  (m : DependentSplitMap F' F'' a a)
  : Set

-- #### Definitions

DependentSplitLift {n = zero}
  = DependentSplitLift₀
DependentSplitLift {n = suc _}
  = DependentSplitLift''

record DependentSplitLift'' {_ X _ _ F} l' l'' m where

  inductive

  field

    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentSplitPath
        (DependentStateLift.path l' f)
        (DependentLift.path l'' f)
        (DependentSplitMap.tail m x y)

    tail
      : (x : ChainObject.Object X)
      → DependentSplitLift
        (DependentStateLift.tail l' x)
        (DependentLift.tail l'' x)
        (DependentSplitMap.tail m x x)

module DependentSplitLift
  = DependentSplitLift''

-- ### DependentSplitLift'

-- #### Base

record DependentSplitLift₀'
  {X : ChainObject₀}
  {X' X'' : DependentObject X}
  {F : ChainArrow₀ X X}
  {F' : DependentArrow X' X'}
  {F'' : DependentArrow X'' X''}
  {i : ChainIdentity₀ F}
  {i' : DependentIdentity F'}
  {i'' : DependentIdentity F''}
  {j : ChainCompose₀ F F F}
  {j' : DependentCompose F' F' F'}
  {j'' : DependentCompose F'' F'' F''}
  {l : ChainLift₀ F}
  (l' : DependentLift i i' j j' l)
  (l'' : DependentLift i i'' j j'' l)
  {a : DependentSplitBase X' X''}
  (m : DependentSplitMap F' F'' a a)
  : Set
  where

  constructor
  
    tt

-- #### Types

DependentSplitLift'
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
  → DependentLift i i' j j' l
  → DependentLift i i'' j j'' l
  → {a : DependentSplitBase X' X''}
  → DependentSplitMap F' F'' a a
  → Set

record DependentSplitLift'''
  {n : ℕ}
  {X : ChainObject (suc n)}
  {X' X'' : DependentObject X}
  {F : ChainArrow X X}
  {F' : DependentArrow X' X'}
  {F'' : DependentArrow X'' X''}
  {i : ChainIdentity F}
  {i' : DependentIdentity F'}
  {i'' : DependentIdentity F''}
  {j : ChainCompose F F F}
  {j' : DependentCompose F' F' F'}
  {j'' : DependentCompose F'' F'' F''}
  {l : ChainLift F}
  (l' : DependentLift i i' j j' l)
  (l'' : DependentLift i i'' j j'' l)
  {a : DependentSplitBase X' X''}
  (m : DependentSplitMap F' F'' a a)
  : Set

-- #### Definitions

DependentSplitLift' {n = zero}
  = DependentSplitLift₀'
DependentSplitLift' {n = suc _}
  = DependentSplitLift'''

record DependentSplitLift''' {_ X _ _ F} l' l'' m where

  inductive

  field

    path
      : {x y : ChainObject.Object X}
      → (f : ChainArrow.Arrow F x y)
      → DependentSplitPath'
        (DependentLift.path l' f)
        (DependentLift.path l'' f)
        (DependentSplitMap.tail m x y)

    tail
      : (x : ChainObject.Object X)
      → DependentSplitLift'
        (DependentLift.tail l' x)
        (DependentLift.tail l'' x)
        (DependentSplitMap.tail m x x)

module DependentSplitLift'
  = DependentSplitLift'''

-- ## Dependent₁

-- ### DependentSplitPath₁

-- #### Definition

DependentSplitPath₁
  : {X Y : Object'}
  → {X' X'' : DependentObject₁ X}
  → {Y' Y'' : DependentObject₁ Y}
  → {F : Arrow' X Y}
  → {F' : DependentArrow₁ X' Y'}
  → {F'' : DependentArrow₁ X'' Y''}
  → {p : Path F}
  → DependentStatePath₁ F' p
  → DependentPath₁ F'' p
  → {a : DependentSplitBase₁ X' X''}
  → {b : DependentSplitBase₁ Y' Y''}
  → DependentSplitMap₁ F' F'' a b
  → Set
DependentSplitPath₁
  = DependentSplitPath

-- #### Module

module DependentSplitPath₁
  {X Y : Object'}
  {X' X'' : DependentObject₁ X}
  {Y' Y'' : DependentObject₁ Y}
  {F : Arrow' X Y}
  {F' : DependentArrow₁ X' Y'}
  {F'' : DependentArrow₁ X'' Y''}
  {p : Path F}
  {p' : DependentStatePath₁ F' p}
  {p'' : DependentPath₁ F'' p}
  {a : DependentSplitBase₁ X' X''}
  {b : DependentSplitBase₁ Y' Y''}
  {m : DependentSplitMap₁ F' F'' a b}
  (q : DependentSplitPath₁ p' p'' m)
  where

  open DependentSplitPath q public

  open module SplitPath'' {x y} p'''
    = SplitPath (tail x {y} p''') public

