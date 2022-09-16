module Category.Simple.Lift.Induced where

open import Category.Core
  using (ChainArrow; ChainCompose; ChainIdentity; ChainObject; DependentObject;
    Object')
open import Category.Core.Unit
  using (compose-equal-unit)
open import Category.Lift
  using (ChainLift; ChainPath)
open import Category.Lift.Unit
  using (path-compose-unit; path-equal-unit; path-identity-unit)
open import Category.Lift.Induced
  using (path-compose-induced'; path-equal-induced; path-equal-induced';
    path-identity-induced; path-identity-induced')
open import Category.Simple.Lift
  using (DependentSimpleLift; DependentSimplePath; DependentSimplePathCompose;
    DependentSimplePathEqual; DependentSimplePathIdentity;
    DependentSimplePrelift; DependentSimplePrelift'; SimplePath;
    SimplePathCompose; SimplePathEqual; SimplePathIdentity; path-compose-simple;
    path-equal-simple; path-identity-simple; tt)
open import Category.Simple.Split.Lift
  using (DependentSimpleSplitPath; DependentSimpleSplitPath';
    DependentSimpleSplitPrelift; DependentSimpleSplitPrelift'; SimpleSplitPath;
    SimpleSplitPath')
open import Category.Simple.State.Lift
  using (DependentSimpleStateLift; DependentSimpleStatePath;
    DependentSimpleStatePathEqual; DependentSimpleStatePathIdentity;
    SimpleStatePath; SimpleStatePathEqual; SimpleStatePathIdentity)
open import Category.Split.Core
  using (DependentSplitBase; SplitBase)
open import Category.Split.Core.Unit
  using (split-compose-unit; split-identity-unit)
open import Category.Split.Lift.Unit
  using (split-path-unit; split-path-unit')
open import Category.State.Lift.Unit
  using (state-path-equal-unit; state-path-identity-unit)
open import Data.Function
  using (_$_)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Base

-- ### SimplePathEqual

simple-path-equal-induced
  : {X Y X' Y' : Object'}
  → {p₁ p₂ : SimpleStatePath X Y}
  → {p₁' p₂' : SimplePath X' Y'}
  → SimpleStatePathEqual p₁ p₂
  → {a : SplitBase X X'}
  → {b : SplitBase Y Y'}
  → SimpleSplitPath p₁ p₁' a b
  → SimpleSplitPath p₂ p₂' a b
  → SimplePathEqual p₁' p₂'
simple-path-equal-induced q r₁ r₂
  = path-equal-simple
  $ path-equal-induced
    (state-path-equal-unit q)
    (split-path-unit r₁)
    (split-path-unit r₂)

-- ### SimplePathEqual'

simple-path-equal-induced'
  : {X Y X' Y' : Object'}
  → {p₁ p₂ : SimplePath X Y}
  → {p₁' p₂' : SimplePath X' Y'}
  → SimplePathEqual p₁ p₂
  → {a : SplitBase X X'}
  → {b : SplitBase Y Y'}
  → SimpleSplitPath' p₁ p₁' a b
  → SimpleSplitPath' p₂ p₂' a b
  → SimplePathEqual p₁' p₂'
simple-path-equal-induced' q r₁ r₂
  = path-equal-simple
  $ path-equal-induced'
    (path-equal-unit q)
    (split-path-unit' r₁)
    (split-path-unit' r₂)

-- ### SimplePathIdentity

simple-path-identity-induced
  : {X X' : Object'}
  → {p : SimpleStatePath X X}
  → {p' : SimplePath X' X'}
  → SimpleStatePathIdentity p
  → {a : SplitBase X X'}
  → SimpleSplitPath p p' a a
  → SimplePathIdentity p'
simple-path-identity-induced q {a = a} r
  = path-identity-simple
  $ path-identity-induced
    (state-path-identity-unit q)
    (split-identity-unit a)
    (split-path-unit r)

-- ### SimplePathIdentity'

simple-path-identity-induced'
  : {X X' : Object'}
  → {p : SimplePath X X}
  → {p' : SimplePath X' X'}
  → SimplePathIdentity p
  → {a : SplitBase X X'}
  → SimpleSplitPath' p p' a a
  → SimplePathIdentity p'
simple-path-identity-induced' q {a = a} r
  = path-identity-simple
  $ path-identity-induced'
    (path-identity-unit q)
    (split-identity-unit a)
    (split-path-unit' r)

-- ### SimplePathCompose'

simple-path-compose-induced'
  : {X Y Z X' Y' Z' : Object'}
  → {p : SimplePath Y Z}
  → {q : SimplePath X Y}
  → {r : SimplePath X Z}
  → {p' : SimplePath Y' Z'}
  → {q' : SimplePath X' Y'}
  → {r' : SimplePath X' Z'}
  → SimplePathCompose p q r
  → {a : SplitBase X X'}
  → {b : SplitBase Y Y'}
  → {c : SplitBase Z Z'}
  → SimpleSplitPath' p p' b c
  → SimpleSplitPath' q q' a b
  → SimpleSplitPath' r r' a c
  → SimplePathCompose p' q' r'
simple-path-compose-induced'
  {X = X} {Y = Y} {Z = Z} s
  {a = a} {b = b} {c = c} t u v
  = path-compose-simple
  $ path-compose-induced'
    (compose-equal-unit X Y Z)
    (path-compose-unit s)
    (split-compose-unit a b c)
    (split-path-unit' t)
    (split-path-unit' u)
    (split-path-unit' v)

-- ## Dependent

-- ### DependentSimplePathEqual

dependent-simple-path-equal-induced
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {p₁ p₂ : ChainPath F}
  → {p₁' : DependentSimpleStatePath X' Y' p₁}
  → {p₂' : DependentSimpleStatePath X' Y' p₂}
  → {p₁'' : DependentSimplePath X'' Y'' p₁}
  → {p₂'' : DependentSimplePath X'' Y'' p₂}
  → DependentSimpleStatePathEqual p₁' p₂'
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → DependentSimpleSplitPath p₁' p₁'' a b
  → DependentSimpleSplitPath p₂' p₂'' a b
  → DependentSimplePathEqual p₁'' p₂''
dependent-simple-path-equal-induced {n = zero} q r₁ r₂
  = simple-path-equal-induced q r₁ r₂
dependent-simple-path-equal-induced {n = suc _} q r₁ r₂
  = record
  { tail
    = λ x p₁''' p₂''' → dependent-simple-path-equal-induced
      (DependentSimpleStatePathEqual.tail q x p₁''' p₂''')
      (DependentSimpleSplitPath.tail r₁ x p₁''')
      (DependentSimpleSplitPath.tail r₂ x p₂''')
  }

-- ### DependentSimplePathEqual'

dependent-simple-path-equal-induced'
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {F : ChainArrow X Y}
  → {p₁ p₂ : ChainPath F}
  → {p₁' : DependentSimplePath X' Y' p₁}
  → {p₂' : DependentSimplePath X' Y' p₂}
  → {p₁'' : DependentSimplePath X'' Y'' p₁}
  → {p₂'' : DependentSimplePath X'' Y'' p₂}
  → DependentSimplePathEqual p₁' p₂'
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → DependentSimpleSplitPath' p₁' p₁'' a b
  → DependentSimpleSplitPath' p₂' p₂'' a b
  → DependentSimplePathEqual p₁'' p₂''
dependent-simple-path-equal-induced' {n = zero} q r₁ r₂
  = simple-path-equal-induced' q r₁ r₂
dependent-simple-path-equal-induced' {n = suc _} q r₁ r₂
  = record
  { tail
    = λ x p₁''' p₂''' → dependent-simple-path-equal-induced'
      (DependentSimplePathEqual.tail q x p₁''' p₂''')
      (DependentSimpleSplitPath'.tail r₁ x p₁''')
      (DependentSimpleSplitPath'.tail r₂ x p₂''')
  }

-- ### DependentSimplePathIdentity

dependent-simple-path-identity-induced
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {p : ChainPath F}
  → {p' : DependentSimpleStatePath X' X' p}
  → {p'' : DependentSimplePath X'' X'' p}
  → DependentSimpleStatePathIdentity p'
  → {a : DependentSplitBase X' X''}
  → DependentSimpleSplitPath p' p'' a a
  → DependentSimplePathIdentity p''
dependent-simple-path-identity-induced {n = zero} q r
  = simple-path-identity-induced q r
dependent-simple-path-identity-induced {n = suc _} q r
  = record
  { tail
    = λ {x} p'' → dependent-simple-path-identity-induced
      (DependentSimpleStatePathIdentity.tail q p'')
      (DependentSimpleSplitPath.tail r x p'')
  }

-- ### DependentSimplePathIdentity'

dependent-simple-path-identity-induced'
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {p : ChainPath F}
  → {p' : DependentSimplePath X' X' p}
  → {p'' : DependentSimplePath X'' X'' p}
  → DependentSimplePathIdentity p'
  → {a : DependentSplitBase X' X''}
  → DependentSimpleSplitPath' p' p'' a a
  → DependentSimplePathIdentity p''
dependent-simple-path-identity-induced' {n = zero} q r
  = simple-path-identity-induced' q r
dependent-simple-path-identity-induced' {n = suc _} q r
  = record
  { tail
    = λ {x} p'' → dependent-simple-path-identity-induced'
      (DependentSimplePathIdentity.tail q p'')
      (DependentSimpleSplitPath'.tail r x p'')
  }

-- ### DependentSimplePathCompose'

dependent-simple-path-compose-induced'
  : {n : ℕ}
  → {X Y Z : ChainObject n}
  → {X' X'' : DependentObject X}
  → {Y' Y'' : DependentObject Y}
  → {Z' Z'' : DependentObject Z}
  → {F : ChainArrow Y Z}
  → {G : ChainArrow X Y}
  → {H : ChainArrow X Z}
  → {p : ChainPath F}
  → {q : ChainPath G}
  → {r : ChainPath H}
  → {p' : DependentSimplePath Y' Z' p}
  → {q' : DependentSimplePath X' Y' q}
  → {r' : DependentSimplePath X' Z' r}
  → {p'' : DependentSimplePath Y'' Z'' p}
  → {q'' : DependentSimplePath X'' Y'' q}
  → {r'' : DependentSimplePath X'' Z'' r}
  → DependentSimplePathCompose p' q' r'
  → {a : DependentSplitBase X' X''}
  → {b : DependentSplitBase Y' Y''}
  → {c : DependentSplitBase Z' Z''}
  → DependentSimpleSplitPath' p' p'' b c
  → DependentSimpleSplitPath' q' q'' a b
  → DependentSimpleSplitPath' r' r'' a c
  → DependentSimplePathCompose p'' q'' r''
dependent-simple-path-compose-induced' {n = zero} s t u v
  = simple-path-compose-induced' s t u v
dependent-simple-path-compose-induced' {n = suc _} s t u v
  = record
  { tail
    = λ x {y} p'' q'' r'' → dependent-simple-path-compose-induced'
      (DependentSimplePathCompose.tail s x p'' q'' r'')
      (DependentSimpleSplitPath'.tail t y p'')
      (DependentSimpleSplitPath'.tail u x q'')
      (DependentSimpleSplitPath'.tail v x r'')
  }

-- ### DependentSimpleLift

dependent-simple-lift-induced
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {j : ChainCompose F F F}
  → {l : ChainLift F}
  → {l' : DependentSimpleStateLift X' i l}
  → {l'' : DependentSimplePrelift X'' j l}
  → {a : DependentSplitBase X' X''}
  → DependentSimpleSplitPrelift l' l'' a
  → DependentSimpleLift X'' i j l
dependent-simple-lift-induced {n = zero} _
  = tt
dependent-simple-lift-induced {n = suc _}
  {i = i} {l' = l'} {l'' = l''} p
  = record
  { DependentSimplePrelift l''
  ; path-equal
    = λ {_} {_} {f₁} {f₂} q → dependent-simple-path-equal-induced
      (DependentSimpleStateLift.path-equal l' q)
      (DependentSimpleSplitPrelift.path p f₁)
      (DependentSimpleSplitPrelift.path p f₂)
  ; path-identity
    = λ x → dependent-simple-path-identity-induced
      (DependentSimpleStateLift.path-identity l' x)
      (DependentSimpleSplitPrelift.path p
        (ChainIdentity.identity i x))
  ; tail
    = λ x → dependent-simple-lift-induced
      (DependentSimpleSplitPrelift.tail p x)
  }

-- ### DependentSimpleLift'

dependent-simple-lift-induced'
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' X'' : DependentObject X}
  → {F : ChainArrow X X}
  → {i : ChainIdentity F}
  → {j : ChainCompose F F F}
  → {l : ChainLift F}
  → {l' : DependentSimpleLift X' i j l}
  → {l'' : DependentSimplePrelift' X'' l}
  → {a : DependentSplitBase X' X''}
  → DependentSimpleSplitPrelift' l' l'' a
  → DependentSimpleLift X'' i j l
dependent-simple-lift-induced' {n = zero} _
  = tt
dependent-simple-lift-induced' {n = suc _}
  {i = i} {j = j} {l' = l'} {l'' = l''} p
  = record
  { DependentSimplePrelift' l''
  ; path-equal
    = λ {_} {_} {f₁} {f₂} q → dependent-simple-path-equal-induced'
      (DependentSimpleLift.path-equal l' q)
      (DependentSimpleSplitPrelift'.path p f₁)
      (DependentSimpleSplitPrelift'.path p f₂)
  ; path-identity
    = λ x → dependent-simple-path-identity-induced'
      (DependentSimpleLift.path-identity l' x)
      (DependentSimpleSplitPrelift'.path p
        (ChainIdentity.identity i x))
  ; path-compose
    = λ f g → dependent-simple-path-compose-induced'
      (DependentSimpleLift.path-compose l' f g)
      (DependentSimpleSplitPrelift'.path p f)
      (DependentSimpleSplitPrelift'.path p g)
      (DependentSimpleSplitPrelift'.path p
        (ChainCompose.compose j f g))
  ; tail
    = λ x → dependent-simple-lift-induced'
      (DependentSimpleSplitPrelift'.tail p x)
  }

