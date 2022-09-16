module Category.Core.Snoc where

open import Category.Core
  using (ChainArrow; ChainCompose; ChainIdentity; ChainObject; DependentArrow;
    DependentCompose; DependentIdentity; DependentObject; chain-arrow₁;
    chain-compose₁; chain-identity₁; chain-object₁)
open import Data.Nat
  using (ℕ; suc; zero)

-- ## Chain

-- ### ChainObject

chain-object-snoc
  : {n : ℕ}
  → {X : ChainObject n}
  → DependentObject X
  → ChainObject (suc n)
chain-object-snoc {n = zero} X'
  = chain-object₁ X'
chain-object-snoc {n = suc _} {X = X} X'
  = record
  { ChainObject X
  ; tail
    = λ x → chain-object-snoc
      (DependentObject.tail X' x)
  }

-- ### ChainArrow

chain-arrow-snoc
  : {n : ℕ}
  → {X Y : ChainObject n}
  → {X' : DependentObject X}
  → {Y' : DependentObject Y}
  → ChainArrow X Y
  → DependentArrow X' Y'
  → ChainArrow
    (chain-object-snoc X')
    (chain-object-snoc Y')
chain-arrow-snoc {n = zero} _ F'
  = chain-arrow₁ F'
chain-arrow-snoc {n = suc _} F F'
  = record
  { ChainArrow F
  ; tail
    = λ x y → chain-arrow-snoc
      (ChainArrow.tail F x y)
      (DependentArrow.tail F' x y)
  }

-- ### ChainIdentity

chain-identity-snoc
  : {n : ℕ}
  → {X : ChainObject n}
  → {X' : DependentObject X}
  → {F : ChainArrow X X}
  → {F' : DependentArrow X' X'}
  → ChainIdentity F
  → DependentIdentity F'
  → ChainIdentity
    (chain-arrow-snoc F F')
chain-identity-snoc {n = zero} _ i'
  = chain-identity₁ i'
chain-identity-snoc {n = suc _} i i'
  = record
  { ChainIdentity i
  ; tail
    = λ x → chain-identity-snoc
      (ChainIdentity.tail i x)
      (DependentIdentity.tail i' x)
  }

-- ### ChainCompose

chain-compose-snoc
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
  → ChainCompose F G H
  → DependentCompose F' G' H'
  → ChainCompose
    (chain-arrow-snoc F F')
    (chain-arrow-snoc G G')
    (chain-arrow-snoc H H')
chain-compose-snoc {n = zero} _ j'
  = chain-compose₁ j'
chain-compose-snoc {n = suc _} j j'
  = record
  { ChainCompose j
  ; tail
    = λ x y z → chain-compose-snoc
      (ChainCompose.tail j x y z)
      (DependentCompose.tail j' x y z)
  }

