{-

Ordered commutative ring structure for constructive Dedekind cuts.

This package is deliberately weaker than the existing `StrictlyOrderedCommRing`
interface used by ordered fields: it does not include trichotomy, so it remains
valid without LEM.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.DedekindCut.Arithmetic.OrderedCommRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Nullary

open import Cubical.DedekindCut
open import Cubical.DedekindCut.Arithmetic
open import Cubical.DedekindCut.Arithmetic.CommRing
open import Cubical.DedekindCut.Arithmetic.Order


module DedekindOrderedCommRing {ℓ : Level} where
  open Order {ℓ}
  open Lattice {ℓ}
  open RationalEmbeddingAt {ℓ}
  open Algebra {ℓ}
  open Addition {ℓ}
  open SignedMultiplication {ℓ}
  open DedekindCommRing {ℓ}
  open SignedOrder {ℓ}

  DedekindCut≤Poset : Poset (ℓ-suc ℓ) ℓ
  DedekindCut≤Poset =
    poset (DedekindCut ℓ) _≤_
      (isposet isSetDedekindCut isProp≤ ≤-refl ≤-trans ≤-antisym)

  DedekindCut≤Pseudolattice : Pseudolattice (ℓ-suc ℓ) ℓ
  DedekindCut≤Pseudolattice =
    makePseudolatticeFromPoset DedekindCut≤Poset _⊓_ _⊔_
      (λ {a} {b} → ⊓≤left a b)
      (λ {a} {b} → ⊓≤right a b)
      (λ {a} {b} {x} → ≤⊓ x a b)
      (λ {a} {b} → left≤⊔ a b)
      (λ {a} {b} → right≤⊔ a b)
      (λ {a} {b} {x} → ⊔≤ a b x)

  DedekindCutIsOrderedCommRing :
    IsOrderedCommRing 0D 1D _+_ _*_ (-_) _<_ _≤_
  DedekindCutIsOrderedCommRing .IsOrderedCommRing.isCommRing =
    DedekindCutCommRing .snd .CommRingStr.isCommRing
  DedekindCutIsOrderedCommRing .IsOrderedCommRing.isPseudolattice =
    DedekindCut≤Pseudolattice .snd .PseudolatticeStr.is-pseudolattice
  DedekindCutIsOrderedCommRing .IsOrderedCommRing.isStrictOrder =
    isStrictOrder<
  DedekindCutIsOrderedCommRing .IsOrderedCommRing.<-≤-weaken =
    <→≤
  DedekindCutIsOrderedCommRing .IsOrderedCommRing.≤≃¬> =
    λ x y →
      propBiimpl→Equiv (isProp≤ x y) (isProp¬ (y < x))
        (≤→¬> x y)
        (¬>→≤ x y)
  DedekindCutIsOrderedCommRing .IsOrderedCommRing.+MonoR≤ =
    +-monoR-≤
  DedekindCutIsOrderedCommRing .IsOrderedCommRing.+MonoR< =
    +-monoR-<
  DedekindCutIsOrderedCommRing .IsOrderedCommRing.posSum→pos∨pos =
    positive-sum-split
  DedekindCutIsOrderedCommRing .IsOrderedCommRing.<-≤-trans =
    <-≤-trans
  DedekindCutIsOrderedCommRing .IsOrderedCommRing.≤-<-trans =
    ≤-<-trans
  DedekindCutIsOrderedCommRing .IsOrderedCommRing.·MonoR≤ =
    λ x y z 0≤z x≤y → *-monoR-≤-nonnegative x y z x≤y 0≤z
  DedekindCutIsOrderedCommRing .IsOrderedCommRing.·MonoR< =
    *-monoR-<-positive
  DedekindCutIsOrderedCommRing .IsOrderedCommRing.0<1 =
    0<1-cut

  DedekindCutOrderedCommRing : OrderedCommRing (ℓ-suc ℓ) ℓ
  DedekindCutOrderedCommRing .fst = DedekindCut ℓ
  DedekindCutOrderedCommRing .snd =
    orderedcommringstr 0D 1D _+_ _*_ (-_) _<_ _≤_ DedekindCutIsOrderedCommRing
