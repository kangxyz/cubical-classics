{-

Ordered commutative ring structure for constructive Dedekind reals.

This package is deliberately weaker than the existing `StrictlyOrderedCommRing`
interface used by ordered fields: it does not include trichotomy, so it remains
valid without LEM.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindReals.Arithmetic.OrderedCommRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Nullary

open import Constructive.DedekindReals
open import Constructive.DedekindReals.Arithmetic.Base
open import Constructive.DedekindReals.Arithmetic.CommRing
open import Constructive.DedekindReals.Arithmetic.Order


module OrderedCommRingStructure {ℓ : Level} where
  open Order {ℓ}
  open Lattice {ℓ}
  open RationalEmbedding {ℓ}
  open Algebra {ℓ}
  open Addition {ℓ}
  open Multiplication {ℓ}
  open CommRingStructure {ℓ}
  open OrderProperties {ℓ}

  DedekindIsOrderedCommRing :
    IsOrderedCommRing 0𝔻 1𝔻 _+_ _*_ (-_) _<_ _≤_
  DedekindIsOrderedCommRing .IsOrderedCommRing.isCommRing =
    DedekindCommRing .snd .CommRingStr.isCommRing
  DedekindIsOrderedCommRing .IsOrderedCommRing.isPseudolattice =
    Dedekind≤Pseudolattice .snd .PseudolatticeStr.is-pseudolattice
  DedekindIsOrderedCommRing .IsOrderedCommRing.isStrictOrder =
    isStrictOrder<
  DedekindIsOrderedCommRing .IsOrderedCommRing.<-≤-weaken =
    <→≤
  DedekindIsOrderedCommRing .IsOrderedCommRing.≤≃¬> =
    λ x y →
      propBiimpl→Equiv (isProp≤ x y) (isProp¬ (y < x))
        (≤→¬> x y)
        (¬>→≤ x y)
  DedekindIsOrderedCommRing .IsOrderedCommRing.+MonoR≤ =
    +-monoR-≤
  DedekindIsOrderedCommRing .IsOrderedCommRing.+MonoR< =
    +-monoR-<
  DedekindIsOrderedCommRing .IsOrderedCommRing.posSum→pos∨pos =
    posSum→pos∨pos
  DedekindIsOrderedCommRing .IsOrderedCommRing.<-≤-trans =
    <-≤-trans
  DedekindIsOrderedCommRing .IsOrderedCommRing.≤-<-trans =
    ≤-<-trans
  DedekindIsOrderedCommRing .IsOrderedCommRing.·MonoR≤ =
    λ x y z 0≤z x≤y → *-rPosPres≤ x y z x≤y 0≤z
  DedekindIsOrderedCommRing .IsOrderedCommRing.·MonoR< =
    *-rPosPres<
  DedekindIsOrderedCommRing .IsOrderedCommRing.0<1 =
    0𝔻<1𝔻

  DedekindOrderedCommRing : OrderedCommRing (ℓ-suc ℓ) ℓ
  DedekindOrderedCommRing .fst = DedekindReal ℓ
  DedekindOrderedCommRing .snd =
    orderedcommringstr 0𝔻 1𝔻 _+_ _*_ (-_) _<_ _≤_ DedekindIsOrderedCommRing
