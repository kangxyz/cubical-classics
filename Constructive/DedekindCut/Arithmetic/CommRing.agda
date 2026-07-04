{-

Commutative ring packaging for constructive Dedekind cuts.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindCut.Arithmetic.CommRing where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing

open import Constructive.DedekindCut
open import Constructive.DedekindCut.Arithmetic.Base
open import Constructive.DedekindCut.Arithmetic.Associativity
open import Constructive.DedekindCut.Arithmetic.Distributivity
open import Constructive.DedekindCut.Arithmetic.Unit


module CommRingStructure {ℓ : Level} where
  open Algebra {ℓ}
  open Addition {ℓ}
  open Multiplication {ℓ}
  open MultiplicationAssociativity {ℓ}
  open MultiplicationDistributivity {ℓ}
  open UnitProperties {ℓ}

  DedekindCommRing : CommRing (ℓ-suc ℓ)
  DedekindCommRing =
    makeCommRing
      0𝔻
      1𝔻
      _+_
      _*_
      -_
      isSetDedekindCut
      +-assoc
      +-idR
      +-invR
      +-comm
      (λ x y z → sym (*-assoc x y z))
      *-idR
      *-distribL
      *-comm
