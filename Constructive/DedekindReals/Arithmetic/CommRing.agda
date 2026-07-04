{-

Commutative ring structure for constructive Dedekind reals

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindReals.Arithmetic.CommRing where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing

open import Constructive.DedekindReals
open import Constructive.DedekindReals.Arithmetic.Base
open import Constructive.DedekindReals.Arithmetic.Associativity
open import Constructive.DedekindReals.Arithmetic.Distributivity
open import Constructive.DedekindReals.Arithmetic.Unit


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
      isSetDedekindReal
      +-assoc
      +-idR
      +-invR
      +-comm
      (λ x y z → sym (*-assoc x y z))
      *-idR
      *-distribL
      *-comm
