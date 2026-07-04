{-

Commutative ring packaging for constructive Dedekind cuts.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.DedekindCut.Arithmetic.CommRing where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing

open import Cubical.DedekindCut
open import Cubical.DedekindCut.Arithmetic
open import Cubical.DedekindCut.Arithmetic.Associativity
open import Cubical.DedekindCut.Arithmetic.Distributivity
open import Cubical.DedekindCut.Arithmetic.Unit


module DedekindCommRing {ℓ : Level} where
  open Algebra {ℓ}
  open Addition {ℓ}
  open SignedMultiplication {ℓ}
  open SignedAssociativity {ℓ}
  open SignedDistributivity {ℓ}
  open NonnegativeUnit {ℓ}

  DedekindCutCommRing : CommRing (ℓ-suc ℓ)
  DedekindCutCommRing =
    makeCommRing
      0D
      1D
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

