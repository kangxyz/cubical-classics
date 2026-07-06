{-

Commutative ring structure for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Arithmetic.CommRing where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing

open import Constructive.CauchyReals.Arithmetic.Addition
open import Constructive.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.CauchyReals.Arithmetic.Base
open import Constructive.CauchyReals.Arithmetic.Multiplication
open import Constructive.CauchyReals.Arithmetic.Negation
open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness


CauchyRealsCommRing : CommRing ℓ-zero
CauchyRealsCommRing =
  makeCommRing 0ᶜ 1ᶜ _+ᶜ_ _·ᶜ_ -ᶜ_
    isSetℝᶜ
    add-assoc
    add-zero-right
    add-inverse-right
    add-comm
    mulᶜ-assoc
    mulᶜ-one-right
    mulᶜ-distrib-right
    mulᶜ-comm


module CauchyRealsCommRingTheory =
  CommRingTheory CauchyRealsCommRing
