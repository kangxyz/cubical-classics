{-

Commutative ring structure for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace


CauchyRealsCommRing : CommRing ℓ-zero
CauchyRealsCommRing =
  makeCommRing 0ᶜ 1ᶜ _+ᶜ_ _·ᶜ_ -ᶜ_
    isSetCompletion
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
