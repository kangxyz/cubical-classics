{-

Limit passage for the finite prefix part of re-centering.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.PrefixLimit where

open import Cubical.Foundations.Prelude

import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Sigma using (fst ; snd)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using (_·ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.Series
  using (tailSum)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower)
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using (PowerSeriesMajorizedOnBall)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Base
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Binomial
  using (triangularRowsSumᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.FiniteLimits
  using
    ( boundedByClosedFromConvergentApproximants
    ; recenterOuterTailApprox
    ; recenterOuterTailApproxConvergesToTail
    )
open import Constructive.Analysis.Reals.PowerSeries.Recenter.StripFinite
  using (recenterPrefixTriangleDifferenceBoundFromMajorizedOnStrictSubball)
open import Constructive.Analysis.Reals.Sequences.Algebra as SeqAlg
  using (addConvergesTo ; negConvergesTo)
open import Constructive.Analysis.Reals.Sequences.Convergence
  using (ConvergesTo ; constantConvergesTo)
open import Constructive.Analysis.Reals.Sequences.Subsequence
  using (shiftConvergesWithModulus)
open import Constructive.Data.PositiveRationals
  using (ℚ⁺ ; radius ; _+⁺_)


recenterPrefixTriangleDifferenceBoundFromMajorizedOnStrictSubballLimit :
  {a : PowerSeries} →
  {δ τ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  {d h : ℝᶜ} →
  (recenterData : RecenterPowerSeriesData a d) →
  BoundedByᶜ δ d →
  BoundedByᶜ τ h →
  BoundedByᶜ σ (rational (radius (δ +⁺ τ))) →
  PowerSeriesMajorizedOnBall a σ v ν →
  (ε : ℚ⁺) →
  (m : ℕ) →
  NatOrder._≤_ (ν ε) m →
  BoundedByᶜ ε
    (powerSeriesPartialSum
      (recenterPowerSeriesWith a d recenterData)
      h
      m
     +ᶜ
     (-ᶜ
      triangularRowsSumᶜ
        (λ n k →
          recenterCoefficientTerm a d n k ·ᶜ
          realPower h n)
        m))
recenterPrefixTriangleDifferenceBoundFromMajorizedOnStrictSubballLimit
    {a = a}
    {δ = δ}
    {τ = τ}
    {σ = σ}
    {v = v}
    {ν = ν}
    {d = d}
    {h = h}
    recenterData
    d-bound
    h-bound
    probe-bound
    majorized
    ε
    m
    ν≤m =
  boundedByClosedFromConvergentApproximants
    ε
    difference-converges
    (λ N →
      recenterPrefixTriangleDifferenceBoundFromMajorizedOnStrictSubball
        d-bound
        h-bound
        probe-bound
        majorized
        ε
        m
        N
        ν≤m)
  where
  terms : ℕ → ℝᶜ
  terms =
    powerSeriesTerm (recenterPowerSeriesWith a d recenterData) h

  triangle : ℝᶜ
  triangle =
    triangularRowsSumᶜ
      (λ n k →
        recenterCoefficientTerm a d n k ·ᶜ
        realPower h n)
      m

  outer :
    ℕ →
    ℝᶜ
  outer N =
    recenterOuterTailApprox a d h zero m N

  shifted-outer-converges :
    ConvergesTo
      (λ N → recenterOuterTailApprox a d h zero m (m Nat.+ N))
      (tailSum terms zero m)
  shifted-outer-converges =
    fst (recenterOuterTailApproxConvergesToTail recenterData h-bound zero m) ,
    shiftConvergesWithModulus
      m
      (snd (recenterOuterTailApproxConvergesToTail recenterData h-bound zero m))

  difference-converges :
    ConvergesTo
      (λ N →
        recenterOuterTailApprox a d h zero m (m Nat.+ N) +ᶜ
        (-ᶜ triangle))
      (powerSeriesPartialSum
        (recenterPowerSeriesWith a d recenterData)
        h
        m
       +ᶜ
       (-ᶜ triangle))
  difference-converges =
    addConvergesTo
      shifted-outer-converges
      (negConvergesTo (constantConvergesTo triangle))
