{-

Entire convergence and zero-centered sum for the exponential series

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Convergence where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
  using (add-inverse-right ; add-zero-right)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
  using (0ᶜ ; 1ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (≤ᶜ-refl)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPowerBoundsFromBound)
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( centeredPowerSeriesSumEverywhere-center
    ; constantPowerSeries
    ; subPowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using
    ( HasPowerSeriesAtWith
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; naturalTimesInverseSucReal-cancel
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using
    ( PowerSeriesMajorizedOnBall
    ; majorizedOnBall→hasPowerSeriesOnBallWith
    ; powerSeriesMajorizedOnBallFromBoundedTerms
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals using (ℚ⁺)

open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Tail


derivativePowerSeries-exp :
  (n : ℕ) →
  derivativePowerSeries expPowerSeries n ≡ expPowerSeries n
derivativePowerSeries-exp n =
  naturalTimesInverseSucReal-cancel n (expPowerSeries n)


primitivePowerSeries-exp :
  (n : ℕ) →
  primitivePowerSeries expPowerSeries n ≡
  subPowerSeries expPowerSeries (constantPowerSeries 1ᶜ) n
primitivePowerSeries-exp zero =
  sym (add-inverse-right 1ᶜ)
primitivePowerSeries-exp (suc n) =
  sym (add-zero-right (expPowerSeries (suc n)))


expPowerSeriesFactorialMajorized :
  (ρ : ℚ⁺) →
  PowerSeriesMajorizedOnBall
    expPowerSeries
    ρ
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
expPowerSeriesFactorialMajorized ρ =
  powerSeriesMajorizedOnBallFromBoundedTerms
    {a = expPowerSeries}
    {ρ = ρ}
    {κ = expPositiveMajorantRadius ρ}
    {v = expPositiveMajorantTerm ρ}
    (λ h h-bound n →
      expPowerSeriesTermBoundByPositiveMajorant
        ρ
        h
        n
        (realPowerBoundsFromBound ρ h h-bound n))
    (λ n → ≤ᶜ-refl (expPositiveMajorantTerm ρ n))
    (expPositiveMajorantTerm-nonnegative ρ)
    (expPositiveMajorantFactorialTailBound ρ)
    (λ {ε} {δ} ε≤δ →
      expPositiveMajorantFactorialModulusAntitone
        ρ
        {ε = ε}
        {δ = δ}
        ε≤δ)


expPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius expPowerSeries
expPowerSeriesInfiniteRadius ρ =
  expPositiveMajorantFactorialModulus ρ ,
  majorizedOnBall→hasPowerSeriesOnBallWith
    (expPowerSeriesFactorialMajorized ρ)


expᶜ :
  ℝᶜ →
  ℝᶜ
expᶜ =
  centeredPowerSeriesSumEverywhere
    expPowerSeries
    0ᶜ
    expPowerSeriesInfiniteRadius


expᶜ-zero :
  expᶜ 0ᶜ ≡ 1ᶜ
expᶜ-zero =
  centeredPowerSeriesSumEverywhere-center
    expPowerSeriesInfiniteRadius
    0ᶜ


expᶜHasPowerSeriesAtWithZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtWith
    expᶜ
    0ᶜ
    expPowerSeries
    ρ
    (expPowerSeriesInfiniteRadius ρ .fst)
expᶜHasPowerSeriesAtWithZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    expPowerSeriesInfiniteRadius
