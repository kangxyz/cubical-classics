{-

Uniform continuity of a power-series limit from its partial sums

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Continuity.Limit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as NatOrder

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.Series
  using (seriesSumFromFiniteTailBoundConvergesAt)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Continuity.PartialSums
  using (PowerSeriesPartialSumsUniformlyContinuousOnBallWith)
open import Constructive.Data.PositiveRationals


powerSeriesLimitApproximationIndex :
  (ℚ⁺ → ℕ) →
  ℚ⁺ →
  ℕ
powerSeriesLimitApproximationIndex μ ε =
  μ (quarter⁺ (half⁺ (quarter⁺ ε)))


powerSeriesSumUniformlyContinuousFromPartialSums :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {ν : PrecisionModulus} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBallWith a ρ χ ν →
  PowerSeriesSumUniformlyContinuousOnBallWith a ρ μ convergence ν
powerSeriesSumUniformlyContinuousFromPartialSums
  {a = a}
  {ρ = ρ}
  {μ = μ}
  {χ = χ}
  {convergence = convergence}
  index-large
  partial-cont
  ε
  {h = h}
  {k = k}
  h-bound
  k-bound
  h∼k =
  MetricSpace.close-mono
    CauchyRealsMetricSpace
    (three-quarter< ε)
    sum∼sum
  where
  τ : ℚ⁺
  τ =
    quarter⁺ ε

  n : ℕ
  n =
    χ ε

  tail-h :
    MetricSpace.Close CauchyRealsMetricSpace
      (powerSeriesSumOnBall a ρ μ convergence h h-bound)
      τ
      (powerSeriesPartialSum a h n)
  tail-h =
    seriesSumFromFiniteTailBoundConvergesAt
      (powerSeriesTerm a h)
      μ
      (HasPowerSeriesOnBallWith.tailBound convergence h h-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus convergence)
      τ
      n
      (index-large ε)

  partial-h∼k :
    MetricSpace.Close CauchyRealsMetricSpace
      (powerSeriesPartialSum a h n)
      τ
      (powerSeriesPartialSum a k n)
  partial-h∼k =
    partial-cont ε h-bound k-bound h∼k

  tail-k :
    MetricSpace.Close CauchyRealsMetricSpace
      (powerSeriesSumOnBall a ρ μ convergence k k-bound)
      τ
      (powerSeriesPartialSum a k n)
  tail-k =
    seriesSumFromFiniteTailBoundConvergesAt
      (powerSeriesTerm a k)
      μ
      (HasPowerSeriesOnBallWith.tailBound convergence k k-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus convergence)
      τ
      n
      (index-large ε)

  sum∼partial-k :
    MetricSpace.Close CauchyRealsMetricSpace
      (powerSeriesSumOnBall a ρ μ convergence h h-bound)
      (τ +⁺ τ)
      (powerSeriesPartialSum a k n)
  sum∼partial-k =
    MetricSpace.close-triangle
      CauchyRealsMetricSpace
      tail-h
      partial-h∼k

  sum∼sum :
    MetricSpace.Close CauchyRealsMetricSpace
      (powerSeriesSumOnBall a ρ μ convergence h h-bound)
      ((τ +⁺ τ) +⁺ τ)
      (powerSeriesSumOnBall a ρ μ convergence k k-bound)
  sum∼sum =
    MetricSpace.close-triangle
      CauchyRealsMetricSpace
      sum∼partial-k
      (MetricSpace.close-sym CauchyRealsMetricSpace tail-k)
