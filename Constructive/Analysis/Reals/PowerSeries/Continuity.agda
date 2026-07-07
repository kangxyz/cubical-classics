{-

Continuity criteria for power-series sums

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Continuity where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Metric.Instances.CauchyReals
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals


powerSeriesLimitApproximationIndex :
  (ℚ⁺ → ℕ) →
  ℚ⁺ →
  ℕ
powerSeriesLimitApproximationIndex μ ε =
  μ (quarter⁺ (half⁺ (quarter⁺ ε)))


PowerSeriesPartialSumsUniformlyContinuousOnBallWith :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (χ : ℚ⁺ → ℕ) →
  PrecisionModulus →
  Type₀
PowerSeriesPartialSumsUniformlyContinuousOnBallWith a ρ χ ν =
  (ε : ℚ⁺) →
  {h k : ℝᶜ} →
  (h-bound : BoundedByᶜ ρ h) →
  (k-bound : BoundedByᶜ ρ k) →
  MetricSpace.Close CauchyRealsMetricSpace h (ν ε) k →
  MetricSpace.Close CauchyRealsMetricSpace
    (powerSeriesPartialSum a h (χ ε))
    (quarter⁺ ε)
    (powerSeriesPartialSum a k (χ ε))


PowerSeriesPartialSumsUniformlyContinuousOnBall :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (χ : ℚ⁺ → ℕ) →
  Type₀
PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ =
  Σ[ ν ∈ PrecisionModulus ]
    PowerSeriesPartialSumsUniformlyContinuousOnBallWith a ρ χ ν


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


powerSeriesSumUniformlyContinuousFromPartialSumsΣ :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ →
  PowerSeriesSumUniformlyContinuousOnBall a ρ μ convergence
powerSeriesSumUniformlyContinuousFromPartialSumsΣ index-large (ν , partial-cont) =
  ν ,
  powerSeriesSumUniformlyContinuousFromPartialSums
    index-large
    partial-cont


powerSeriesSumContinuousAtFromPartialSums :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {ν : PrecisionModulus} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBallWith a ρ χ ν →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  PowerSeriesSumContinuousAtWith a ρ μ convergence h h-bound ν
powerSeriesSumContinuousAtFromPartialSums index-large partial-cont =
  uniformlyContinuousPowerSeriesSum→continuousAt
    (powerSeriesSumUniformlyContinuousFromPartialSums
      index-large
      partial-cont)


powerSeriesSumContinuousAtFromPartialSumsΣ :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  PowerSeriesSumContinuousAt a ρ μ convergence h h-bound
powerSeriesSumContinuousAtFromPartialSumsΣ index-large (ν , partial-cont) h h-bound =
  ν ,
  powerSeriesSumContinuousAtFromPartialSums
    index-large
    partial-cont
    h
    h-bound


centeredPowerSeriesSumUniformlyContinuousFromDisplacement :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {ν : PrecisionModulus} →
  PowerSeriesSumUniformlyContinuousOnBallWith a ρ μ convergence ν →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith a c ρ μ convergence ν
centeredPowerSeriesSumUniformlyContinuousFromDisplacement
  {c = c}
  uniform
  ε
  {x = x}
  {y = y}
  x-inBall
  y-inBall
  x∼y =
  uniform
    ε
    (InPowerSeriesBall.displacementBound x-inBall)
    (InPowerSeriesBall.displacementBound y-inBall)
    (add-close-left x∼y (-ᶜ c))


centeredPowerSeriesSumUniformlyContinuousFromDisplacementΣ :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  PowerSeriesSumUniformlyContinuousOnBall a ρ μ convergence →
  CenteredPowerSeriesSumUniformlyContinuousOnBall a c ρ μ convergence
centeredPowerSeriesSumUniformlyContinuousFromDisplacementΣ (ν , uniform) =
  ν ,
  centeredPowerSeriesSumUniformlyContinuousFromDisplacement uniform


centeredPowerSeriesSumUniformlyContinuousFromPartialSums :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {ν : PrecisionModulus} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBallWith a ρ χ ν →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith a c ρ μ convergence ν
centeredPowerSeriesSumUniformlyContinuousFromPartialSums index-large partial-cont =
  centeredPowerSeriesSumUniformlyContinuousFromDisplacement
    (powerSeriesSumUniformlyContinuousFromPartialSums
      index-large
      partial-cont)


centeredPowerSeriesSumUniformlyContinuousFromPartialSumsΣ :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ →
  CenteredPowerSeriesSumUniformlyContinuousOnBall a c ρ μ convergence
centeredPowerSeriesSumUniformlyContinuousFromPartialSumsΣ index-large partial-cont =
  centeredPowerSeriesSumUniformlyContinuousFromDisplacementΣ
    (powerSeriesSumUniformlyContinuousFromPartialSumsΣ
      index-large
      partial-cont)
