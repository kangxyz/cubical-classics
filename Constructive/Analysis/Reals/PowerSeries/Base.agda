{-

Power series over HoTT Cauchy reals

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower)
open import Constructive.Data.PositiveRationals


PowerSeries : Type₀
PowerSeries =
  ℕ → ℝᶜ


powerSeriesTerm :
  PowerSeries →
  ℝᶜ →
  ℕ →
  ℝᶜ
powerSeriesTerm a h n =
  a n ·ᶜ realPower h n


powerSeriesPartialSum :
  PowerSeries →
  ℝᶜ →
  ℕ →
  ℝᶜ
powerSeriesPartialSum a h =
  partialSum (powerSeriesTerm a h)


powerSeriesTerm-cong :
  {a b : PowerSeries} →
  {h k : ℝᶜ} →
  ((n : ℕ) → a n ≡ b n) →
  h ≡ k →
  powerSeriesTerm a h ≡ powerSeriesTerm b k
powerSeriesTerm-cong {h = h} {k = k} coeff h≡k =
  funExt λ n →
    cong₂
      _·ᶜ_
      (coeff n)
      (cong (λ x → realPower x n) h≡k)


powerSeriesTerm-cong-coefficients :
  {a b : PowerSeries} →
  ((n : ℕ) → a n ≡ b n) →
  (h : ℝᶜ) →
  powerSeriesTerm a h ≡ powerSeriesTerm b h
powerSeriesTerm-cong-coefficients {a = a} {b = b} coeff h =
  powerSeriesTerm-cong {a = a} {b = b} {h = h} {k = h} coeff refl




powerSeriesPartialSum-cong :
  {a b : PowerSeries} →
  {h k : ℝᶜ} →
  ((n : ℕ) → a n ≡ b n) →
  h ≡ k →
  (n : ℕ) →
  powerSeriesPartialSum a h n ≡ powerSeriesPartialSum b k n
powerSeriesPartialSum-cong coeff h≡k n =
  cong
    (λ u → partialSum u n)
    (powerSeriesTerm-cong coeff h≡k)


PowerSeriesTailBound :
  PowerSeries →
  ℝᶜ →
  (ℚ⁺ → ℕ) →
  Type₀
PowerSeriesTailBound a h μ =
  TailBound (powerSeriesTerm a h) μ




powerSeriesSumFromFiniteTailBound :
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  PowerSeriesTailBound a h μ →
  AntitoneNatModulus μ →
  ℝᶜ
powerSeriesSumFromFiniteTailBound a h μ tailBound μ-antitone =
  seriesSumFromFiniteTailBound
    (powerSeriesTerm a h)
    μ
    tailBound
    μ-antitone


powerSeriesConvergesFromFiniteTailBound :
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : PowerSeriesTailBound a h μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (powerSeriesTerm a h)
      μ
      tailBound
      μ-antitone)
    (powerSeriesSumFromFiniteTailBound a h μ tailBound μ-antitone)
powerSeriesConvergesFromFiniteTailBound a h μ tailBound μ-antitone =
  seriesSumFromFiniteTailBoundConverges
    (powerSeriesTerm a h)
    μ
    tailBound
    μ-antitone
