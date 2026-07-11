{-

Geometric majorants for unit-bounded coefficient streams

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.SubunitMajorant where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.GeometricDecay
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (≤ᶜ-refl)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Convergence
  using (HasPowerSeriesOnBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using
    ( PowerSeriesMajorizedOnBall
    ; majorizedOnBall→hasPowerSeriesOnBallWith
    ; powerSeriesMajorizedOnBallFromBoundedTerms
    )
open import Constructive.Analysis.Reals.Series.Geometric.Positive
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


unitCoefficientPowerSeriesTermBoundFromPowerBound :
  (a : PowerSeries) →
  ((n : ℕ) → BoundedByᶜ 1⁺ (a n)) →
  (ρ : ℚ⁺) →
  (h : ℝᶜ) →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n) →
  BoundedByᶜ (positivePower ρ n) (powerSeriesTerm a h n)
unitCoefficientPowerSeriesTermBoundFromPowerBound
    a coefficientBound ρ h n powerBound =
  subst
    (λ κ → BoundedByᶜ κ (powerSeriesTerm a h n))
    (*⁺-identity-left (positivePower ρ n))
    (bounded-byᶜ-mul
      1⁺
      (positivePower ρ n)
      (a n)
      (realPower h n)
      (coefficientBound n)
      powerBound)


unitCoefficientPowerSeriesMajorizedOnBall :
  (a : PowerSeries) →
  ((n : ℕ) → BoundedByᶜ 1⁺ (a n)) →
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PowerSeriesMajorizedOnBall
    a
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
unitCoefficientPowerSeriesMajorizedOnBall a coefficientBound ρ ρ<1 =
  powerSeriesMajorizedOnBallFromBoundedTerms
    {a = a}
    {ρ = ρ}
    {κ = positivePower ρ}
    {v = positiveGeometricTerm ρ}
    (λ h h-bound n →
      unitCoefficientPowerSeriesTermBoundFromPowerBound
        a
        coefficientBound
        ρ
        h
        n
        (realPowerBoundsFromBound ρ h h-bound n))
    (λ n → ≤ᶜ-refl (positiveGeometricTerm ρ n))
    (positiveGeometricTerm-nonnegative ρ)
    (λ ε m k μ≤m →
      positiveGeometricFiniteTailBoundFromRatio ρ ρ<1 ε m k μ≤m)
    (λ {ε} {δ} ε≤δ →
      positiveGeometricPowerModulus-antitone
        ρ
        ρ<1
        {ε = ε}
        {δ = δ}
        ε≤δ)


unitCoefficientPowerSeriesOnSubunitBallWith :
  (a : PowerSeries) →
  ((n : ℕ) → BoundedByᶜ 1⁺ (a n)) →
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBallWith
    a
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
unitCoefficientPowerSeriesOnSubunitBallWith a coefficientBound ρ ρ<1 =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (unitCoefficientPowerSeriesMajorizedOnBall
      a
      coefficientBound
      ρ
      ρ<1)
