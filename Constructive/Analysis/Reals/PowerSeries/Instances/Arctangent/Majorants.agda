{-

Subunit-ball majorants for atanh and atan

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Majorants where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (≤ᶜ-refl)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using
    ( positiveGeometricFiniteTailBoundFromRatio
    ; positiveGeometricPowerModulus
    ; positiveGeometricPowerModulus-antitone
    ; positiveGeometricTerm
    ; positiveGeometricTerm-nonnegative
    ; positivePower
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using
    ( RealGeometricBound
    ; RealGeometricPowerBounds
    ; realGeometricPowerBoundsFromBound
    ; realPower
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Coefficients
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


UnitCoefficientPowerBoundsOnBall :
  ℚ⁺ →
  Type₀
UnitCoefficientPowerBoundsOnBall ρ =
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n)


unitCoefficientPowerSeriesMajorizedOnBallFromPowerBounds :
  (a : PowerSeries) →
  ((n : ℕ) → BoundedByᶜ 1⁺ (a n)) →
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  UnitCoefficientPowerBoundsOnBall ρ →
  PowerSeriesMajorizedOnBall
    a
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
unitCoefficientPowerSeriesMajorizedOnBallFromPowerBounds
    a coefficientBound ρ ρ<1 powerBounds =
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
        (powerBounds h h-bound n))
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


unitCoefficientPowerSeriesPowerBoundsFromBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  UnitCoefficientPowerBoundsOnBall ρ
unitCoefficientPowerSeriesPowerBoundsFromBall ρ ρ<1 h h-bound n =
  RealGeometricPowerBounds.powerBound
    (realGeometricPowerBoundsFromBound h bound)
    n
  where
  bound : RealGeometricBound h
  bound =
    ρ , ρ<1 , h-bound


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
  unitCoefficientPowerSeriesMajorizedOnBallFromPowerBounds
    a
    coefficientBound
    ρ
    ρ<1
    (unitCoefficientPowerSeriesPowerBoundsFromBall ρ ρ<1)


evenGeometricPowerSeriesMajorizedOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PowerSeriesMajorizedOnBall
    evenGeometricPowerSeries
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
evenGeometricPowerSeriesMajorizedOnBall =
  unitCoefficientPowerSeriesMajorizedOnBall
    evenGeometricPowerSeries
    evenGeometricPowerSeriesCoefficientBoundOne


alternatingEvenGeometricPowerSeriesMajorizedOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PowerSeriesMajorizedOnBall
    alternatingEvenGeometricPowerSeries
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
alternatingEvenGeometricPowerSeriesMajorizedOnBall =
  unitCoefficientPowerSeriesMajorizedOnBall
    alternatingEvenGeometricPowerSeries
    alternatingEvenGeometricPowerSeriesCoefficientBoundOne


atanhPowerSeriesMajorizedOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PowerSeriesMajorizedOnBall
    atanhPowerSeries
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
atanhPowerSeriesMajorizedOnBall =
  unitCoefficientPowerSeriesMajorizedOnBall
    atanhPowerSeries
    atanhPowerSeriesCoefficientBoundOne


atanPowerSeriesMajorizedOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PowerSeriesMajorizedOnBall
    atanPowerSeries
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
atanPowerSeriesMajorizedOnBall =
  unitCoefficientPowerSeriesMajorizedOnBall
    atanPowerSeries
    atanPowerSeriesCoefficientBoundOne
