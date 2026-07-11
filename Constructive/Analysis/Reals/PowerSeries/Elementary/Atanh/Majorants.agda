{-

Subunit-ball majorants for hyperbolic arctangent

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Majorants where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (≤ᶜ-refl)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.GeometricDecay
open import Constructive.Analysis.Reals.Series.Geometric.Positive
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using
    ( realPower
    ; realPowerBoundsFromBound
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Elementary.SubunitMajorant
  using (unitCoefficientPowerSeriesMajorizedOnBall)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


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
