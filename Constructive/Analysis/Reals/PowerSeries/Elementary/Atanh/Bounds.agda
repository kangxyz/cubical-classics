{-

Coefficient and finite-derivative bounds for atanh and atan

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Bounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.GeometricDecay
  using (positivePower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Bounds
  using (PowerSeriesCoefficientBounds)
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using (inverseSucReal ; primitivePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Elementary.CoefficientBounds
  using
    ( inverseSucRealBoundOne
    ; oneBoundOne
    ; primitivePowerSeriesCoefficientBoundOne
    ; zeroBoundOne
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


evenGeometricPowerSeriesCoefficientBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (evenGeometricPowerSeries n)
evenGeometricPowerSeriesCoefficientBoundOne zero =
  oneBoundOne
evenGeometricPowerSeriesCoefficientBoundOne (suc zero) =
  zeroBoundOne
evenGeometricPowerSeriesCoefficientBoundOne (suc (suc n)) =
  evenGeometricPowerSeriesCoefficientBoundOne n


atanhPowerSeriesCoefficientBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (atanhPowerSeries n)
atanhPowerSeriesCoefficientBoundOne =
  primitivePowerSeriesCoefficientBoundOne
    evenGeometricPowerSeries
    evenGeometricPowerSeriesCoefficientBoundOne


atanhPowerSeriesCoefficientBounds :
  PowerSeriesCoefficientBounds atanhPowerSeries
atanhPowerSeriesCoefficientBounds =
  (λ _ → 1⁺) ,
  atanhPowerSeriesCoefficientBoundOne
