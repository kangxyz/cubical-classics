{-

Formal hyperbolic-arctangent coefficient stream

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Coefficients where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using
    ( derivativePowerSeries
    ; derivativePrimitivePowerSeries
    ; primitivePowerSeries
    )


evenGeometricPowerSeries :
  PowerSeries
evenGeometricPowerSeries zero =
  1ᶜ
evenGeometricPowerSeries (suc zero) =
  0ᶜ
evenGeometricPowerSeries (suc (suc n)) =
  evenGeometricPowerSeries n


atanhPowerSeries :
  PowerSeries
atanhPowerSeries =
  primitivePowerSeries evenGeometricPowerSeries


atanhPowerSeriesCoefficient-zero :
  atanhPowerSeries zero ≡ 0ᶜ
atanhPowerSeriesCoefficient-zero =
  refl


derivativePowerSeries-atanh :
  (n : ℕ) →
  derivativePowerSeries atanhPowerSeries n ≡
  evenGeometricPowerSeries n
derivativePowerSeries-atanh =
  derivativePrimitivePowerSeries evenGeometricPowerSeries
