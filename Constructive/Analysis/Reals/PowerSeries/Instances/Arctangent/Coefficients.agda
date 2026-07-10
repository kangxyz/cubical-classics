{-

Formal atanh and atan coefficient streams

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Coefficients where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
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


alternatingEvenGeometricPowerSeries :
  PowerSeries
alternatingEvenGeometricPowerSeries zero =
  1ᶜ
alternatingEvenGeometricPowerSeries (suc zero) =
  0ᶜ
alternatingEvenGeometricPowerSeries (suc (suc n)) =
  -ᶜ alternatingEvenGeometricPowerSeries n


atanhPowerSeries :
  PowerSeries
atanhPowerSeries =
  primitivePowerSeries evenGeometricPowerSeries


atanPowerSeries :
  PowerSeries
atanPowerSeries =
  primitivePowerSeries alternatingEvenGeometricPowerSeries


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


derivativePowerSeries-atan :
  (n : ℕ) →
  derivativePowerSeries atanPowerSeries n ≡
  alternatingEvenGeometricPowerSeries n
derivativePowerSeries-atan =
  derivativePrimitivePowerSeries alternatingEvenGeometricPowerSeries
