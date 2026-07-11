{-

Formal arctangent coefficient stream

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Arctangent.Coefficients where

open import Cubical.Foundations.Prelude using (_≡_)
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


alternatingEvenGeometricPowerSeries :
  PowerSeries
alternatingEvenGeometricPowerSeries zero =
  1ᶜ
alternatingEvenGeometricPowerSeries (suc zero) =
  0ᶜ
alternatingEvenGeometricPowerSeries (suc (suc n)) =
  -ᶜ alternatingEvenGeometricPowerSeries n


atanPowerSeries :
  PowerSeries
atanPowerSeries =
  primitivePowerSeries alternatingEvenGeometricPowerSeries


derivativePowerSeries-atan :
  (n : ℕ) →
  derivativePowerSeries atanPowerSeries n ≡
  alternatingEvenGeometricPowerSeries n
derivativePowerSeries-atan =
  derivativePrimitivePowerSeries alternatingEvenGeometricPowerSeries
