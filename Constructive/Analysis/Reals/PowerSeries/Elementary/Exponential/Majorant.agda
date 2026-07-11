{-

Factorial majorization of exponential power-series terms

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Exponential.Majorant where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)

open import Constructive.Analysis.GeometricDecay using (positivePower)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using (_·ᶜ_ ; mulᶜ-rational-left)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Quantitative
  using (bounded-byᶜ-scale-rational-closed-bound)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
  using (scalarMulᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Exponential.Coefficients
  using
    ( expPowerSeries
    ; expPowerSeries-reciprocalFactorial
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds.Coefficients
  using
    ( reciprocalFactorial⁺
    ; reciprocalFactorialClosedBoundSelf
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds.Majorant
  using (factorialMajorantRadius)
open import Constructive.Data.PositiveRationals
  using (ℚ⁺ ; *⁺-comm)
import Constructive.Data.Rationals.Factorial as Factorial


expPowerSeriesTerm-scalarReciprocal :
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm expPowerSeries h n ≡
  scalarMulᶜ (Factorial.reciprocalFactorial n) (realPower h n)
expPowerSeriesTerm-scalarReciprocal h n =
  cong
    (_·ᶜ realPower h n)
    (expPowerSeries-reciprocalFactorial n) ∙
  mulᶜ-rational-left
    (Factorial.reciprocalFactorial n)
    (realPower h n)


expPowerSeriesTermBoundByFactorialMajorant :
  (ρ : ℚ⁺) →
  (h : ℝᶜ) →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n) →
  BoundedByᶜ (factorialMajorantRadius ρ n)
    (powerSeriesTerm expPowerSeries h n)
expPowerSeriesTermBoundByFactorialMajorant ρ h n powerBound =
  subst2
    BoundedByᶜ
    (*⁺-comm (reciprocalFactorial⁺ n) (positivePower ρ n))
    (sym (expPowerSeriesTerm-scalarReciprocal h n))
    (bounded-byᶜ-scale-rational-closed-bound
      (Factorial.reciprocalFactorial n)
      (positivePower ρ n)
      (reciprocalFactorial⁺ n)
      (realPower h n)
      (reciprocalFactorialClosedBoundSelf n)
      powerBound)
