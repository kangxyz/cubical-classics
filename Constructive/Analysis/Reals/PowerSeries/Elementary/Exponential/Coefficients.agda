{-

Part of Constructive.Analysis.Reals.PowerSeries.Elementary.Exponential

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Exponential.Coefficients where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (scalarMulᶜ-nonnegative ; scalarMulᶜ-pres≤ᶜ-scalar)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-refl)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.DerivativeData
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.Calculus.DerivativeRules
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.GeometricDecay
open import Constructive.Analysis.Reals.Series.Geometric.Positive
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( centeredPowerSeriesSumEverywhere-center
    ; constantPowerSeries
    ; constantPowerSeriesInfiniteRadius
    ; rationalScaleModulus
    ; rationalScaleModulus-antitone
    ; rationalScalePrecision
    ; rationalScalePrecision-mono
    ; rationalScaleTailBound
    ; subPowerSeries
    ; subPowerSeriesInfiniteRadius
    )
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using
    ( derivativePowerSeries
    ; inverseSucReal
    ; naturalTimesInverseSucReal-cancel
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds.Coefficients
  using
    ( reciprocalFactorial⁺
    ; reciprocalFactorialClosedBoundOne
    ; reciprocalFactorialClosedBoundSelf
    )
open import Constructive.Data.PositiveRationals
  using
    ( ℚ⁺
    ; 1⁺
    ; _+⁺_
    ; _*⁺_
    ; *⁺-comm
    ; *⁺-identity-left
    ; half⁺
    ; half<
    ; radius
    ; scalar-bound
    )
import Constructive.Data.Rationals.Base as RationalBase
import Constructive.Data.Rationals.Archimedean as Rational
import Constructive.Data.Rationals.Factorial as Factorial
import Constructive.Data.Rationals.Multiplication as RationalMul

expPowerSeries :
  PowerSeries
expPowerSeries zero =
  1ᶜ
expPowerSeries (suc n) =
  inverseSucReal n ·ᶜ expPowerSeries n


inverseSucReal-rational :
  (n : ℕ) →
  (q : ℚ) →
  inverseSucReal n ·ᶜ rational q ≡
  rational (Rational.divideBySuc q n)
inverseSucReal-rational n q =
  mulᶜ-rational-rational inverse q ∙
  cong rational inverse-times-q≡q-div
  where
  inverse : ℚ
  inverse =
    Rational.divideBySuc RationalBase.1ℚ n

  unit : ℚ
  unit =
    Rational.unitFraction n

  inverse≡unit : inverse ≡ unit
  inverse≡unit =
    Rational.divideBySuc-as-unitFraction RationalBase.1ℚ n ∙
    ℚ.·IdL unit

  inverse-times-q≡q-div :
    inverse ℚ.· q ≡ Rational.divideBySuc q n
  inverse-times-q≡q-div =
    cong (λ r → r ℚ.· q) inverse≡unit ∙
    ℚ.·Comm unit q ∙
    sym (Rational.divideBySuc-as-unitFraction q n)


expPowerSeries-reciprocalFactorial :
  (n : ℕ) →
  expPowerSeries n ≡
  rational (Factorial.reciprocalFactorial n)
expPowerSeries-reciprocalFactorial zero =
  refl
expPowerSeries-reciprocalFactorial (suc n) =
  cong
    (inverseSucReal n ·ᶜ_)
    (expPowerSeries-reciprocalFactorial n) ∙
  inverseSucReal-rational n (Factorial.reciprocalFactorial n)


expPowerSeriesCoefficientBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (expPowerSeries n)
expPowerSeriesCoefficientBoundOne n =
  subst
    (BoundedByᶜ 1⁺)
    (sym (expPowerSeries-reciprocalFactorial n))
    (rational-closed-bound→boundedᶜ
      1⁺
      (Factorial.reciprocalFactorial n)
      (reciprocalFactorialClosedBoundOne n))
