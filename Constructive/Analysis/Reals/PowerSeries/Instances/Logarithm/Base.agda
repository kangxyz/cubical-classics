{-

Formal logarithm power-series coefficients

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (_,_)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Estimates
  using (bounded-byᶜ-abs≤rational)
open import Constructive.Analysis.GeometricDecay
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using
    ( realPower
    ; realPowerBoundsFromBound
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using (centeredPowerSeriesSumOnBall-center)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; inverseSucReal
    ; naturalTimesInverseSucReal-cancel
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Geometric
  using
    ( alternatingGeometricPowerSeries
    ; alternatingGeometricPowerSeriesRadius
    )
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative
  using
    ( PowerSeriesIteratedFormalPartialDerivativeBounds
    ; positivePartialSum
    ; powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    )
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using
    ( AnalyticWithinAt
    ; HasPowerSeriesWithinAtWith
    ; centeredPowerSeriesWithinBallAnalyticWithinAt
    ; centeredPowerSeriesWithinBallFunction
    ; centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational
import Constructive.Data.Rationals.Factorial as Factorial


logOnePlusPowerSeries :
  PowerSeries
logOnePlusPowerSeries zero =
  0ᶜ
logOnePlusPowerSeries (suc n) =
  inverseSucReal n ·ᶜ alternatingGeometricPowerSeries n


logOnePlusPowerSeriesCoefficient-zero :
  logOnePlusPowerSeries zero ≡ 0ᶜ
logOnePlusPowerSeriesCoefficient-zero =
  refl


derivativePowerSeries-logOnePlus :
  (n : ℕ) →
  derivativePowerSeries logOnePlusPowerSeries n ≡
  alternatingGeometricPowerSeries n
derivativePowerSeries-logOnePlus n =
  naturalTimesInverseSucReal-cancel
    n
    (alternatingGeometricPowerSeries n)


logZeroBoundOne :
  BoundedByᶜ 1⁺ 0ᶜ
logZeroBoundOne =
  rational-closed-bound→boundedᶜ
    1⁺
    Rational.0ℚ
    (rational-closed-boundᶜ 0≤1 0≤1)
  where
  0≤1 :
    Rational.0ℚ ℚOrder.≤ Rational.1ℚ
  0≤1 =
    Rational.<→≤
      {p = Rational.0ℚ}
      {q = Rational.1ℚ}
      Rational.0<1


logOneBoundOne :
  BoundedByᶜ 1⁺ 1ᶜ
logOneBoundOne =
  rational-closed-bound→boundedᶜ
    1⁺
    Rational.1ℚ
    (rational-closed-boundᶜ 1≤1 -1≤1)
  where
  1≤1 :
    Rational.1ℚ ℚOrder.≤ Rational.1ℚ
  1≤1 =
    Rational.≤-refl Rational.1ℚ

  -1≤1 :
    ℚ.- Rational.1ℚ ℚOrder.≤ Rational.1ℚ
  -1≤1 =
    Rational.<→≤
      {p = Rational.-1ℚ}
      {q = Rational.1ℚ}
      (ℚOrder.isTrans<
        Rational.-1ℚ
        Rational.0ℚ
        Rational.1ℚ
        Rational.-1<0
        Rational.0<1)


logInverseSucRealBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (inverseSucReal n)
logInverseSucRealBoundOne n =
  rational-closed-bound→boundedᶜ
    1⁺
    inverse
    (rational-closed-boundᶜ inverse≤1 negative≤1)
  where
  inverse : ℚ
  inverse =
    Rational.divideBySuc Rational.1ℚ n

  unit : ℚ
  unit =
    Rational.unitFraction n

  inverse≡unit :
    inverse ≡ unit
  inverse≡unit =
    Rational.divideBySuc-as-unitFraction Rational.1ℚ n ∙
    ℚ.·IdL unit

  inverse≤1 :
    inverse ℚOrder.≤ Rational.1ℚ
  inverse≤1 =
    subst
      (λ q → q ℚOrder.≤ Rational.1ℚ)
      (sym inverse≡unit)
      (Factorial.unitFraction≤1 n)

  inverseNonnegative :
    Rational.0ℚ ℚOrder.≤ inverse
  inverseNonnegative =
    Rational.<→≤
      {p = Rational.0ℚ}
      {q = inverse}
      (Rational.divideBySuc-positive
        {q = Rational.1ℚ}
        Rational.0<1
        n)

  negative≤0 :
    ℚ.- inverse ℚOrder.≤ Rational.0ℚ
  negative≤0 =
    Rational.neg-nonpositive
      {q = inverse}
      inverseNonnegative

  0≤1 :
    Rational.0ℚ ℚOrder.≤ Rational.1ℚ
  0≤1 =
    Rational.<→≤
      {p = Rational.0ℚ}
      {q = Rational.1ℚ}
      Rational.0<1

  negative≤1 :
    ℚ.- inverse ℚOrder.≤ Rational.1ℚ
  negative≤1 =
    Rational.≤-trans
      {p = ℚ.- inverse}
      {q = Rational.0ℚ}
      {r = Rational.1ℚ}
      negative≤0
      0≤1


alternatingGeometricPowerSeriesCoefficientBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (alternatingGeometricPowerSeries n)
alternatingGeometricPowerSeriesCoefficientBoundOne zero =
  logOneBoundOne
alternatingGeometricPowerSeriesCoefficientBoundOne (suc n) =
  bounded-byᶜ-neg
    1⁺
    (alternatingGeometricPowerSeries n)
    (alternatingGeometricPowerSeriesCoefficientBoundOne n)


logOnePlusPowerSeriesCoefficientBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (logOnePlusPowerSeries n)
logOnePlusPowerSeriesCoefficientBoundOne zero =
  logZeroBoundOne
logOnePlusPowerSeriesCoefficientBoundOne (suc n) =
  subst
    (λ κ → BoundedByᶜ κ (logOnePlusPowerSeries (suc n)))
    (*⁺-identity-left 1⁺)
    (bounded-byᶜ-mul
      1⁺
      1⁺
      (inverseSucReal n)
      (alternatingGeometricPowerSeries n)
      (logInverseSucRealBoundOne n)
      (alternatingGeometricPowerSeriesCoefficientBoundOne n))


logOnePlusPowerSeriesTermBoundFromPowerBound :
  (ρ : ℚ⁺) →
  (h : ℝᶜ) →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n) →
  BoundedByᶜ (positivePower ρ n) (powerSeriesTerm logOnePlusPowerSeries h n)
logOnePlusPowerSeriesTermBoundFromPowerBound ρ h n powerBound =
  subst
    (λ κ → BoundedByᶜ κ (powerSeriesTerm logOnePlusPowerSeries h n))
    (*⁺-identity-left (positivePower ρ n))
    (bounded-byᶜ-mul
      1⁺
      (positivePower ρ n)
      (logOnePlusPowerSeries n)
      (realPower h n)
      (logOnePlusPowerSeriesCoefficientBoundOne n)
      powerBound)


logOnePlusPowerSeriesMajorizedOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PowerSeriesMajorizedOnBall
    logOnePlusPowerSeries
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
logOnePlusPowerSeriesMajorizedOnBall ρ ρ<1 =
  termMajorant ,
  (λ ε m k μ≤m →
    positiveGeometricFiniteTailBoundFromRatio ρ ρ<1 ε m k μ≤m) ,
  (λ {ε} {δ} ε≤δ →
    positiveGeometricPowerModulus-antitone
      ρ
      ρ<1
      {ε = ε}
      {δ = δ}
      ε≤δ)
  where
  termMajorant :
    (h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy
      (powerSeriesTerm logOnePlusPowerSeries h)
      (positiveGeometricTerm ρ)
  termMajorant h h-bound =
    seriesMajorizedByTerms
      (λ n →
        bounded-byᶜ-abs≤rational
          (logOnePlusPowerSeriesTermBoundFromPowerBound
            ρ
            h
            n
            (realPowerBoundsFromBound ρ h h-bound n)))
      (positiveGeometricTerm-nonnegative ρ)


logOnePlusPowerSeriesOnSubunitBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBallWith
    logOnePlusPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
logOnePlusPowerSeriesOnSubunitBallWith ρ ρ<1 =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (logOnePlusPowerSeriesMajorizedOnBall ρ ρ<1)


logOnePlusᶜWithinSubunitBall :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  (x : ℝᶜ) →
  InPowerSeriesBall 0ᶜ ρ x →
  ℝᶜ
logOnePlusᶜWithinSubunitBall ρ ρ<1 =
  centeredPowerSeriesWithinBallFunction
    logOnePlusPowerSeries
    0ᶜ
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (logOnePlusPowerSeriesOnSubunitBallWith ρ ρ<1)


logOnePlusᶜWithinSubunitBall-zero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (zero-inBall : InPowerSeriesBall 0ᶜ ρ 0ᶜ) →
  logOnePlusᶜWithinSubunitBall ρ ρ<1 0ᶜ zero-inBall ≡ 0ᶜ
logOnePlusᶜWithinSubunitBall-zero ρ ρ<1 zero-inBall =
  centeredPowerSeriesSumOnBall-center
    (logOnePlusPowerSeriesOnSubunitBallWith ρ ρ<1)
    0ᶜ
    zero-inBall
