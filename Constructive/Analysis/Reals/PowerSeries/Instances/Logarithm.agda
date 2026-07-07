{-

Formal logarithm power-series coefficients

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm where

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
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Majorant
  using (bounded-byᶜ-abs)
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
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using (centeredPowerSeriesSumOnBall-center)
open import Constructive.Analysis.Reals.PowerSeries.Continuity
  using (PowerSeriesCoefficientBounds)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; inverseSucReal
    ; naturalTimesInverseSucReal-cancel
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence
  using
    ( derivativePowerSeriesRadiusFromCoefficientPath
    ; primitivePowerSeriesRadiusFromCoefficientPath
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
    ; HasPowerSeriesWithinAt
    ; HasPowerSeriesWithinAtContinuousAt
    ; HasPowerSeriesWithinAtOnBall
    ; HasPowerSeriesWithinAtUniformlyContinuousOnBall
    ; HasPowerSeriesWithinAtWith
    ; centeredPowerSeriesWithinBallAnalyticWithinAt
    ; centeredPowerSeriesWithinBallFunction
    ; centeredPowerSeriesWithinBallHasPowerSeriesWithinAt
    ; centeredPowerSeriesWithinBallHasPowerSeriesWithinAtOnBall
    ; centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith
    ; hasPowerSeriesWithinAtWith→continuousAtFromCoefficientBoundsCanonical
    ; hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonical
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


logOnePlusPowerSeriesCoefficient-suc :
  (n : ℕ) →
  logOnePlusPowerSeries (suc n) ≡
  inverseSucReal n ·ᶜ alternatingGeometricPowerSeries n
logOnePlusPowerSeriesCoefficient-suc n =
  refl


derivativePowerSeries-logOnePlus :
  (n : ℕ) →
  derivativePowerSeries logOnePlusPowerSeries n ≡
  alternatingGeometricPowerSeries n
derivativePowerSeries-logOnePlus n =
  naturalTimesInverseSucReal-cancel
    n
    (alternatingGeometricPowerSeries n)


primitivePowerSeries-alternatingGeometric-zero :
  primitivePowerSeries alternatingGeometricPowerSeries zero ≡
  logOnePlusPowerSeries zero
primitivePowerSeries-alternatingGeometric-zero =
  refl


primitivePowerSeries-alternatingGeometric-suc :
  (n : ℕ) →
  primitivePowerSeries alternatingGeometricPowerSeries (suc n) ≡
  logOnePlusPowerSeries (suc n)
primitivePowerSeries-alternatingGeometric-suc n =
  refl


primitivePowerSeries-alternatingGeometric :
  (n : ℕ) →
  primitivePowerSeries alternatingGeometricPowerSeries n ≡
  logOnePlusPowerSeries n
primitivePowerSeries-alternatingGeometric zero =
  refl
primitivePowerSeries-alternatingGeometric (suc n) =
  refl


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


logOnePlusPowerSeriesCoefficientBounds :
  PowerSeriesCoefficientBounds logOnePlusPowerSeries
logOnePlusPowerSeriesCoefficientBounds =
  (λ _ → 1⁺) ,
  logOnePlusPowerSeriesCoefficientBoundOne


logOnePlusPowerSeriesIteratedFormalPartialDerivativeBounds :
  (σ : ℚ⁺) →
  {x : ℝᶜ} →
  BoundedByᶜ σ x →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    logOnePlusPowerSeries
    x
    (λ s n →
      positivePartialSum
        (λ k →
          scalar-bound (Rational.natMul (suc k) Rational.1ℚ) *⁺
          1⁺ *⁺
          positivePower σ k)
        n)
logOnePlusPowerSeriesIteratedFormalPartialDerivativeBounds σ x-bound =
  powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    σ
    x-bound
    (λ _ → 1⁺)
    logOnePlusPowerSeriesCoefficientBoundOne


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


LogOnePlusGeometricMajorant :
  ℚ⁺ →
  Type₀
LogOnePlusGeometricMajorant ρ =
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  SeriesMajorizedBy
    (powerSeriesTerm logOnePlusPowerSeries h)
    (positiveGeometricTerm ρ)


LogOnePlusPowerBoundsOnBall :
  ℚ⁺ →
  Type₀
LogOnePlusPowerBoundsOnBall ρ =
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n)


logOnePlusPowerSeriesGeometricMajorantFromPowerBounds :
  (ρ : ℚ⁺) →
  LogOnePlusPowerBoundsOnBall ρ →
  LogOnePlusGeometricMajorant ρ
logOnePlusPowerSeriesGeometricMajorantFromPowerBounds ρ powerBounds h h-bound =
  seriesMajorizedByTerms
    (λ n →
      bounded-byᶜ-abs
        (logOnePlusPowerSeriesTermBoundFromPowerBound
          ρ
          h
          n
          (powerBounds h h-bound n)))
    (positiveGeometricTerm-nonnegative ρ)


logOnePlusPowerSeriesPowerBoundsFromBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  LogOnePlusPowerBoundsOnBall ρ
logOnePlusPowerSeriesPowerBoundsFromBall ρ ρ<1 h h-bound n =
  RealGeometricPowerBounds.powerBound
    (realGeometricPowerBoundsFromBound h bound)
    n
  where
  bound : RealGeometricBound h
  bound =
    record
      { ratioBound = ρ
      ; ratioBound<1 = ρ<1
      ; termBound = h-bound
      }


logOnePlusPowerSeriesGeometricMajorant :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  LogOnePlusGeometricMajorant ρ
logOnePlusPowerSeriesGeometricMajorant ρ ρ<1 =
  logOnePlusPowerSeriesGeometricMajorantFromPowerBounds
    ρ
    (logOnePlusPowerSeriesPowerBoundsFromBall ρ ρ<1)


logOnePlusPowerSeriesMajorizedOnBallFromGeometric :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  LogOnePlusGeometricMajorant ρ →
  PowerSeriesMajorizedOnBall
    logOnePlusPowerSeries
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
logOnePlusPowerSeriesMajorizedOnBallFromGeometric ρ ρ<1 majorant =
  majorant ,
  (λ ε m k μ≤m →
    positiveGeometricFiniteTailBoundFromRatio ρ ρ<1 ε m k μ≤m) ,
  (λ {ε} {δ} ε≤δ →
    positiveGeometricPowerModulus-antitone
      ρ
      ρ<1
      {ε = ε}
      {δ = δ}
      ε≤δ)


logOnePlusPowerSeriesMajorizedOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PowerSeriesMajorizedOnBall
    logOnePlusPowerSeries
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
logOnePlusPowerSeriesMajorizedOnBall ρ ρ<1 =
  logOnePlusPowerSeriesMajorizedOnBallFromGeometric
    ρ
    ρ<1
    (logOnePlusPowerSeriesGeometricMajorant ρ ρ<1)


logOnePlusPowerSeriesOnBallWithFromGeometricMajorant :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  LogOnePlusGeometricMajorant ρ →
  HasPowerSeriesOnBallWith
    logOnePlusPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
logOnePlusPowerSeriesOnBallWithFromGeometricMajorant ρ ρ<1 majorant =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (logOnePlusPowerSeriesMajorizedOnBallFromGeometric ρ ρ<1 majorant)


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


logOnePlusᶜHasPowerSeriesWithinAtWithZero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAtWith
    (logOnePlusᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    logOnePlusPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
logOnePlusᶜHasPowerSeriesWithinAtWithZero ρ ρ<1 =
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith
    logOnePlusPowerSeries
    0ᶜ
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (logOnePlusPowerSeriesOnSubunitBallWith ρ ρ<1)


logOnePlusᶜWithinSubunitBallUniformlyContinuousFromCoefficientBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall
    (logOnePlusᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    ρ
logOnePlusᶜWithinSubunitBallUniformlyContinuousFromCoefficientBounds
  ρ
  ρ<1 =
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonical
    (logOnePlusᶜHasPowerSeriesWithinAtWithZero ρ ρ<1)
    logOnePlusPowerSeriesCoefficientBounds


logOnePlusᶜWithinSubunitBallContinuousAtFromCoefficientBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall 0ᶜ ρ x) →
  HasPowerSeriesWithinAtContinuousAt
    (logOnePlusᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    ρ
    x
    x-inBall
    x-inBall
logOnePlusᶜWithinSubunitBallContinuousAtFromCoefficientBounds
  ρ
  ρ<1
  x
  x-inBall =
  hasPowerSeriesWithinAtWith→continuousAtFromCoefficientBoundsCanonical
    (logOnePlusᶜHasPowerSeriesWithinAtWithZero ρ ρ<1)
    logOnePlusPowerSeriesCoefficientBounds
    x
    x-inBall
    x-inBall


logOnePlusᶜHasPowerSeriesWithinAtOnBallZero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAtOnBall
    (logOnePlusᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    logOnePlusPowerSeries
    ρ
logOnePlusᶜHasPowerSeriesWithinAtOnBallZero ρ ρ<1 =
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAtOnBall
    logOnePlusPowerSeries
    0ᶜ
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (logOnePlusPowerSeriesOnSubunitBallWith ρ ρ<1)


logOnePlusᶜHasPowerSeriesWithinAtZero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAt
    (logOnePlusᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    logOnePlusPowerSeries
logOnePlusᶜHasPowerSeriesWithinAtZero ρ ρ<1 =
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAt
    logOnePlusPowerSeries
    0ᶜ
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (logOnePlusPowerSeriesOnSubunitBallWith ρ ρ<1)


logOnePlusᶜAnalyticWithinAtZero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  AnalyticWithinAt
    (logOnePlusᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
logOnePlusᶜAnalyticWithinAtZero ρ ρ<1 =
  centeredPowerSeriesWithinBallAnalyticWithinAt
    logOnePlusPowerSeries
    0ᶜ
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (logOnePlusPowerSeriesOnSubunitBallWith ρ ρ<1)


logOnePlusPowerSeriesOnBallFromGeometricMajorant :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  LogOnePlusGeometricMajorant ρ →
  HasPowerSeriesOnBall logOnePlusPowerSeries ρ
logOnePlusPowerSeriesOnBallFromGeometricMajorant ρ ρ<1 majorant =
  positiveGeometricPowerModulus ρ ρ<1 ,
  logOnePlusPowerSeriesOnBallWithFromGeometricMajorant ρ ρ<1 majorant


logOnePlusPowerSeriesOnSubunitBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBall logOnePlusPowerSeries ρ
logOnePlusPowerSeriesOnSubunitBall ρ ρ<1 =
  positiveGeometricPowerModulus ρ ρ<1 ,
  logOnePlusPowerSeriesOnSubunitBallWith ρ ρ<1


logOnePlusPowerSeriesRadius :
  HasPowerSeriesRadius logOnePlusPowerSeries 1⁺
logOnePlusPowerSeriesRadius =
  record
    { onSubball =
        λ ρ ρ<1 →
          logOnePlusPowerSeriesOnSubunitBall ρ ρ<1
    }


derivativeLogOnePlusPowerSeriesRadius :
  HasPowerSeriesRadius (derivativePowerSeries logOnePlusPowerSeries) 1⁺
derivativeLogOnePlusPowerSeriesRadius =
  derivativePowerSeriesRadiusFromCoefficientPath
    {a = logOnePlusPowerSeries}
    {b = alternatingGeometricPowerSeries}
    derivativePowerSeries-logOnePlus
    alternatingGeometricPowerSeriesRadius


primitiveAlternatingGeometricPowerSeriesRadius :
  HasPowerSeriesRadius
    (primitivePowerSeries alternatingGeometricPowerSeries)
    1⁺
primitiveAlternatingGeometricPowerSeriesRadius =
  primitivePowerSeriesRadiusFromCoefficientPath
    {a = alternatingGeometricPowerSeries}
    {b = logOnePlusPowerSeries}
    primitivePowerSeries-alternatingGeometric
    logOnePlusPowerSeriesRadius


logOnePlusPowerSeriesRadiusFromGeometricMajorants :
  ((ρ : ℚ⁺) →
    radius ρ ℚOrder.< Rational.1ℚ →
    LogOnePlusGeometricMajorant ρ) →
  HasPowerSeriesRadius logOnePlusPowerSeries 1⁺
logOnePlusPowerSeriesRadiusFromGeometricMajorants majorants =
  record
    { onSubball =
        λ ρ ρ<1 →
          logOnePlusPowerSeriesOnBallFromGeometricMajorant
            ρ
            ρ<1
            (majorants ρ ρ<1)
    }
