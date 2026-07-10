{-

Part of Constructive.Analysis.Reals.PowerSeries.Instances.Exponential

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Coefficients where

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
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (scalarMulᶜ-nonnegative ; scalarMulᶜ-pres≤ᶜ-scalar)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-refl)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative.Base
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.Calculus.Derivative.Rules
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Majorant
  using
    ( bounded-byᶜ-abs
    ; bounded-byᶜ-scale-rational-closed-bound
    )
open import Constructive.Analysis.GeometricDecay
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using
    ( RealGeometricBound
    ; RealGeometricPowerBounds
    ; realGeometricPowerBoundsFromBound
    ; realPowerBoundsFromBound
    ; realPower
    )
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
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; inverseSucReal
    ; naturalTimesInverseSucReal-cancel
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence
  using
    ( derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    ; primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    )
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using
    ( AnalyticAt
    ; HasPowerSeriesAt
    ; HasPowerSeriesAtOnBall
    ; HasPowerSeriesAtWith
    ; centeredPowerSeriesSumEverywhereAnalyticAt
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAt
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative
  using
    ( PowerSeriesIteratedFormalPartialDerivativeBounds
    ; PowerSeriesPartialSumsDerivativeModulusLarge
    ; centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
    ; positivePartialSum
    ; powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    ; powerSeriesFormalPartialSumsDerivativeModulus
    ; termwiseConvergenceIndex
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

open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Internal

expPowerSeries :
  PowerSeries
expPowerSeries zero =
  1ᶜ
expPowerSeries (suc n) =
  inverseSucReal n ·ᶜ expPowerSeries n


expPowerSeriesCoefficient-zero :
  expPowerSeries zero ≡ 1ᶜ
expPowerSeriesCoefficient-zero =
  refl


expPowerSeriesCoefficient-suc :
  (n : ℕ) →
  expPowerSeries (suc n) ≡
  inverseSucReal n ·ᶜ expPowerSeries n
expPowerSeriesCoefficient-suc n =
  refl


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


expPowerSeries-divideByFactorial :
  (n : ℕ) →
  expPowerSeries n ≡
  rational (Factorial.divideByFactorial RationalBase.1ℚ n)
expPowerSeries-divideByFactorial n =
  expPowerSeries-reciprocalFactorial n ∙
  cong rational (sym (Factorial.divideByFactorial-one n))


reciprocalFactorialClosedBoundOne :
  (n : ℕ) →
  RationalClosedBoundᶜ 1⁺ (Factorial.reciprocalFactorial n)
reciprocalFactorialClosedBoundOne n =
  rational-closed-boundᶜ
    (Factorial.reciprocalFactorial≤1 n)
    negative≤1
  where
  reciprocalNonnegative :
    RationalBase.0ℚ ℚOrder.≤ Factorial.reciprocalFactorial n
  reciprocalNonnegative =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = Factorial.reciprocalFactorial n}
      (Factorial.reciprocalFactorial-positive n)

  negative≤0 :
    ℚ.- Factorial.reciprocalFactorial n ℚOrder.≤ RationalBase.0ℚ
  negative≤0 =
    RationalBase.neg-nonpositive
      {q = Factorial.reciprocalFactorial n}
      reciprocalNonnegative

  0≤1 :
    RationalBase.0ℚ ℚOrder.≤ RationalBase.1ℚ
  0≤1 =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = RationalBase.1ℚ}
      RationalBase.0<1

  negative≤1 :
    ℚ.- Factorial.reciprocalFactorial n ℚOrder.≤ RationalBase.1ℚ
  negative≤1 =
    RationalBase.≤-trans
      {p = ℚ.- Factorial.reciprocalFactorial n}
      {q = RationalBase.0ℚ}
      {r = RationalBase.1ℚ}
      negative≤0
      0≤1


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


reciprocalFactorial⁺ :
  ℕ →
  ℚ⁺
reciprocalFactorial⁺ n =
  Factorial.reciprocalFactorial n ,
  Factorial.reciprocalFactorial-positive n


reciprocalFactorialClosedBoundSelf :
  (n : ℕ) →
  RationalClosedBoundᶜ (reciprocalFactorial⁺ n) (Factorial.reciprocalFactorial n)
reciprocalFactorialClosedBoundSelf n =
  rational-closed-boundᶜ
    (RationalBase.≤-refl reciprocal)
    negative≤reciprocal
  where
  reciprocal : ℚ
  reciprocal =
    Factorial.reciprocalFactorial n

  reciprocal-nonnegative :
    RationalBase.0ℚ ℚOrder.≤ reciprocal
  reciprocal-nonnegative =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = reciprocal}
      (Factorial.reciprocalFactorial-positive n)

  negative≤0 :
    ℚ.- reciprocal ℚOrder.≤ RationalBase.0ℚ
  negative≤0 =
    RationalBase.neg-nonpositive {q = reciprocal} reciprocal-nonnegative

  negative≤reciprocal :
    ℚ.- reciprocal ℚOrder.≤ reciprocal
  negative≤reciprocal =
    RationalBase.≤-trans
      {p = ℚ.- reciprocal}
      {q = RationalBase.0ℚ}
      {r = reciprocal}
      negative≤0
      reciprocal-nonnegative
