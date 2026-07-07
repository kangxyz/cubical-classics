{-

Part of Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric.Coefficients where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
  using (_+ᶜ_ ; add-inverse-right ; add-zero-left)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_ ; neg-involutive)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (≤ᶜ-refl)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using
    ( positiveGeometricPowerModulus
    ; positiveGeometricPowerModulus-antitone
    ; positiveGeometricFiniteTailBoundFromRatio
    ; positiveGeometricTerm
    ; positiveGeometricTerm-nonnegative
    ; positivePower
    )
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
    ; centeredPowerSeriesSumEverywhere-neg
    ; constantPowerSeries
    ; constantPowerSeriesInfiniteRadius
    ; negPowerSeries
    ; negPowerSeriesInfiniteRadius
    ; subPowerSeries
    ; subPowerSeriesInfiniteRadius
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; inverseSucReal
    ; naturalReal
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
    ; hasDerivativeAtWith-derivative-path
    ; positivePartialSum
    ; powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    ; powerSeriesFormalPartialSumsDerivativeModulus
    ; termwiseConvergenceIndex
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential
  using
    ( reciprocalFactorial⁺
    ; expPositiveMajorantRadius
    ; expPositiveMajorantTerm
    ; expPositiveMajorantTerm-nonnegative
    ; expPositiveMajorantFactorialModulus
    ; expPositiveMajorantFactorialTailBound
    ; expPositiveMajorantFactorialModulusAntitone
    )
open import Constructive.Data.PositiveRationals
  using
    ( ℚ⁺
    ; 1⁺
    ; _+⁺_
    ; _*⁺_
    ; *⁺-comm
    ; *⁺-identity-left
    ; ℚ⁺Path
    ; radius
    ; scalar-bound
    )
import Constructive.Data.Rationals.Archimedean as Rational
import Constructive.Data.Rationals.Base as RationalBase
import Constructive.Data.Rationals.Factorial as Factorial

open import Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric.Internal

mutual
  sinPowerSeries :
    PowerSeries
  sinPowerSeries zero =
    0ᶜ
  sinPowerSeries (suc n) =
    inverseSucReal n ·ᶜ cosPowerSeries n

  cosPowerSeries :
    PowerSeries
  cosPowerSeries zero =
    1ᶜ
  cosPowerSeries (suc n) =
    -ᶜ (inverseSucReal n ·ᶜ sinPowerSeries n)


sinPowerSeriesCoefficient-zero :
  sinPowerSeries zero ≡ 0ᶜ
sinPowerSeriesCoefficient-zero =
  refl


sinPowerSeriesCoefficient-suc :
  (n : ℕ) →
  sinPowerSeries (suc n) ≡
  inverseSucReal n ·ᶜ cosPowerSeries n
sinPowerSeriesCoefficient-suc n =
  refl


cosPowerSeriesCoefficient-zero :
  cosPowerSeries zero ≡ 1ᶜ
cosPowerSeriesCoefficient-zero =
  refl


cosPowerSeriesCoefficient-suc :
  (n : ℕ) →
  cosPowerSeries (suc n) ≡
  -ᶜ (inverseSucReal n ·ᶜ sinPowerSeries n)
cosPowerSeriesCoefficient-suc n =
  refl


derivativePowerSeries-sin :
  (n : ℕ) →
  derivativePowerSeries sinPowerSeries n ≡ cosPowerSeries n
derivativePowerSeries-sin n =
  naturalTimesInverseSucReal-cancel n (cosPowerSeries n)


derivativePowerSeries-cos :
  (n : ℕ) →
  derivativePowerSeries cosPowerSeries n ≡
  negPowerSeries sinPowerSeries n
derivativePowerSeries-cos n =
  mulᶜ-neg-right
    (naturalReal (suc n))
    (inverseSucReal n ·ᶜ sinPowerSeries n) ∙
  cong -ᶜ_ (naturalTimesInverseSucReal-cancel n (sinPowerSeries n))


primitivePowerSeries-cos :
  (n : ℕ) →
  primitivePowerSeries cosPowerSeries n ≡ sinPowerSeries n
primitivePowerSeries-cos zero =
  refl
primitivePowerSeries-cos (suc n) =
  refl


primitivePowerSeries-sin :
  (n : ℕ) →
  primitivePowerSeries sinPowerSeries n ≡
  subPowerSeries (constantPowerSeries 1ᶜ) cosPowerSeries n
primitivePowerSeries-sin zero =
  sym (add-inverse-right 1ᶜ)
primitivePowerSeries-sin (suc n) =
  sym (add-zero-left term) ∙
  cong (λ x → 0ᶜ +ᶜ x) (sym negCos≡term)
  where
  term : ℝᶜ
  term =
    inverseSucReal n ·ᶜ sinPowerSeries n

  negCos≡term :
    -ᶜ cosPowerSeries (suc n) ≡ term
  negCos≡term =
    cong -ᶜ_ (cosPowerSeriesCoefficient-suc n) ∙
    neg-involutive term
