{-

Formal sine and cosine power-series coefficients

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric where

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


zeroBoundOne :
  BoundedByᶜ 1⁺ 0ᶜ
zeroBoundOne =
  rational-closed-bound→boundedᶜ
    1⁺
    RationalBase.0ℚ
    (rational-closed-boundᶜ 0≤1 0≤1)
  where
  0≤1 :
    RationalBase.0ℚ ℚOrder.≤ RationalBase.1ℚ
  0≤1 =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = RationalBase.1ℚ}
      RationalBase.0<1


oneBoundOne :
  BoundedByᶜ 1⁺ 1ᶜ
oneBoundOne =
  rational-closed-bound→boundedᶜ
    1⁺
    RationalBase.1ℚ
    (rational-closed-boundᶜ 1≤1 -1≤1)
  where
  1≤1 :
    RationalBase.1ℚ ℚOrder.≤ RationalBase.1ℚ
  1≤1 =
    RationalBase.≤-refl RationalBase.1ℚ

  -1≤1 :
    ℚ.- RationalBase.1ℚ ℚOrder.≤ RationalBase.1ℚ
  -1≤1 =
    RationalBase.<→≤
      {p = RationalBase.-1ℚ}
      {q = RationalBase.1ℚ}
      (ℚOrder.isTrans<
        RationalBase.-1ℚ
        RationalBase.0ℚ
        RationalBase.1ℚ
        RationalBase.-1<0
        RationalBase.0<1)


inverseSucRealBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (inverseSucReal n)
inverseSucRealBoundOne n =
  rational-closed-bound→boundedᶜ
    1⁺
    inverse
    (rational-closed-boundᶜ inverse≤1 negative≤1)
  where
  inverse : ℚ
  inverse =
    Rational.divideBySuc RationalBase.1ℚ n

  unit : ℚ
  unit =
    Rational.unitFraction n

  inverse≡unit :
    inverse ≡ unit
  inverse≡unit =
    Rational.divideBySuc-as-unitFraction RationalBase.1ℚ n ∙
    ℚ.·IdL unit

  inverse≤1 :
    inverse ℚOrder.≤ RationalBase.1ℚ
  inverse≤1 =
    subst
      (λ q → q ℚOrder.≤ RationalBase.1ℚ)
      (sym inverse≡unit)
      (Factorial.unitFraction≤1 n)

  inverseNonnegative :
    RationalBase.0ℚ ℚOrder.≤ inverse
  inverseNonnegative =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = inverse}
      (Rational.divideBySuc-positive
        {q = RationalBase.1ℚ}
        RationalBase.0<1
        n)

  negative≤0 :
    ℚ.- inverse ℚOrder.≤ RationalBase.0ℚ
  negative≤0 =
    RationalBase.neg-nonpositive
      {q = inverse}
      inverseNonnegative

  0≤1 :
    RationalBase.0ℚ ℚOrder.≤ RationalBase.1ℚ
  0≤1 =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = RationalBase.1ℚ}
      RationalBase.0<1

  negative≤1 :
    ℚ.- inverse ℚOrder.≤ RationalBase.1ℚ
  negative≤1 =
    RationalBase.≤-trans
      {p = ℚ.- inverse}
      {q = RationalBase.0ℚ}
      {r = RationalBase.1ℚ}
      negative≤0
      0≤1


zeroBound :
  (κ : ℚ⁺) →
  BoundedByᶜ κ 0ᶜ
zeroBound κ =
  rational-closed-bound→boundedᶜ
    κ
    RationalBase.0ℚ
    (rational-closed-boundᶜ 0≤κ 0≤κ)
  where
  0≤κ :
    RationalBase.0ℚ ℚOrder.≤ radius κ
  0≤κ =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = radius κ}
      (κ .snd)


unitFraction⁺ :
  ℕ →
  ℚ⁺
unitFraction⁺ n =
  Rational.unitFraction n ,
  Rational.unitFraction-positive n


unitFraction⁺*reciprocalFactorial⁺ :
  (n : ℕ) →
  unitFraction⁺ n *⁺ reciprocalFactorial⁺ n ≡
  reciprocalFactorial⁺ (suc n)
unitFraction⁺*reciprocalFactorial⁺ n =
  ℚ⁺Path
    (ℚ.·Comm unit reciprocal ∙
    sym (Rational.divideBySuc-as-unitFraction reciprocal n) ∙
    sym (Factorial.reciprocalFactorial-suc n))
  where
  unit : ℚ
  unit =
    Rational.unitFraction n

  reciprocal : ℚ
  reciprocal =
    Factorial.reciprocalFactorial n


oneBoundReciprocalFactorialZero :
  BoundedByᶜ (reciprocalFactorial⁺ zero) 1ᶜ
oneBoundReciprocalFactorialZero =
  rational-closed-bound→boundedᶜ
    (reciprocalFactorial⁺ zero)
    RationalBase.1ℚ
    (rational-closed-boundᶜ 1≤1 -1≤1)
  where
  1≤1 :
    RationalBase.1ℚ ℚOrder.≤ RationalBase.1ℚ
  1≤1 =
    RationalBase.≤-refl RationalBase.1ℚ

  -1≤1 :
    ℚ.- RationalBase.1ℚ ℚOrder.≤ RationalBase.1ℚ
  -1≤1 =
    RationalBase.<→≤
      {p = RationalBase.-1ℚ}
      {q = RationalBase.1ℚ}
      (ℚOrder.isTrans<
        RationalBase.-1ℚ
        RationalBase.0ℚ
        RationalBase.1ℚ
        RationalBase.-1<0
        RationalBase.0<1)


inverseSucRealBoundUnit :
  (n : ℕ) →
  BoundedByᶜ (unitFraction⁺ n) (inverseSucReal n)
inverseSucRealBoundUnit n =
  rational-closed-bound→boundedᶜ
    (unitFraction⁺ n)
    inverse
    (rational-closed-boundᶜ inverse≤unit negative≤unit)
  where
  inverse : ℚ
  inverse =
    Rational.divideBySuc RationalBase.1ℚ n

  unit : ℚ
  unit =
    Rational.unitFraction n

  inverse≡unit :
    inverse ≡ unit
  inverse≡unit =
    Rational.divideBySuc-as-unitFraction RationalBase.1ℚ n ∙
    ℚ.·IdL unit

  inverse≤unit :
    inverse ℚOrder.≤ unit
  inverse≤unit =
    subst
      (λ q → inverse ℚOrder.≤ q)
      inverse≡unit
      (RationalBase.≤-refl inverse)

  inverseNonnegative :
    RationalBase.0ℚ ℚOrder.≤ inverse
  inverseNonnegative =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = inverse}
      (Rational.divideBySuc-positive
        {q = RationalBase.1ℚ}
        RationalBase.0<1
        n)

  negative≤0 :
    ℚ.- inverse ℚOrder.≤ RationalBase.0ℚ
  negative≤0 =
    RationalBase.neg-nonpositive
      {q = inverse}
      inverseNonnegative

  0≤unit :
    RationalBase.0ℚ ℚOrder.≤ unit
  0≤unit =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = unit}
      (Rational.unitFraction-positive n)

  negative≤unit :
    ℚ.- inverse ℚOrder.≤ unit
  negative≤unit =
    RationalBase.≤-trans
      {p = ℚ.- inverse}
      {q = RationalBase.0ℚ}
      {r = unit}
      negative≤0
      0≤unit


mutual
  sinPowerSeriesCoefficientBoundOne :
    (n : ℕ) →
    BoundedByᶜ 1⁺ (sinPowerSeries n)
  sinPowerSeriesCoefficientBoundOne zero =
    zeroBoundOne
  sinPowerSeriesCoefficientBoundOne (suc n) =
    subst
      (λ κ → BoundedByᶜ κ (sinPowerSeries (suc n)))
      (*⁺-identity-left 1⁺)
      (bounded-byᶜ-mul
        1⁺
        1⁺
        (inverseSucReal n)
        (cosPowerSeries n)
        (inverseSucRealBoundOne n)
        (cosPowerSeriesCoefficientBoundOne n))

  cosPowerSeriesCoefficientBoundOne :
    (n : ℕ) →
    BoundedByᶜ 1⁺ (cosPowerSeries n)
  cosPowerSeriesCoefficientBoundOne zero =
    oneBoundOne
  cosPowerSeriesCoefficientBoundOne (suc n) =
    subst
      (λ κ → BoundedByᶜ κ (cosPowerSeries (suc n)))
      (*⁺-identity-left 1⁺)
      (bounded-byᶜ-neg
        (1⁺ *⁺ 1⁺)
        (inverseSucReal n ·ᶜ sinPowerSeries n)
        (bounded-byᶜ-mul
          1⁺
          1⁺
          (inverseSucReal n)
          (sinPowerSeries n)
          (inverseSucRealBoundOne n)
          (sinPowerSeriesCoefficientBoundOne n)))


sinPowerSeriesIteratedFormalPartialDerivativeBounds :
  (σ : ℚ⁺) →
  {x : ℝᶜ} →
  BoundedByᶜ σ x →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    sinPowerSeries
    x
    (λ s n →
      positivePartialSum
        (λ k →
          scalar-bound (Rational.natMul (suc k) RationalBase.1ℚ) *⁺
          1⁺ *⁺
          positivePower σ k)
        n)
sinPowerSeriesIteratedFormalPartialDerivativeBounds σ x-bound =
  powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    σ
    x-bound
    (λ _ → 1⁺)
    sinPowerSeriesCoefficientBoundOne


cosPowerSeriesIteratedFormalPartialDerivativeBounds :
  (σ : ℚ⁺) →
  {x : ℝᶜ} →
  BoundedByᶜ σ x →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    cosPowerSeries
    x
    (λ s n →
      positivePartialSum
        (λ k →
          scalar-bound (Rational.natMul (suc k) RationalBase.1ℚ) *⁺
          1⁺ *⁺
          positivePower σ k)
        n)
cosPowerSeriesIteratedFormalPartialDerivativeBounds σ x-bound =
  powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    σ
    x-bound
    (λ _ → 1⁺)
    cosPowerSeriesCoefficientBoundOne


mutual
  sinPowerSeriesCoefficientBoundFactorial :
    (n : ℕ) →
    BoundedByᶜ (reciprocalFactorial⁺ n) (sinPowerSeries n)
  sinPowerSeriesCoefficientBoundFactorial zero =
    zeroBound (reciprocalFactorial⁺ zero)
  sinPowerSeriesCoefficientBoundFactorial (suc n) =
    subst
      (λ κ → BoundedByᶜ κ (sinPowerSeries (suc n)))
      (unitFraction⁺*reciprocalFactorial⁺ n)
      (bounded-byᶜ-mul
        (unitFraction⁺ n)
        (reciprocalFactorial⁺ n)
        (inverseSucReal n)
        (cosPowerSeries n)
        (inverseSucRealBoundUnit n)
        (cosPowerSeriesCoefficientBoundFactorial n))

  cosPowerSeriesCoefficientBoundFactorial :
    (n : ℕ) →
    BoundedByᶜ (reciprocalFactorial⁺ n) (cosPowerSeries n)
  cosPowerSeriesCoefficientBoundFactorial zero =
    oneBoundReciprocalFactorialZero
  cosPowerSeriesCoefficientBoundFactorial (suc n) =
    subst
      (λ κ → BoundedByᶜ κ (cosPowerSeries (suc n)))
      (unitFraction⁺*reciprocalFactorial⁺ n)
      (bounded-byᶜ-neg
        (unitFraction⁺ n *⁺ reciprocalFactorial⁺ n)
        (inverseSucReal n ·ᶜ sinPowerSeries n)
        (bounded-byᶜ-mul
          (unitFraction⁺ n)
          (reciprocalFactorial⁺ n)
          (inverseSucReal n)
          (sinPowerSeries n)
          (inverseSucRealBoundUnit n)
          (sinPowerSeriesCoefficientBoundFactorial n)))


sinPowerSeriesTermBoundFromPowerBound :
  (ρ : ℚ⁺) →
  (h : ℝᶜ) →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n) →
  BoundedByᶜ (positivePower ρ n) (powerSeriesTerm sinPowerSeries h n)
sinPowerSeriesTermBoundFromPowerBound ρ h n powerBound =
  subst
    (λ κ → BoundedByᶜ κ (powerSeriesTerm sinPowerSeries h n))
    (*⁺-identity-left (positivePower ρ n))
    (bounded-byᶜ-mul
      1⁺
      (positivePower ρ n)
      (sinPowerSeries n)
      (realPower h n)
      (sinPowerSeriesCoefficientBoundOne n)
      powerBound)


cosPowerSeriesTermBoundFromPowerBound :
  (ρ : ℚ⁺) →
  (h : ℝᶜ) →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n) →
  BoundedByᶜ (positivePower ρ n) (powerSeriesTerm cosPowerSeries h n)
cosPowerSeriesTermBoundFromPowerBound ρ h n powerBound =
  subst
    (λ κ → BoundedByᶜ κ (powerSeriesTerm cosPowerSeries h n))
    (*⁺-identity-left (positivePower ρ n))
    (bounded-byᶜ-mul
      1⁺
      (positivePower ρ n)
      (cosPowerSeries n)
      (realPower h n)
      (cosPowerSeriesCoefficientBoundOne n)
      powerBound)


sinPowerSeriesTermBoundByExpMajorant :
  (ρ : ℚ⁺) →
  (h : ℝᶜ) →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n) →
  BoundedByᶜ (expPositiveMajorantRadius ρ n)
    (powerSeriesTerm sinPowerSeries h n)
sinPowerSeriesTermBoundByExpMajorant ρ h n powerBound =
  subst
    (λ κ → BoundedByᶜ κ (powerSeriesTerm sinPowerSeries h n))
    (*⁺-comm (reciprocalFactorial⁺ n) (positivePower ρ n))
    (bounded-byᶜ-mul
      (reciprocalFactorial⁺ n)
      (positivePower ρ n)
      (sinPowerSeries n)
      (realPower h n)
      (sinPowerSeriesCoefficientBoundFactorial n)
      powerBound)


cosPowerSeriesTermBoundByExpMajorant :
  (ρ : ℚ⁺) →
  (h : ℝᶜ) →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n) →
  BoundedByᶜ (expPositiveMajorantRadius ρ n)
    (powerSeriesTerm cosPowerSeries h n)
cosPowerSeriesTermBoundByExpMajorant ρ h n powerBound =
  subst
    (λ κ → BoundedByᶜ κ (powerSeriesTerm cosPowerSeries h n))
    (*⁺-comm (reciprocalFactorial⁺ n) (positivePower ρ n))
    (bounded-byᶜ-mul
      (reciprocalFactorial⁺ n)
      (positivePower ρ n)
      (cosPowerSeries n)
      (realPower h n)
      (cosPowerSeriesCoefficientBoundFactorial n)
      powerBound)


SinPowerSeriesMajorizedOnBall :
  ℚ⁺ →
  (ℕ → ℝᶜ) →
  (ℚ⁺ → ℕ) →
  Type₀
SinPowerSeriesMajorizedOnBall ρ v μ =
  PowerSeriesMajorizedOnBall sinPowerSeries ρ v μ


CosPowerSeriesMajorizedOnBall :
  ℚ⁺ →
  (ℕ → ℝᶜ) →
  (ℚ⁺ → ℕ) →
  Type₀
CosPowerSeriesMajorizedOnBall ρ v μ =
  PowerSeriesMajorizedOnBall cosPowerSeries ρ v μ


TrigPowerSeriesPowerBoundsOnBall :
  ℚ⁺ →
  Type₀
TrigPowerSeriesPowerBoundsOnBall ρ =
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n)


trigPowerSeriesPowerBoundsFromBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  TrigPowerSeriesPowerBoundsOnBall ρ
trigPowerSeriesPowerBoundsFromBall ρ ρ<1 h h-bound n =
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


trigPowerSeriesPowerBoundsOnAnyBall :
  (ρ : ℚ⁺) →
  TrigPowerSeriesPowerBoundsOnBall ρ
trigPowerSeriesPowerBoundsOnAnyBall ρ h h-bound n =
  realPowerBoundsFromBound ρ h h-bound n


sinPowerSeriesFactorialMajorizedFromPowerBounds :
  (ρ : ℚ⁺) →
  TrigPowerSeriesPowerBoundsOnBall ρ →
  SinPowerSeriesMajorizedOnBall
    ρ
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
sinPowerSeriesFactorialMajorizedFromPowerBounds ρ powerBounds =
  powerSeriesMajorizedOnBallFromBoundedTerms
    {a = sinPowerSeries}
    {ρ = ρ}
    {κ = expPositiveMajorantRadius ρ}
    {v = expPositiveMajorantTerm ρ}
    (λ h h-bound n →
      sinPowerSeriesTermBoundByExpMajorant
        ρ
        h
        n
        (powerBounds h h-bound n))
    (λ n → ≤ᶜ-refl (expPositiveMajorantTerm ρ n))
    (expPositiveMajorantTerm-nonnegative ρ)
    (expPositiveMajorantFactorialTailBound ρ)
    (λ {ε} {δ} ε≤δ →
      expPositiveMajorantFactorialModulusAntitone
        ρ
        {ε = ε}
        {δ = δ}
        ε≤δ)


cosPowerSeriesFactorialMajorizedFromPowerBounds :
  (ρ : ℚ⁺) →
  TrigPowerSeriesPowerBoundsOnBall ρ →
  CosPowerSeriesMajorizedOnBall
    ρ
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
cosPowerSeriesFactorialMajorizedFromPowerBounds ρ powerBounds =
  powerSeriesMajorizedOnBallFromBoundedTerms
    {a = cosPowerSeries}
    {ρ = ρ}
    {κ = expPositiveMajorantRadius ρ}
    {v = expPositiveMajorantTerm ρ}
    (λ h h-bound n →
      cosPowerSeriesTermBoundByExpMajorant
        ρ
        h
        n
        (powerBounds h h-bound n))
    (λ n → ≤ᶜ-refl (expPositiveMajorantTerm ρ n))
    (expPositiveMajorantTerm-nonnegative ρ)
    (expPositiveMajorantFactorialTailBound ρ)
    (λ {ε} {δ} ε≤δ →
      expPositiveMajorantFactorialModulusAntitone
        ρ
        {ε = ε}
        {δ = δ}
        ε≤δ)


sinPowerSeriesFactorialMajorized :
  (ρ : ℚ⁺) →
  SinPowerSeriesMajorizedOnBall
    ρ
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
sinPowerSeriesFactorialMajorized ρ =
  sinPowerSeriesFactorialMajorizedFromPowerBounds
    ρ
    (trigPowerSeriesPowerBoundsOnAnyBall ρ)


cosPowerSeriesFactorialMajorized :
  (ρ : ℚ⁺) →
  CosPowerSeriesMajorizedOnBall
    ρ
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
cosPowerSeriesFactorialMajorized ρ =
  cosPowerSeriesFactorialMajorizedFromPowerBounds
    ρ
    (trigPowerSeriesPowerBoundsOnAnyBall ρ)


sinPowerSeriesSubunitMajorizedFromPowerBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  TrigPowerSeriesPowerBoundsOnBall ρ →
  SinPowerSeriesMajorizedOnBall
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
sinPowerSeriesSubunitMajorizedFromPowerBounds ρ ρ<1 powerBounds =
  powerSeriesMajorizedOnBallFromBoundedTerms
    {a = sinPowerSeries}
    {ρ = ρ}
    {κ = positivePower ρ}
    {v = positiveGeometricTerm ρ}
    (λ h h-bound n →
      sinPowerSeriesTermBoundFromPowerBound
        ρ
        h
        n
        (powerBounds h h-bound n))
    (λ n → ≤ᶜ-refl (positiveGeometricTerm ρ n))
    (positiveGeometricTerm-nonnegative ρ)
    (λ ε m k μ≤m →
      positiveGeometricFiniteTailBoundFromRatio ρ ρ<1 ε m k μ≤m)
    (λ {ε} {δ} ε≤δ →
      positiveGeometricPowerModulus-antitone
        ρ
        ρ<1
        {ε = ε}
        {δ = δ}
        ε≤δ)


cosPowerSeriesSubunitMajorizedFromPowerBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  TrigPowerSeriesPowerBoundsOnBall ρ →
  CosPowerSeriesMajorizedOnBall
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
cosPowerSeriesSubunitMajorizedFromPowerBounds ρ ρ<1 powerBounds =
  powerSeriesMajorizedOnBallFromBoundedTerms
    {a = cosPowerSeries}
    {ρ = ρ}
    {κ = positivePower ρ}
    {v = positiveGeometricTerm ρ}
    (λ h h-bound n →
      cosPowerSeriesTermBoundFromPowerBound
        ρ
        h
        n
        (powerBounds h h-bound n))
    (λ n → ≤ᶜ-refl (positiveGeometricTerm ρ n))
    (positiveGeometricTerm-nonnegative ρ)
    (λ ε m k μ≤m →
      positiveGeometricFiniteTailBoundFromRatio ρ ρ<1 ε m k μ≤m)
    (λ {ε} {δ} ε≤δ →
      positiveGeometricPowerModulus-antitone
        ρ
        ρ<1
        {ε = ε}
        {δ = δ}
        ε≤δ)


sinPowerSeriesSubunitMajorized :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  SinPowerSeriesMajorizedOnBall
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
sinPowerSeriesSubunitMajorized ρ ρ<1 =
  sinPowerSeriesSubunitMajorizedFromPowerBounds
    ρ
    ρ<1
    (trigPowerSeriesPowerBoundsFromBall ρ ρ<1)


cosPowerSeriesSubunitMajorized :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  CosPowerSeriesMajorizedOnBall
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
cosPowerSeriesSubunitMajorized ρ ρ<1 =
  cosPowerSeriesSubunitMajorizedFromPowerBounds
    ρ
    ρ<1
    (trigPowerSeriesPowerBoundsFromBall ρ ρ<1)


sinPowerSeriesOnBallWithFromMajorant :
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  SinPowerSeriesMajorizedOnBall ρ v μ →
  HasPowerSeriesOnBallWith sinPowerSeries ρ μ
sinPowerSeriesOnBallWithFromMajorant =
  majorizedOnBall→hasPowerSeriesOnBallWith


cosPowerSeriesOnBallWithFromMajorant :
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  CosPowerSeriesMajorizedOnBall ρ v μ →
  HasPowerSeriesOnBallWith cosPowerSeries ρ μ
cosPowerSeriesOnBallWithFromMajorant =
  majorizedOnBall→hasPowerSeriesOnBallWith


sinPowerSeriesOnSubunitBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  HasPowerSeriesOnBallWith
    sinPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
sinPowerSeriesOnSubunitBallWith ρ ρ<1 =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (sinPowerSeriesSubunitMajorized ρ ρ<1)


cosPowerSeriesOnSubunitBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  HasPowerSeriesOnBallWith
    cosPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
cosPowerSeriesOnSubunitBallWith ρ ρ<1 =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (cosPowerSeriesSubunitMajorized ρ ρ<1)


sinPowerSeriesOnBallFromMajorant :
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  SinPowerSeriesMajorizedOnBall ρ v μ →
  HasPowerSeriesOnBall sinPowerSeries ρ
sinPowerSeriesOnBallFromMajorant =
  majorizedOnBall→hasPowerSeriesOnBall


cosPowerSeriesOnBallFromMajorant :
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  CosPowerSeriesMajorizedOnBall ρ v μ →
  HasPowerSeriesOnBall cosPowerSeries ρ
cosPowerSeriesOnBallFromMajorant =
  majorizedOnBall→hasPowerSeriesOnBall


sinPowerSeriesOnSubunitBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  HasPowerSeriesOnBall sinPowerSeries ρ
sinPowerSeriesOnSubunitBall ρ ρ<1 =
  positiveGeometricPowerModulus ρ ρ<1 ,
  sinPowerSeriesOnSubunitBallWith ρ ρ<1


cosPowerSeriesOnSubunitBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  HasPowerSeriesOnBall cosPowerSeries ρ
cosPowerSeriesOnSubunitBall ρ ρ<1 =
  positiveGeometricPowerModulus ρ ρ<1 ,
  cosPowerSeriesOnSubunitBallWith ρ ρ<1


sinPowerSeriesOnBallWith :
  (ρ : ℚ⁺) →
  HasPowerSeriesOnBallWith
    sinPowerSeries
    ρ
    (expPositiveMajorantFactorialModulus ρ)
sinPowerSeriesOnBallWith ρ =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (sinPowerSeriesFactorialMajorized ρ)


cosPowerSeriesOnBallWith :
  (ρ : ℚ⁺) →
  HasPowerSeriesOnBallWith
    cosPowerSeries
    ρ
    (expPositiveMajorantFactorialModulus ρ)
cosPowerSeriesOnBallWith ρ =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (cosPowerSeriesFactorialMajorized ρ)


sinPowerSeriesOnBall :
  (ρ : ℚ⁺) →
  HasPowerSeriesOnBall sinPowerSeries ρ
sinPowerSeriesOnBall ρ =
  expPositiveMajorantFactorialModulus ρ ,
  sinPowerSeriesOnBallWith ρ


cosPowerSeriesOnBall :
  (ρ : ℚ⁺) →
  HasPowerSeriesOnBall cosPowerSeries ρ
cosPowerSeriesOnBall ρ =
  expPositiveMajorantFactorialModulus ρ ,
  cosPowerSeriesOnBallWith ρ


sinPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius sinPowerSeries
sinPowerSeriesInfiniteRadius =
  sinPowerSeriesOnBall


cosPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius cosPowerSeries
cosPowerSeriesInfiniteRadius =
  cosPowerSeriesOnBall


sinᶜ :
  ℝᶜ →
  ℝᶜ
sinᶜ =
  centeredPowerSeriesSumEverywhere
    sinPowerSeries
    0ᶜ
    sinPowerSeriesInfiniteRadius


cosᶜ :
  ℝᶜ →
  ℝᶜ
cosᶜ =
  centeredPowerSeriesSumEverywhere
    cosPowerSeries
    0ᶜ
    cosPowerSeriesInfiniteRadius


sinᶜ-zero :
  sinᶜ 0ᶜ ≡ 0ᶜ
sinᶜ-zero =
  centeredPowerSeriesSumEverywhere-center
    sinPowerSeriesInfiniteRadius
    0ᶜ


cosᶜ-zero :
  cosᶜ 0ᶜ ≡ 1ᶜ
cosᶜ-zero =
  centeredPowerSeriesSumEverywhere-center
    cosPowerSeriesInfiniteRadius
    0ᶜ


negSinᶜ :
  ℝᶜ →
  ℝᶜ
negSinᶜ =
  centeredPowerSeriesSumEverywhere
    (negPowerSeries sinPowerSeries)
    0ᶜ
    (negPowerSeriesInfiniteRadius sinPowerSeriesInfiniteRadius)


negSinᶜ-path :
  (x : ℝᶜ) →
  negSinᶜ x ≡ -ᶜ sinᶜ x
negSinᶜ-path =
  centeredPowerSeriesSumEverywhere-neg
    sinPowerSeriesInfiniteRadius
    0ᶜ


sinᶜHasPowerSeriesAtWithZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtWith
    sinᶜ
    0ᶜ
    sinPowerSeries
    ρ
    (sinPowerSeriesInfiniteRadius ρ .fst)
sinᶜHasPowerSeriesAtWithZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    sinPowerSeriesInfiniteRadius


cosᶜHasPowerSeriesAtWithZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtWith
    cosᶜ
    0ᶜ
    cosPowerSeries
    ρ
    (cosPowerSeriesInfiniteRadius ρ .fst)
cosᶜHasPowerSeriesAtWithZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    cosPowerSeriesInfiniteRadius


sinᶜHasPowerSeriesAtOnBallZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtOnBall sinᶜ 0ᶜ sinPowerSeries ρ
sinᶜHasPowerSeriesAtOnBallZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall
    sinPowerSeriesInfiniteRadius


cosᶜHasPowerSeriesAtOnBallZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtOnBall cosᶜ 0ᶜ cosPowerSeries ρ
cosᶜHasPowerSeriesAtOnBallZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall
    cosPowerSeriesInfiniteRadius


sinᶜHasPowerSeriesAtZero :
  HasPowerSeriesAt sinᶜ 0ᶜ sinPowerSeries
sinᶜHasPowerSeriesAtZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAt
    sinPowerSeriesInfiniteRadius


cosᶜHasPowerSeriesAtZero :
  HasPowerSeriesAt cosᶜ 0ᶜ cosPowerSeries
cosᶜHasPowerSeriesAtZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAt
    cosPowerSeriesInfiniteRadius


sinᶜAnalyticAtZero :
  AnalyticAt sinᶜ 0ᶜ
sinᶜAnalyticAtZero =
  centeredPowerSeriesSumEverywhereAnalyticAt
    sinPowerSeries
    0ᶜ
    sinPowerSeriesInfiniteRadius


cosᶜAnalyticAtZero :
  AnalyticAt cosᶜ 0ᶜ
cosᶜAnalyticAtZero =
  centeredPowerSeriesSumEverywhereAnalyticAt
    cosPowerSeries
    0ᶜ
    cosPowerSeriesInfiniteRadius


derivativeSinPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (derivativePowerSeries sinPowerSeries)
derivativeSinPowerSeriesInfiniteRadius =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = sinPowerSeries}
    {b = cosPowerSeries}
    derivativePowerSeries-sin
    cosPowerSeriesInfiniteRadius


derivativeCosPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (derivativePowerSeries cosPowerSeries)
derivativeCosPowerSeriesInfiniteRadius =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = cosPowerSeries}
    {b = negPowerSeries sinPowerSeries}
    derivativePowerSeries-cos
    (negPowerSeriesInfiniteRadius sinPowerSeriesInfiniteRadius)


sinᶜHasDerivativeAtWithFromIteratedBoundsOnSubball :
  {x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement 0ᶜ x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    sinPowerSeries
    (centeredDisplacement 0ᶜ x)
    δ →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (sinPowerSeriesInfiniteRadius ρ .fst)
      (derivativeSinPowerSeriesInfiniteRadius σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith sinᶜ x (cosᶜ x) μ
sinᶜHasDerivativeAtWithFromIteratedBoundsOnSubball
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {δ = δ}
  x-displacement-bound
  margin
  derivative-bounds
  partialModulus-large =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
    {a = sinPowerSeries}
    {b = cosPowerSeries}
    {c = 0ᶜ}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    {δ = δ}
    derivativePowerSeries-sin
    sinPowerSeriesInfiniteRadius
    derivativeSinPowerSeriesInfiniteRadius
    cosPowerSeriesInfiniteRadius
    x-displacement-bound
    margin
    derivative-bounds
    partialModulus-large


cosᶜHasDerivativeAtWithFromIteratedBoundsOnSubball :
  {x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement 0ᶜ x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    cosPowerSeries
    (centeredDisplacement 0ᶜ x)
    δ →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (cosPowerSeriesInfiniteRadius ρ .fst)
      (derivativeCosPowerSeriesInfiniteRadius σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith cosᶜ x (-ᶜ sinᶜ x) μ
cosᶜHasDerivativeAtWithFromIteratedBoundsOnSubball
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {δ = δ}
  x-displacement-bound
  margin
  derivative-bounds
  partialModulus-large =
  hasDerivativeAtWith-derivative-path
    {f = cosᶜ}
    {x = x}
    {d = negSinᶜ x}
    {e = -ᶜ sinᶜ x}
    {μ = μ}
    (negSinᶜ-path x)
    derivative
  where
  derivative :
    HasDerivativeAtWith cosᶜ x (negSinᶜ x) μ
  derivative =
    centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
      {a = cosPowerSeries}
      {b = negPowerSeries sinPowerSeries}
      {c = 0ᶜ}
      {x = x}
      {ρ = ρ}
      {σ = σ}
      {μ = μ}
      {δ = δ}
      derivativePowerSeries-cos
      cosPowerSeriesInfiniteRadius
      derivativeCosPowerSeriesInfiniteRadius
      (negPowerSeriesInfiniteRadius sinPowerSeriesInfiniteRadius)
      x-displacement-bound
      margin
      derivative-bounds
      partialModulus-large


primitiveCosPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (primitivePowerSeries cosPowerSeries)
primitiveCosPowerSeriesInfiniteRadius =
  primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = cosPowerSeries}
    {b = sinPowerSeries}
    primitivePowerSeries-cos
    sinPowerSeriesInfiniteRadius


primitiveSinPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (primitivePowerSeries sinPowerSeries)
primitiveSinPowerSeriesInfiniteRadius =
  primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = sinPowerSeries}
    {b = subPowerSeries (constantPowerSeries 1ᶜ) cosPowerSeries}
    primitivePowerSeries-sin
    (subPowerSeriesInfiniteRadius
      (constantPowerSeriesInfiniteRadius 1ᶜ)
      cosPowerSeriesInfiniteRadius)


SinPowerSeriesMajorants :
  Type₀
SinPowerSeriesMajorants =
  (ρ : ℚ⁺) →
  Σ[ v ∈ (ℕ → ℝᶜ) ]
  Σ[ μ ∈ (ℚ⁺ → ℕ) ]
    SinPowerSeriesMajorizedOnBall ρ v μ


CosPowerSeriesMajorants :
  Type₀
CosPowerSeriesMajorants =
  (ρ : ℚ⁺) →
  Σ[ v ∈ (ℕ → ℝᶜ) ]
  Σ[ μ ∈ (ℚ⁺ → ℕ) ]
    CosPowerSeriesMajorizedOnBall ρ v μ


sinPowerSeriesInfiniteRadiusFromMajorants :
  SinPowerSeriesMajorants →
  HasInfinitePowerSeriesRadius sinPowerSeries
sinPowerSeriesInfiniteRadiusFromMajorants majorants ρ =
  μ , sinPowerSeriesOnBallWithFromMajorant majorant
  where
  v : ℕ → ℝᶜ
  v =
    majorants ρ .fst

  μ : ℚ⁺ → ℕ
  μ =
    majorants ρ .snd .fst

  majorant : SinPowerSeriesMajorizedOnBall ρ v μ
  majorant =
    majorants ρ .snd .snd


cosPowerSeriesInfiniteRadiusFromMajorants :
  CosPowerSeriesMajorants →
  HasInfinitePowerSeriesRadius cosPowerSeries
cosPowerSeriesInfiniteRadiusFromMajorants majorants ρ =
  μ , cosPowerSeriesOnBallWithFromMajorant majorant
  where
  v : ℕ → ℝᶜ
  v =
    majorants ρ .fst

  μ : ℚ⁺ → ℕ
  μ =
    majorants ρ .snd .fst

  majorant : CosPowerSeriesMajorizedOnBall ρ v μ
  majorant =
    majorants ρ .snd .snd
