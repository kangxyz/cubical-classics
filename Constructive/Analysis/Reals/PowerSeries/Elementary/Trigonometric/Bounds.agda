{-

Part of Constructive.Analysis.Reals.PowerSeries.Elementary.Trigonometric

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Trigonometric.Bounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
  using (_+ᶜ_ ; add-inverse-right ; add-zero-left)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_ ; neg-involutive)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (≤ᶜ-refl)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.DerivativeData
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.Calculus.DerivativeRules
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.GeometricDecay
open import Constructive.Analysis.Reals.Series.Geometric.Positive
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower)
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
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using
    ( derivativePowerSeries
    ; inverseSucReal
    ; naturalReal
    ; naturalTimesInverseSucReal-cancel
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Elementary.CoefficientBounds
  using
    ( inverseSucRealBoundOne
    ; oneBoundOne
    ; zeroBound
    ; zeroBoundOne
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds
  using
    ( reciprocalFactorial⁺
    ; factorialMajorantRadius
    ; factorialMajorantTerm
    ; factorialMajorantTerm-nonnegative
    ; factorialMajorantModulus
    ; factorialMajorantTailBound
    ; factorialMajorantModulusAntitone
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

open import Constructive.Analysis.Reals.PowerSeries.Elementary.Trigonometric.Coefficients

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
