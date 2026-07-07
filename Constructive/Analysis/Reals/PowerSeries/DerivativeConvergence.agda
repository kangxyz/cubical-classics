{-

Convergence transport for formal derivative coefficients

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero)
open import Cubical.Data.Rationals using (ℚ)

open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals


derivativePowerSeriesOnBallWithFromCoefficientPath :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  ((n : ℕ) → derivativePowerSeries a n ≡ b n) →
  HasPowerSeriesOnBallWith b ρ μ →
  HasPowerSeriesOnBallWith (derivativePowerSeries a) ρ μ
derivativePowerSeriesOnBallWithFromCoefficientPath {a = a} {b = b} coeff≡ =
  hasPowerSeriesOnBallWith-cong
    {a = b}
    {b = derivativePowerSeries a}
    (λ n → sym (coeff≡ n))


derivativePowerSeriesOnBallFromCoefficientPath :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  ((n : ℕ) → derivativePowerSeries a n ≡ b n) →
  HasPowerSeriesOnBall b ρ →
  HasPowerSeriesOnBall (derivativePowerSeries a) ρ
derivativePowerSeriesOnBallFromCoefficientPath {a = a} {b = b} coeff≡ =
  hasPowerSeriesOnBall-cong
    {a = b}
    {b = derivativePowerSeries a}
    (λ n → sym (coeff≡ n))


derivativePowerSeriesRadiusFromCoefficientPath :
  {a b : PowerSeries} →
  {R : ℚ⁺} →
  ((n : ℕ) → derivativePowerSeries a n ≡ b n) →
  HasPowerSeriesRadius b R →
  HasPowerSeriesRadius (derivativePowerSeries a) R
derivativePowerSeriesRadiusFromCoefficientPath {a = a} {b = b} coeff≡ =
  hasPowerSeriesRadius-cong
    {a = b}
    {b = derivativePowerSeries a}
    (λ n → sym (coeff≡ n))


derivativePowerSeriesInfiniteRadiusFromCoefficientPath :
  {a b : PowerSeries} →
  ((n : ℕ) → derivativePowerSeries a n ≡ b n) →
  HasInfinitePowerSeriesRadius b →
  HasInfinitePowerSeriesRadius (derivativePowerSeries a)
derivativePowerSeriesInfiniteRadiusFromCoefficientPath {a = a} {b = b} coeff≡ =
  hasInfinitePowerSeriesRadius-cong
    {a = b}
    {b = derivativePowerSeries a}
    (λ n → sym (coeff≡ n))


primitivePowerSeriesOnBallWithFromCoefficientPath :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  ((n : ℕ) → primitivePowerSeries a n ≡ b n) →
  HasPowerSeriesOnBallWith b ρ μ →
  HasPowerSeriesOnBallWith (primitivePowerSeries a) ρ μ
primitivePowerSeriesOnBallWithFromCoefficientPath {a = a} {b = b} coeff≡ =
  hasPowerSeriesOnBallWith-cong
    {a = b}
    {b = primitivePowerSeries a}
    (λ n → sym (coeff≡ n))


primitivePowerSeriesOnBallFromCoefficientPath :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  ((n : ℕ) → primitivePowerSeries a n ≡ b n) →
  HasPowerSeriesOnBall b ρ →
  HasPowerSeriesOnBall (primitivePowerSeries a) ρ
primitivePowerSeriesOnBallFromCoefficientPath {a = a} {b = b} coeff≡ =
  hasPowerSeriesOnBall-cong
    {a = b}
    {b = primitivePowerSeries a}
    (λ n → sym (coeff≡ n))


primitivePowerSeriesRadiusFromCoefficientPath :
  {a b : PowerSeries} →
  {R : ℚ⁺} →
  ((n : ℕ) → primitivePowerSeries a n ≡ b n) →
  HasPowerSeriesRadius b R →
  HasPowerSeriesRadius (primitivePowerSeries a) R
primitivePowerSeriesRadiusFromCoefficientPath {a = a} {b = b} coeff≡ =
  hasPowerSeriesRadius-cong
    {a = b}
    {b = primitivePowerSeries a}
    (λ n → sym (coeff≡ n))


primitivePowerSeriesInfiniteRadiusFromCoefficientPath :
  {a b : PowerSeries} →
  ((n : ℕ) → primitivePowerSeries a n ≡ b n) →
  HasInfinitePowerSeriesRadius b →
  HasInfinitePowerSeriesRadius (primitivePowerSeries a)
primitivePowerSeriesInfiniteRadiusFromCoefficientPath {a = a} {b = b} coeff≡ =
  hasInfinitePowerSeriesRadius-cong
    {a = b}
    {b = primitivePowerSeries a}
    (λ n → sym (coeff≡ n))


derivativeZeroPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (derivativePowerSeries zeroPowerSeries)
derivativeZeroPowerSeriesInfiniteRadius =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = zeroPowerSeries}
    {b = zeroPowerSeries}
    derivativePowerSeries-zero
    zeroPowerSeriesInfiniteRadius


derivativeConstantPowerSeriesInfiniteRadius :
  (c : ℝᶜ) →
  HasInfinitePowerSeriesRadius (derivativePowerSeries (constantPowerSeries c))
derivativeConstantPowerSeriesInfiniteRadius c =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = constantPowerSeries c}
    {b = zeroPowerSeries}
    (derivativePowerSeries-constant c)
    zeroPowerSeriesInfiniteRadius


derivativePrimitivePowerSeriesRadius :
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius (derivativePowerSeries (primitivePowerSeries a)) R
derivativePrimitivePowerSeriesRadius {a = a} =
  derivativePowerSeriesRadiusFromCoefficientPath
    {a = primitivePowerSeries a}
    {b = a}
    (derivativePrimitivePowerSeries a)


derivativePrimitivePowerSeriesInfiniteRadius :
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius (derivativePowerSeries (primitivePowerSeries a))
derivativePrimitivePowerSeriesInfiniteRadius {a = a} =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = primitivePowerSeries a}
    {b = a}
    (derivativePrimitivePowerSeries a)


derivativeNegPowerSeriesRadius :
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius (derivativePowerSeries a) R →
  HasPowerSeriesRadius (derivativePowerSeries (negPowerSeries a)) R
derivativeNegPowerSeriesRadius {a = a} radiusData =
  derivativePowerSeriesRadiusFromCoefficientPath
    {a = negPowerSeries a}
    {b = negPowerSeries (derivativePowerSeries a)}
    (derivativePowerSeries-neg a)
    (negPowerSeriesRadius radiusData)


derivativeNegPowerSeriesInfiniteRadius :
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius (derivativePowerSeries a) →
  HasInfinitePowerSeriesRadius (derivativePowerSeries (negPowerSeries a))
derivativeNegPowerSeriesInfiniteRadius {a = a} radiusData =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = negPowerSeries a}
    {b = negPowerSeries (derivativePowerSeries a)}
    (derivativePowerSeries-neg a)
    (negPowerSeriesInfiniteRadius radiusData)


derivativeAddPowerSeriesRadius :
  {a b : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius (derivativePowerSeries a) R →
  HasPowerSeriesRadius (derivativePowerSeries b) R →
  HasPowerSeriesRadius (derivativePowerSeries (addPowerSeries a b)) R
derivativeAddPowerSeriesRadius {a = a} {b = b} left right =
  derivativePowerSeriesRadiusFromCoefficientPath
    {a = addPowerSeries a b}
    {b = addPowerSeries (derivativePowerSeries a) (derivativePowerSeries b)}
    (derivativePowerSeries-add a b)
    (addPowerSeriesRadius left right)


derivativeAddPowerSeriesInfiniteRadius :
  {a b : PowerSeries} →
  HasInfinitePowerSeriesRadius (derivativePowerSeries a) →
  HasInfinitePowerSeriesRadius (derivativePowerSeries b) →
  HasInfinitePowerSeriesRadius (derivativePowerSeries (addPowerSeries a b))
derivativeAddPowerSeriesInfiniteRadius {a = a} {b = b} left right =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = addPowerSeries a b}
    {b = addPowerSeries (derivativePowerSeries a) (derivativePowerSeries b)}
    (derivativePowerSeries-add a b)
    (addPowerSeriesInfiniteRadius left right)


derivativeSubPowerSeriesRadius :
  {a b : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius (derivativePowerSeries a) R →
  HasPowerSeriesRadius (derivativePowerSeries b) R →
  HasPowerSeriesRadius (derivativePowerSeries (subPowerSeries a b)) R
derivativeSubPowerSeriesRadius {a = a} {b = b} left right =
  derivativePowerSeriesRadiusFromCoefficientPath
    {a = subPowerSeries a b}
    {b = subPowerSeries (derivativePowerSeries a) (derivativePowerSeries b)}
    (derivativePowerSeries-sub a b)
    (subPowerSeriesRadius left right)


derivativeSubPowerSeriesInfiniteRadius :
  {a b : PowerSeries} →
  HasInfinitePowerSeriesRadius (derivativePowerSeries a) →
  HasInfinitePowerSeriesRadius (derivativePowerSeries b) →
  HasInfinitePowerSeriesRadius (derivativePowerSeries (subPowerSeries a b))
derivativeSubPowerSeriesInfiniteRadius {a = a} {b = b} left right =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = subPowerSeries a b}
    {b = subPowerSeries (derivativePowerSeries a) (derivativePowerSeries b)}
    (derivativePowerSeries-sub a b)
    (subPowerSeriesInfiniteRadius left right)


derivativeRationalScalePowerSeriesRadius :
  (q : ℚ) →
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius (derivativePowerSeries a) R →
  HasPowerSeriesRadius
    (derivativePowerSeries (rationalScalePowerSeries q a))
    R
derivativeRationalScalePowerSeriesRadius q {a = a} radiusData =
  derivativePowerSeriesRadiusFromCoefficientPath
    {a = rationalScalePowerSeries q a}
    {b = rationalScalePowerSeries q (derivativePowerSeries a)}
    (derivativePowerSeries-rationalScale q a)
    (rationalScalePowerSeriesRadius q radiusData)


derivativeRationalScalePowerSeriesInfiniteRadius :
  (q : ℚ) →
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius (derivativePowerSeries a) →
  HasInfinitePowerSeriesRadius
    (derivativePowerSeries (rationalScalePowerSeries q a))
derivativeRationalScalePowerSeriesInfiniteRadius q {a = a} radiusData =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = rationalScalePowerSeries q a}
    {b = rationalScalePowerSeries q (derivativePowerSeries a)}
    (derivativePowerSeries-rationalScale q a)
    (rationalScalePowerSeriesInfiniteRadius q radiusData)


primitiveZeroPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (primitivePowerSeries zeroPowerSeries)
primitiveZeroPowerSeriesInfiniteRadius =
  primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = zeroPowerSeries}
    {b = zeroPowerSeries}
    primitivePowerSeries-zero
    zeroPowerSeriesInfiniteRadius


primitiveDerivativePowerSeriesRadius :
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius (primitivePowerSeries (derivativePowerSeries a)) R
primitiveDerivativePowerSeriesRadius {a = a} radiusData =
  primitivePowerSeriesRadiusFromCoefficientPath
    {a = derivativePowerSeries a}
    {b = subPowerSeries a (constantPowerSeries (a zero))}
    (primitiveDerivativePowerSeries a)
    (subPowerSeriesRadius radiusData (constantPowerSeriesRadius (a zero)))


primitiveDerivativePowerSeriesInfiniteRadius :
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius (primitivePowerSeries (derivativePowerSeries a))
primitiveDerivativePowerSeriesInfiniteRadius {a = a} radiusData =
  primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = derivativePowerSeries a}
    {b = subPowerSeries a (constantPowerSeries (a zero))}
    (primitiveDerivativePowerSeries a)
    (subPowerSeriesInfiniteRadius
      radiusData
      (constantPowerSeriesInfiniteRadius (a zero)))


primitiveNegPowerSeriesRadius :
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius (primitivePowerSeries a) R →
  HasPowerSeriesRadius (primitivePowerSeries (negPowerSeries a)) R
primitiveNegPowerSeriesRadius {a = a} radiusData =
  primitivePowerSeriesRadiusFromCoefficientPath
    {a = negPowerSeries a}
    {b = negPowerSeries (primitivePowerSeries a)}
    (primitivePowerSeries-neg a)
    (negPowerSeriesRadius radiusData)


primitiveNegPowerSeriesInfiniteRadius :
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius (primitivePowerSeries a) →
  HasInfinitePowerSeriesRadius (primitivePowerSeries (negPowerSeries a))
primitiveNegPowerSeriesInfiniteRadius {a = a} radiusData =
  primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = negPowerSeries a}
    {b = negPowerSeries (primitivePowerSeries a)}
    (primitivePowerSeries-neg a)
    (negPowerSeriesInfiniteRadius radiusData)


primitiveAddPowerSeriesRadius :
  {a b : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius (primitivePowerSeries a) R →
  HasPowerSeriesRadius (primitivePowerSeries b) R →
  HasPowerSeriesRadius (primitivePowerSeries (addPowerSeries a b)) R
primitiveAddPowerSeriesRadius {a = a} {b = b} left right =
  primitivePowerSeriesRadiusFromCoefficientPath
    {a = addPowerSeries a b}
    {b = addPowerSeries (primitivePowerSeries a) (primitivePowerSeries b)}
    (primitivePowerSeries-add a b)
    (addPowerSeriesRadius left right)


primitiveAddPowerSeriesInfiniteRadius :
  {a b : PowerSeries} →
  HasInfinitePowerSeriesRadius (primitivePowerSeries a) →
  HasInfinitePowerSeriesRadius (primitivePowerSeries b) →
  HasInfinitePowerSeriesRadius (primitivePowerSeries (addPowerSeries a b))
primitiveAddPowerSeriesInfiniteRadius {a = a} {b = b} left right =
  primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = addPowerSeries a b}
    {b = addPowerSeries (primitivePowerSeries a) (primitivePowerSeries b)}
    (primitivePowerSeries-add a b)
    (addPowerSeriesInfiniteRadius left right)


primitiveSubPowerSeriesRadius :
  {a b : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius (primitivePowerSeries a) R →
  HasPowerSeriesRadius (primitivePowerSeries b) R →
  HasPowerSeriesRadius (primitivePowerSeries (subPowerSeries a b)) R
primitiveSubPowerSeriesRadius {a = a} {b = b} left right =
  primitivePowerSeriesRadiusFromCoefficientPath
    {a = subPowerSeries a b}
    {b = subPowerSeries (primitivePowerSeries a) (primitivePowerSeries b)}
    (primitivePowerSeries-sub a b)
    (subPowerSeriesRadius left right)


primitiveSubPowerSeriesInfiniteRadius :
  {a b : PowerSeries} →
  HasInfinitePowerSeriesRadius (primitivePowerSeries a) →
  HasInfinitePowerSeriesRadius (primitivePowerSeries b) →
  HasInfinitePowerSeriesRadius (primitivePowerSeries (subPowerSeries a b))
primitiveSubPowerSeriesInfiniteRadius {a = a} {b = b} left right =
  primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = subPowerSeries a b}
    {b = subPowerSeries (primitivePowerSeries a) (primitivePowerSeries b)}
    (primitivePowerSeries-sub a b)
    (subPowerSeriesInfiniteRadius left right)


primitiveRationalScalePowerSeriesRadius :
  (q : ℚ) →
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius (primitivePowerSeries a) R →
  HasPowerSeriesRadius
    (primitivePowerSeries (rationalScalePowerSeries q a))
    R
primitiveRationalScalePowerSeriesRadius q {a = a} radiusData =
  primitivePowerSeriesRadiusFromCoefficientPath
    {a = rationalScalePowerSeries q a}
    {b = rationalScalePowerSeries q (primitivePowerSeries a)}
    (primitivePowerSeries-rationalScale q a)
    (rationalScalePowerSeriesRadius q radiusData)


primitiveRationalScalePowerSeriesInfiniteRadius :
  (q : ℚ) →
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius (primitivePowerSeries a) →
  HasInfinitePowerSeriesRadius
    (primitivePowerSeries (rationalScalePowerSeries q a))
primitiveRationalScalePowerSeriesInfiniteRadius q {a = a} radiusData =
  primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = rationalScalePowerSeries q a}
    {b = rationalScalePowerSeries q (primitivePowerSeries a)}
    (primitivePowerSeries-rationalScale q a)
    (rationalScalePowerSeriesInfiniteRadius q radiusData)
