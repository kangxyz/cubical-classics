{-

Convergence transport for formal derivative coefficients

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.Closure where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
  using (0ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using
    ( _·ᶜ_
    ; mulᶜ-comm
    ; mulᶜ-zero-left
    ; mulᶜ-rational-left
    ; mulᶜ-rational-left-assoc
    ; mulᶜ-rational-rational
    ; mulᶜ-rational-right
    ; mulᶜ-rational-right-assoc
    ; mulᶜ-comm-rational-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_ ; neg-rational)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarOrder
  using (scalarMulᶜ-pres≤ᶜ-nonnegative)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using
    ( bounded-byᶜ-mul
    ; mulᶜ-pres≤ᶜ-right
    ; mulᶜ≤abs-product
    ; neg-mulᶜ≤abs-product
    ; scalarMulᶜ-nonnegative
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
  using
    ( scalarMulᶜ
    ; scalarMulᶜ-assoc
    ; scalarMulᶜ-neg-real
    ; scalarMulᶜ-one
    )
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-refl ; ≤ᶜ-trans)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using
    ( BoundedByᶜ
    ; rational-bound→boundedᶜ
    ; rational-closed-boundᶜ
    ; rational-closed-bound→boundedᶜ
    ; scalar-bound-rational-boundᶜ
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using
    ( absᶜ
    ; absᶜ-least
    ; absᶜ-nonnegative
    ; ≤ᶜabsᶜ-left
    ; ≤ᶜabsᶜ-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
  using (≤ℚ→rational≤ᶜ)
open import Constructive.Analysis.Reals.Series
  using
    ( SeriesMajorizedBy
    ; TailBound
    ; drop
    ; tailBound-drop
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Majorant
  using (bounded-byᶜ-abs)
open import Constructive.Analysis.GeometricDecay
  using
    ( positiveGeometricGap
    ; positiveGeometricPower-linear-bound
    ; positivePower
    ; positivePower-radius
    ; positiveRationalPower-nonnegative
    )
open import Constructive.Analysis.GeometricDecay.Rational
  using (rationalPower)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using
    ( PowerSeriesMajorizedOnBall
    ; hasPowerSeriesOnBallFromBoundedTerms
    ; hasPowerSeriesOnBallFromTermBounds
    ; hasPowerSeriesOnBallWithFromBoundedTerms
    ; hasPowerSeriesOnBallWithFromTermBounds
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.Core
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.StrictSubball.OnBall


derivativePowerSeriesRadius :
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius (derivativePowerSeries a) R
derivativePowerSeriesRadius {a = a} {R = R} radiusData =
  hasPowerSeriesRadius
    {a = derivativePowerSeries a}
    {R = R}
    (λ ρ ρ<R →
      derivativePowerSeriesOnStrictSubball
        {a = a}
        {ρ = ρ}
        {σ = middleRadius ρ ρ<R}
        (ρ<middle ρ ρ<R)
        (HasPowerSeriesRadius.onSubball
          radiusData
          (middleRadius ρ ρ<R)
          (middle<R ρ ρ<R)))
  where
  middle-positive :
    (ρ : ℚ⁺) →
    (ρ<R : radius ρ ℚOrder.< radius R) →
    Rational.0ℚ ℚOrder.< Rational.middle (radius ρ) (radius R)
  middle-positive ρ ρ<R =
    Rational.≤<-trans
      {p = Rational.0ℚ}
      {q = radius ρ}
      {r = Rational.middle (radius ρ) (radius R)}
      (Rational.<→≤ {p = Rational.0ℚ} {q = radius ρ} (ρ .snd))
      (Rational.middle>l {p = radius ρ} {q = radius R} ρ<R)

  middleRadius :
    (ρ : ℚ⁺) →
    radius ρ ℚOrder.< radius R →
    ℚ⁺
  middleRadius ρ ρ<R =
    Rational.middle (radius ρ) (radius R) ,
    middle-positive ρ ρ<R

  ρ<middle :
    (ρ : ℚ⁺) →
    (ρ<R : radius ρ ℚOrder.< radius R) →
    radius ρ ℚOrder.< radius (middleRadius ρ ρ<R)
  ρ<middle ρ ρ<R =
    Rational.middle>l {p = radius ρ} {q = radius R} ρ<R

  middle<R :
    (ρ : ℚ⁺) →
    (ρ<R : radius ρ ℚOrder.< radius R) →
    radius (middleRadius ρ ρ<R) ℚOrder.< radius R
  middle<R ρ ρ<R =
    Rational.middle<r {p = radius ρ} {q = radius R} ρ<R


derivativePowerSeriesInfiniteRadius :
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius (derivativePowerSeries a)
derivativePowerSeriesInfiniteRadius {a = a} radiusData ρ =
  derivativePowerSeriesOnStrictSubball
    {a = a}
    {ρ = ρ}
    {σ = ρ +⁺ 1⁺}
    (summand-left<sum ρ 1⁺)
    (radiusData (ρ +⁺ 1⁺))


derivativePowerSeriesRadiusFromCoefficientBoundsAndMajorants :
  {a : PowerSeries} →
  {R : ℚ⁺} →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  ((ρ : ℚ⁺) →
    radius ρ ℚOrder.< radius R →
    DerivativePowerSeriesBoundMajorantOnBall κ ρ) →
  HasPowerSeriesRadius (derivativePowerSeries a) R
derivativePowerSeriesRadiusFromCoefficientBoundsAndMajorants
    {a = a}
    κ
    coefficientBounds
    majorants =
  hasPowerSeriesRadius
    {a = derivativePowerSeries a}
    (λ ρ ρ<R →
      derivativePowerSeriesOnBallFromCoefficientBoundsAndBoundMajorant
        {a = a}
        {ρ = ρ}
        κ
        coefficientBounds
        (majorants ρ ρ<R))


derivativePowerSeriesInfiniteRadiusFromCoefficientBoundsAndMajorants :
  {a : PowerSeries} →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  ((ρ : ℚ⁺) → DerivativePowerSeriesBoundMajorantOnBall κ ρ) →
  HasInfinitePowerSeriesRadius (derivativePowerSeries a)
derivativePowerSeriesInfiniteRadiusFromCoefficientBoundsAndMajorants
    {a = a}
    κ
    coefficientBounds
    majorants
    ρ =
  derivativePowerSeriesOnBallFromCoefficientBoundsAndBoundMajorant
    {a = a}
    {ρ = ρ}
    κ
    coefficientBounds
    (majorants ρ)


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


derivativeRealScalePowerSeriesRadius :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ x →
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius (derivativePowerSeries a) R →
  HasPowerSeriesRadius
    (derivativePowerSeries (realScalePowerSeries x a))
    R
derivativeRealScalePowerSeriesRadius x κ x-bound {a = a} radiusData =
  derivativePowerSeriesRadiusFromCoefficientPath
    {a = realScalePowerSeries x a}
    {b = realScalePowerSeries x (derivativePowerSeries a)}
    (derivativePowerSeries-realScale x a)
    (realScalePowerSeriesRadius x κ x-bound radiusData)


derivativeRealScalePowerSeriesInfiniteRadius :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ x →
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius (derivativePowerSeries a) →
  HasInfinitePowerSeriesRadius
    (derivativePowerSeries (realScalePowerSeries x a))
derivativeRealScalePowerSeriesInfiniteRadius x κ x-bound {a = a} radiusData =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = realScalePowerSeries x a}
    {b = realScalePowerSeries x (derivativePowerSeries a)}
    (derivativePowerSeries-realScale x a)
    (realScalePowerSeriesInfiniteRadius x κ x-bound radiusData)


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


primitiveRealScalePowerSeriesRadius :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ x →
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius (primitivePowerSeries a) R →
  HasPowerSeriesRadius
    (primitivePowerSeries (realScalePowerSeries x a))
    R
primitiveRealScalePowerSeriesRadius x κ x-bound {a = a} radiusData =
  primitivePowerSeriesRadiusFromCoefficientPath
    {a = realScalePowerSeries x a}
    {b = realScalePowerSeries x (primitivePowerSeries a)}
    (primitivePowerSeries-realScale x a)
    (realScalePowerSeriesRadius x κ x-bound radiusData)


primitiveRealScalePowerSeriesInfiniteRadius :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ x →
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius (primitivePowerSeries a) →
  HasInfinitePowerSeriesRadius
    (primitivePowerSeries (realScalePowerSeries x a))
primitiveRealScalePowerSeriesInfiniteRadius x κ x-bound {a = a} radiusData =
  primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = realScalePowerSeries x a}
    {b = realScalePowerSeries x (primitivePowerSeries a)}
    (primitivePowerSeries-realScale x a)
    (realScalePowerSeriesInfiniteRadius x κ x-bound radiusData)
