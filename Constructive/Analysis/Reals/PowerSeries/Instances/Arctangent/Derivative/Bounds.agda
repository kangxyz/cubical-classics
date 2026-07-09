{-

Strict-subball bounds for the second formal derivative of atanh

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Derivative.Bounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; suc)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
  using (scalarMulᶜ-rational)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using (derivativePowerSeries ; derivativePowerSeries-cong)
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.Internal
  using
    ( derivativeStrictSubballModulus
    ; derivativeStrictSubballScale
    ; positiveRationalSelfBounded
    )
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.StrictSubball
  using
    ( derivativePowerSeriesMajorizedOnStrictSubballFromMajorizedOnBall
    ; derivativePowerSeriesStrictSubballMajorant
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Coefficients
  using
    ( atanhPowerSeries
    ; derivativePowerSeries-atanh
    ; evenGeometricPowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Majorants
  using (evenGeometricPowerSeriesMajorizedOnBall)
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using (PowerSeriesMajorizedOnBall ; powerSeriesMajorizedOnBall-cong)
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.SecondDerivativePartialSumBounds.Finite
  using (PowerSeriesSecondDerivativePartialSumsBoundOnBall)
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.SecondDerivativePartialSumBounds.MajorizedRational
  using
    ( powerSeriesSecondDerivativePartialSumsBoundOnBallFromMajorizedRationalBounds
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using
    ( positiveGeometricPowerModulus
    ; positiveGeometricTerm
    ; positivePower
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


atanhSecondDerivative-evenGeometricPath :
  (n : ℕ) →
  derivativePowerSeries (derivativePowerSeries atanhPowerSeries) n ≡
  derivativePowerSeries evenGeometricPowerSeries n
atanhSecondDerivative-evenGeometricPath =
  derivativePowerSeries-cong derivativePowerSeries-atanh


atanhSecondDerivativeMajorantBound :
  {rho sigma : ℚ⁺} →
  (rho<sigma : radius rho ℚOrder.< radius sigma) →
  (n : ℕ) →
  BoundedByᶜ
    (derivativeStrictSubballScale rho sigma rho<sigma *⁺
      positivePower sigma (suc n))
    (derivativePowerSeriesStrictSubballMajorant
      rho<sigma
      (positiveGeometricTerm sigma)
      n)
atanhSecondDerivativeMajorantBound
  {rho = rho}
  {sigma = sigma}
  rho<sigma
  n =
  subst
    (BoundedByᶜ bound)
    (sym
      (scalarMulᶜ-rational
        (radius (derivativeStrictSubballScale rho sigma rho<sigma))
        (radius (positivePower sigma (suc n)))))
    (positiveRationalSelfBounded bound)
  where
  bound : ℚ⁺
  bound =
    derivativeStrictSubballScale rho sigma rho<sigma *⁺
    positivePower sigma (suc n)


atanhSecondDerivativeMajorizedOnStrictSubball :
  {rho sigma : ℚ⁺} →
  (rho<sigma : radius rho ℚOrder.< radius sigma) →
  (sigma<1 : radius sigma ℚOrder.< Rational.1ℚ) →
  PowerSeriesMajorizedOnBall
    (derivativePowerSeries (derivativePowerSeries atanhPowerSeries))
    rho
    (derivativePowerSeriesStrictSubballMajorant
      rho<sigma
      (positiveGeometricTerm sigma))
    (derivativeStrictSubballModulus
      rho<sigma
      (positiveGeometricPowerModulus sigma sigma<1))
atanhSecondDerivativeMajorizedOnStrictSubball
  {rho = rho}
  {sigma = sigma}
  rho<sigma
  sigma<1 =
  powerSeriesMajorizedOnBall-cong
    (λ n → sym (atanhSecondDerivative-evenGeometricPath n))
    (derivativePowerSeriesMajorizedOnStrictSubballFromMajorizedOnBall
      rho<sigma
      (evenGeometricPowerSeriesMajorizedOnBall sigma sigma<1))


atanhSecondDerivativePartialSumsBoundOnStrictSubball :
  {rho sigma : ℚ⁺} →
  (rho<sigma : radius rho ℚOrder.< radius sigma) →
  (sigma<1 : radius sigma ℚOrder.< Rational.1ℚ) →
  PowerSeriesSecondDerivativePartialSumsBoundOnBall atanhPowerSeries rho
atanhSecondDerivativePartialSumsBoundOnStrictSubball
  {rho = rho}
  {sigma = sigma}
  rho<sigma
  sigma<1 =
  powerSeriesSecondDerivativePartialSumsBoundOnBallFromMajorizedRationalBounds
    (atanhSecondDerivativeMajorizedOnStrictSubball rho<sigma sigma<1)
    (atanhSecondDerivativeMajorantBound rho<sigma)
