{-

Part of Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.Derivative where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (neg-zeroᶜ)
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using
    ( AnalyticAt
    ; HasPowerSeriesAt
    ; HasPowerSeriesAtOnBall
    ; HasPowerSeriesAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using
    ( derivativePowerSeries
    ; naturalReal
    )
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.FiniteSupport
open import Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.Closure
open import Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.FiniteSeries

derivativePowerSeriesZeroAfter :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a (suc N) →
  PowerSeriesZeroAfter (derivativePowerSeries a) N
derivativePowerSeriesZeroAfter N zeroAfter n N≤n =
  cong
    (λ c → naturalReal (suc n) ·ᶜ c)
    (zeroAfter (suc n) (NatOrder.suc-≤-suc N≤n)) ∙
  mulᶜ-zero-right (naturalReal (suc n))


derivativePowerSeriesZeroAfterZero :
  {a : PowerSeries} →
  PowerSeriesZeroAfter a zero →
  PowerSeriesZeroAfter (derivativePowerSeries a) zero
derivativePowerSeriesZeroAfterZero zeroAfter n _ =
  cong
    (λ c → naturalReal (suc n) ·ᶜ c)
    (zeroAfter (suc n) NatOrder.zero-≤) ∙
  mulᶜ-zero-right (naturalReal (suc n))


derivativePowerSeriesPolynomial :
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  IsPolynomialPowerSeries (derivativePowerSeries a)
derivativePowerSeriesPolynomial (zero , zeroAfter) =
  zero , derivativePowerSeriesZeroAfterZero zeroAfter
derivativePowerSeriesPolynomial (suc N , zeroAfter) =
  N , derivativePowerSeriesZeroAfter N zeroAfter


derivativeFinitePowerSeriesZeroAfterLength :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  PowerSeriesZeroAfter (derivativePowerSeries (finitePowerSeries N coeff)) N
derivativeFinitePowerSeriesZeroAfterLength zero coeff =
  derivativePowerSeriesZeroAfterZero
    (finitePowerSeriesZeroAfter zero coeff)
derivativeFinitePowerSeriesZeroAfterLength (suc N) coeff =
  powerSeriesZeroAfter-weaken
    (suc zero , refl)
    (derivativePowerSeriesZeroAfter
      N
      (finitePowerSeriesZeroAfter (suc N) coeff))


finitePowerSeriesFormalDerivativeEval :
  (N : ℕ) →
  (Fin N → ℝᶜ) →
  ℝᶜ →
  ℝᶜ
finitePowerSeriesFormalDerivativeEval N coeff h =
  powerSeriesPartialSum
    (derivativePowerSeries (finitePowerSeries N coeff))
    h
    N


finitePowerSeriesFormalDerivativeOnBallWith :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBallWith
    (derivativePowerSeries (finitePowerSeries N coeff))
    ρ
    (λ _ → N)
finitePowerSeriesFormalDerivativeOnBallWith N coeff =
  finiteSupportPowerSeriesOnBallWith
    N
    (derivativeFinitePowerSeriesZeroAfterLength N coeff)


finitePowerSeriesFormalDerivativeSumOnBall-eval :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  {ρ : ℚ⁺} →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (derivativePowerSeries (finitePowerSeries N coeff))
    ρ
    (λ _ → N)
    (finitePowerSeriesFormalDerivativeOnBallWith N coeff)
    h
    h-bound
  ≡ finitePowerSeriesFormalDerivativeEval N coeff h
finitePowerSeriesFormalDerivativeSumOnBall-eval N coeff h h-bound =
  powerSeriesSumOnBall-constantModulusPartialSum
    N
    (finitePowerSeriesFormalDerivativeOnBallWith N coeff)
    h
    h-bound


centeredFinitePowerSeriesFormalDerivativeSumOnBall-eval :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  centeredPowerSeriesSumOnBall
    (derivativePowerSeries (finitePowerSeries N coeff))
    c
    ρ
    (λ _ → N)
    (finitePowerSeriesFormalDerivativeOnBallWith N coeff)
    x
    inBall
  ≡ finitePowerSeriesFormalDerivativeEval N coeff (centeredDisplacement c x)
centeredFinitePowerSeriesFormalDerivativeSumOnBall-eval N coeff c x inBall =
  centeredPowerSeriesSumOnBall-constantModulusPartialSum
    N
    (finitePowerSeriesFormalDerivativeOnBallWith N coeff)
    x
    inBall


finitePowerSeriesFormalDerivativeHasPowerSeriesAtWith :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesAtWith
    (λ x →
      finitePowerSeriesFormalDerivativeEval
        N
        coeff
        (centeredDisplacement c x))
    c
    (derivativePowerSeries (finitePowerSeries N coeff))
    ρ
    (λ _ → N)
finitePowerSeriesFormalDerivativeHasPowerSeriesAtWith N coeff c =
  finitePowerSeriesFormalDerivativeOnBallWith N coeff ,
  λ x inBall →
    sym
      (centeredFinitePowerSeriesFormalDerivativeSumOnBall-eval
        N
        coeff
        c
        x
        inBall)


finitePowerSeriesFormalDerivativeHasPowerSeriesAtOnBall :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  HasPowerSeriesAtOnBall
    (λ x →
      finitePowerSeriesFormalDerivativeEval
        N
        coeff
        (centeredDisplacement c x))
    c
    (derivativePowerSeries (finitePowerSeries N coeff))
    ρ
finitePowerSeriesFormalDerivativeHasPowerSeriesAtOnBall N coeff c ρ =
  (λ _ → N) ,
  finitePowerSeriesFormalDerivativeHasPowerSeriesAtWith N coeff c


finitePowerSeriesFormalDerivativeHasPowerSeriesAt :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  HasPowerSeriesAt
    (λ x →
      finitePowerSeriesFormalDerivativeEval
        N
        coeff
        (centeredDisplacement c x))
    c
    (derivativePowerSeries (finitePowerSeries N coeff))
finitePowerSeriesFormalDerivativeHasPowerSeriesAt N coeff c =
  1⁺ ,
  finitePowerSeriesFormalDerivativeHasPowerSeriesAtOnBall N coeff c 1⁺


finitePowerSeriesFormalDerivativeAnalyticAt :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  AnalyticAt
    (λ x →
      finitePowerSeriesFormalDerivativeEval
        N
        coeff
        (centeredDisplacement c x))
    c
finitePowerSeriesFormalDerivativeAnalyticAt N coeff c =
  derivativePowerSeries (finitePowerSeries N coeff) ,
  finitePowerSeriesFormalDerivativeHasPowerSeriesAt N coeff c


derivativePowerSeriesPolynomialInfiniteRadius :
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  HasInfinitePowerSeriesRadius (derivativePowerSeries a)
derivativePowerSeriesPolynomialInfiniteRadius poly =
  polynomialPowerSeriesInfiniteRadius (derivativePowerSeriesPolynomial poly)
