{-

Part of Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.Primitive where

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
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (neg-zeroᶜ)
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
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
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; inverseSucReal
    ; naturalReal
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct
  using (cauchyProductPowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( bounded-byᶜ-zero
    ; addPowerSeries
    ; constantPowerSeries
    ; negPowerSeries
    ; powerSeriesPartialSum-shift
    ; rationalScalePowerSeries
    ; shiftPowerSeries
    ; subPowerSeries
    ; tailSum-zero-sequence
    ; zeroPowerSeries
    )
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.Internal
open import Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.FiniteSupport
open import Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.Closure
open import Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.FiniteSeries
open import Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.Derivative

primitivePowerSeriesZeroAfter :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  PowerSeriesZeroAfter (primitivePowerSeries a) (suc N)
primitivePowerSeriesZeroAfter N zeroAfter zero sucN≤0 =
  Empty.rec (NatOrder.¬-<-zero sucN≤0)
primitivePowerSeriesZeroAfter N zeroAfter (suc n) sucN≤sucn =
  cong
    (λ c → inverseSucReal n ·ᶜ c)
    (zeroAfter n (NatOrder.pred-≤-pred sucN≤sucn)) ∙
  mulᶜ-zero-right (inverseSucReal n)


primitivePowerSeriesPolynomial :
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  IsPolynomialPowerSeries (primitivePowerSeries a)
primitivePowerSeriesPolynomial (N , zeroAfter) =
  suc N , primitivePowerSeriesZeroAfter N zeroAfter


finitePowerSeriesFormalPrimitiveEval :
  (N : ℕ) →
  (Fin N → ℝᶜ) →
  ℝᶜ →
  ℝᶜ
finitePowerSeriesFormalPrimitiveEval N coeff h =
  powerSeriesPartialSum
    (primitivePowerSeries (finitePowerSeries N coeff))
    h
    (suc N)


finitePowerSeriesFormalPrimitiveOnBallWith :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBallWith
    (primitivePowerSeries (finitePowerSeries N coeff))
    ρ
    (λ _ → suc N)
finitePowerSeriesFormalPrimitiveOnBallWith N coeff =
  finiteSupportPowerSeriesOnBallWith
    (suc N)
    (primitivePowerSeriesZeroAfter N (finitePowerSeriesZeroAfter N coeff))


finitePowerSeriesFormalPrimitiveSumOnBall-eval :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  {ρ : ℚ⁺} →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (primitivePowerSeries (finitePowerSeries N coeff))
    ρ
    (λ _ → suc N)
    (finitePowerSeriesFormalPrimitiveOnBallWith N coeff)
    h
    h-bound
  ≡ finitePowerSeriesFormalPrimitiveEval N coeff h
finitePowerSeriesFormalPrimitiveSumOnBall-eval N coeff h h-bound =
  powerSeriesSumOnBall-constantModulusPartialSum
    (suc N)
    (finitePowerSeriesFormalPrimitiveOnBallWith N coeff)
    h
    h-bound


centeredFinitePowerSeriesFormalPrimitiveSumOnBall-eval :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  centeredPowerSeriesSumOnBall
    (primitivePowerSeries (finitePowerSeries N coeff))
    c
    ρ
    (λ _ → suc N)
    (finitePowerSeriesFormalPrimitiveOnBallWith N coeff)
    x
    inBall
  ≡ finitePowerSeriesFormalPrimitiveEval N coeff (centeredDisplacement c x)
centeredFinitePowerSeriesFormalPrimitiveSumOnBall-eval N coeff c x inBall =
  centeredPowerSeriesSumOnBall-constantModulusPartialSum
    (suc N)
    (finitePowerSeriesFormalPrimitiveOnBallWith N coeff)
    x
    inBall


finitePowerSeriesFormalPrimitiveHasPowerSeriesAtWith :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesAtWith
    (λ x →
      finitePowerSeriesFormalPrimitiveEval
        N
        coeff
        (centeredDisplacement c x))
    c
    (primitivePowerSeries (finitePowerSeries N coeff))
    ρ
    (λ _ → suc N)
finitePowerSeriesFormalPrimitiveHasPowerSeriesAtWith N coeff c =
  finitePowerSeriesFormalPrimitiveOnBallWith N coeff ,
  λ x inBall →
    sym
      (centeredFinitePowerSeriesFormalPrimitiveSumOnBall-eval
        N
        coeff
        c
        x
        inBall)


finitePowerSeriesFormalPrimitiveHasPowerSeriesAtOnBall :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  HasPowerSeriesAtOnBall
    (λ x →
      finitePowerSeriesFormalPrimitiveEval
        N
        coeff
        (centeredDisplacement c x))
    c
    (primitivePowerSeries (finitePowerSeries N coeff))
    ρ
finitePowerSeriesFormalPrimitiveHasPowerSeriesAtOnBall N coeff c ρ =
  (λ _ → suc N) ,
  finitePowerSeriesFormalPrimitiveHasPowerSeriesAtWith N coeff c


finitePowerSeriesFormalPrimitiveHasPowerSeriesAt :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  HasPowerSeriesAt
    (λ x →
      finitePowerSeriesFormalPrimitiveEval
        N
        coeff
        (centeredDisplacement c x))
    c
    (primitivePowerSeries (finitePowerSeries N coeff))
finitePowerSeriesFormalPrimitiveHasPowerSeriesAt N coeff c =
  1⁺ ,
  finitePowerSeriesFormalPrimitiveHasPowerSeriesAtOnBall N coeff c 1⁺


finitePowerSeriesFormalPrimitiveAnalyticAt :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  AnalyticAt
    (λ x →
      finitePowerSeriesFormalPrimitiveEval
        N
        coeff
        (centeredDisplacement c x))
    c
finitePowerSeriesFormalPrimitiveAnalyticAt N coeff c =
  primitivePowerSeries (finitePowerSeries N coeff) ,
  finitePowerSeriesFormalPrimitiveHasPowerSeriesAt N coeff c


primitivePowerSeriesPolynomialInfiniteRadius :
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  HasInfinitePowerSeriesRadius (primitivePowerSeries a)
primitivePowerSeriesPolynomialInfiniteRadius poly =
  polynomialPowerSeriesInfiniteRadius (primitivePowerSeriesPolynomial poly)
