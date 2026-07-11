{-

Part of Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.FiniteSeries where

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
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( powerSeriesPartialSum-shift
    ; shiftPowerSeries
    )
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.FiniteSupport
open import Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.Closure

finitePowerSeries :
  (N : ℕ) →
  (Fin N → ℝᶜ) →
  PowerSeries
finitePowerSeries zero coeff n =
  0ᶜ
finitePowerSeries (suc N) coeff zero =
  coeff Fin.zero
finitePowerSeries (suc N) coeff (suc n) =
  finitePowerSeries N (λ i → coeff (Fin.suc i)) n


finitePowerSeriesEval :
  (N : ℕ) →
  (Fin N → ℝᶜ) →
  ℝᶜ →
  ℝᶜ
finitePowerSeriesEval zero coeff h =
  0ᶜ
finitePowerSeriesEval (suc N) coeff h =
  coeff Fin.zero +ᶜ
  h ·ᶜ finitePowerSeriesEval N (λ i → coeff (Fin.suc i)) h


shiftFinitePowerSeries :
  (N : ℕ) →
  (coeff : Fin (suc N) → ℝᶜ) →
  (n : ℕ) →
  shiftPowerSeries (finitePowerSeries (suc N) coeff) n ≡
  finitePowerSeries N (λ i → coeff (Fin.suc i)) n
shiftFinitePowerSeries N coeff n =
  refl


finitePowerSeriesEval-partialSum :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (h : ℝᶜ) →
  powerSeriesPartialSum (finitePowerSeries N coeff) h N ≡
  finitePowerSeriesEval N coeff h
finitePowerSeriesEval-partialSum zero coeff h =
  refl
finitePowerSeriesEval-partialSum (suc N) coeff h =
  powerSeriesPartialSum-shift (finitePowerSeries (suc N) coeff) h N ∙
  cong
    (λ s → coeff Fin.zero +ᶜ h ·ᶜ s)
    (powerSeriesPartialSum-cong
      (shiftFinitePowerSeries N coeff)
      refl
      N ∙
    finitePowerSeriesEval-partialSum
      N
      (λ i → coeff (Fin.suc i))
      h)


finitePowerSeriesZeroAfter :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  PowerSeriesZeroAfter (finitePowerSeries N coeff) N
finitePowerSeriesZeroAfter zero coeff n _ =
  refl
finitePowerSeriesZeroAfter (suc N) coeff zero sucN≤0 =
  Empty.rec (NatOrder.¬-<-zero sucN≤0)
finitePowerSeriesZeroAfter (suc N) coeff (suc n) sucN≤sucn =
  finitePowerSeriesZeroAfter
    N
    (λ i → coeff (Fin.suc i))
    n
    (NatOrder.pred-≤-pred sucN≤sucn)


finitePowerSeriesOnBallWith :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBallWith (finitePowerSeries N coeff) ρ (λ _ → N)
finitePowerSeriesOnBallWith N coeff =
  finiteSupportPowerSeriesOnBallWith
    N
    (finitePowerSeriesZeroAfter N coeff)


finitePowerSeriesOnBall :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall (finitePowerSeries N coeff) ρ
finitePowerSeriesOnBall N coeff =
  finiteSupportPowerSeriesOnBall
    N
    (finitePowerSeriesZeroAfter N coeff)


finitePowerSeriesSumOnBall-eval :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  {ρ : ℚ⁺} →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (finitePowerSeries N coeff)
    ρ
    (λ _ → N)
    (finitePowerSeriesOnBallWith N coeff)
    h
    h-bound
  ≡ finitePowerSeriesEval N coeff h
finitePowerSeriesSumOnBall-eval N coeff h h-bound =
  powerSeriesSumOnBall-constantModulusPartialSum
    N
    (finitePowerSeriesOnBallWith N coeff)
    h
    h-bound ∙
  finitePowerSeriesEval-partialSum N coeff h


centeredFinitePowerSeriesSumOnBall-eval :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  centeredPowerSeriesSumOnBall
    (finitePowerSeries N coeff)
    c
    ρ
    (λ _ → N)
    (finitePowerSeriesOnBallWith N coeff)
    x
    inBall
  ≡ finitePowerSeriesEval N coeff (centeredDisplacement c x)
centeredFinitePowerSeriesSumOnBall-eval N coeff c x inBall =
  centeredPowerSeriesSumOnBall-constantModulusPartialSum
    N
    (finitePowerSeriesOnBallWith N coeff)
    x
    inBall ∙
  finitePowerSeriesEval-partialSum
    N
    coeff
    (centeredDisplacement c x)


finitePowerSeriesEvalHasPowerSeriesAtWith :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesAtWith
    (λ x → finitePowerSeriesEval N coeff (centeredDisplacement c x))
    c
    (finitePowerSeries N coeff)
    ρ
    (λ _ → N)
finitePowerSeriesEvalHasPowerSeriesAtWith N coeff c =
  finitePowerSeriesOnBallWith N coeff ,
  λ x inBall →
    sym (centeredFinitePowerSeriesSumOnBall-eval N coeff c x inBall)


finitePowerSeriesEvalHasPowerSeriesAtOnBall :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  HasPowerSeriesAtOnBall
    (λ x → finitePowerSeriesEval N coeff (centeredDisplacement c x))
    c
    (finitePowerSeries N coeff)
    ρ
finitePowerSeriesEvalHasPowerSeriesAtOnBall N coeff c ρ =
  (λ _ → N) ,
  finitePowerSeriesEvalHasPowerSeriesAtWith N coeff c


finitePowerSeriesEvalHasPowerSeriesAt :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  HasPowerSeriesAt
    (λ x → finitePowerSeriesEval N coeff (centeredDisplacement c x))
    c
    (finitePowerSeries N coeff)
finitePowerSeriesEvalHasPowerSeriesAt N coeff c =
  1⁺ ,
  finitePowerSeriesEvalHasPowerSeriesAtOnBall N coeff c 1⁺


finitePowerSeriesEvalAnalyticAt :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  AnalyticAt
    (λ x → finitePowerSeriesEval N coeff (centeredDisplacement c x))
    c
finitePowerSeriesEvalAnalyticAt N coeff c =
  finitePowerSeries N coeff ,
  finitePowerSeriesEvalHasPowerSeriesAt N coeff c


finitePowerSeriesPolynomial :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  IsPolynomialPowerSeries (finitePowerSeries N coeff)
finitePowerSeriesPolynomial N coeff =
  N , finitePowerSeriesZeroAfter N coeff


finitePowerSeriesInfiniteRadius :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  HasInfinitePowerSeriesRadius (finitePowerSeries N coeff)
finitePowerSeriesInfiniteRadius N coeff =
  polynomialPowerSeriesInfiniteRadius (finitePowerSeriesPolynomial N coeff)


monomialPowerSeries :
  ℕ →
  ℝᶜ →
  PowerSeries
monomialPowerSeries zero c zero =
  c
monomialPowerSeries zero c (suc _) =
  0ᶜ
monomialPowerSeries (suc d) c zero =
  0ᶜ
monomialPowerSeries (suc d) c (suc n) =
  monomialPowerSeries d c n


monomialPowerSeriesZeroAfter :
  (d : ℕ) →
  (c : ℝᶜ) →
  PowerSeriesZeroAfter (monomialPowerSeries d c) (suc d)
monomialPowerSeriesZeroAfter zero c zero 1≤0 =
  Empty.rec (NatOrder.¬-<-zero 1≤0)
monomialPowerSeriesZeroAfter zero c (suc n) _ =
  refl
monomialPowerSeriesZeroAfter (suc d) c zero sucsd≤0 =
  Empty.rec (NatOrder.¬-<-zero sucsd≤0)
monomialPowerSeriesZeroAfter (suc d) c (suc n) sucsd≤sucn =
  monomialPowerSeriesZeroAfter
    d
    c
    n
    (NatOrder.pred-≤-pred sucsd≤sucn)


monomialPowerSeriesOnBallWith :
  (d : ℕ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBallWith (monomialPowerSeries d c) ρ (λ _ → suc d)
monomialPowerSeriesOnBallWith d c =
  finiteSupportPowerSeriesOnBallWith
    (suc d)
    (monomialPowerSeriesZeroAfter d c)


monomialPowerSeriesOnBall :
  (d : ℕ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall (monomialPowerSeries d c) ρ
monomialPowerSeriesOnBall d c =
  finiteSupportPowerSeriesOnBall
    (suc d)
    (monomialPowerSeriesZeroAfter d c)


monomialPowerSeriesPolynomial :
  (d : ℕ) →
  (c : ℝᶜ) →
  IsPolynomialPowerSeries (monomialPowerSeries d c)
monomialPowerSeriesPolynomial d c =
  suc d , monomialPowerSeriesZeroAfter d c


monomialPowerSeriesInfiniteRadius :
  (d : ℕ) →
  (c : ℝᶜ) →
  HasInfinitePowerSeriesRadius (monomialPowerSeries d c)
monomialPowerSeriesInfiniteRadius d c =
  polynomialPowerSeriesInfiniteRadius (monomialPowerSeriesPolynomial d c)
