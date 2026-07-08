{-

Fixed positive-denominator scaling for global logarithm domains

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.DomainScaling where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.Nat using (zero ; suc)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using (HasPowerSeriesAtWith)
open import Constructive.Analysis.Reals.PowerSeries.Base
  using (PowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.FiniteSeries
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using
    ( InPowerSeriesBall
    ; centeredDisplacement
    ; centeredDisplacement-zero
    ; centeredPowerSeriesSumOnBall
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


divideByPositiveStrictSubunitRadius :
  ℚ⁺ →
  ℚ⁺ →
  ℚ⁺
divideByPositiveStrictSubunitRadius ρ cLower =
  ρ *⁺ posInv⁺ cLower


divideByPositiveStrictSubunitRadius<1 :
  (ρ cLower : ℚ⁺) →
  radius ρ ℚOrder.< radius cLower →
  radius (divideByPositiveStrictSubunitRadius ρ cLower)
    ℚOrder.< Rational.1ℚ
divideByPositiveStrictSubunitRadius<1 ρ cLower ρ<cLower =
  Rational.div-positive-denom-<1
    {q = radius ρ}
    {a = radius cLower}
    ρ<cLower
    (cLower .snd)


divideByPositiveᶜ-scaleBound :
  (ρ cLower : ℚ⁺) →
  (h c : ℝᶜ) →
  BoundedByᶜ ρ h →
  (c-bound : BoundedAwayPositiveᶜ cLower c) →
  BoundedByᶜ
    (divideByPositiveStrictSubunitRadius ρ cLower)
    (divideByPositiveᶜ h cLower c c-bound)
divideByPositiveᶜ-scaleBound ρ cLower h c h-bound c-bound =
  bounded-byᶜ-mul
    ρ
    (posInv⁺ cLower)
    h
    (reciprocalPositiveᶜ cLower c c-bound)
    h-bound
    (reciprocalPositiveᶜ-posInv-bound cLower c c-bound)


divideByPositiveᶜ-strictSubunitBound :
  (ρ cLower : ℚ⁺) →
  radius ρ ℚOrder.< radius cLower →
  (h c : ℝᶜ) →
  BoundedByᶜ ρ h →
  (c-bound : BoundedAwayPositiveᶜ cLower c) →
  BoundedByᶜ
    (divideByPositiveStrictSubunitRadius ρ cLower)
    (divideByPositiveᶜ h cLower c c-bound)
divideByPositiveᶜ-strictSubunitBound ρ cLower _ h c h-bound c-bound =
  divideByPositiveᶜ-scaleBound ρ cLower h c h-bound c-bound


divideByPositiveFixedCoefficient :
  ℝᶜ →
  Fin.Fin (suc (suc zero)) →
  ℝᶜ
divideByPositiveFixedCoefficient _ Fin.zero =
  0ᶜ
divideByPositiveFixedCoefficient r (Fin.suc Fin.zero) =
  r


divideByPositiveFixedPowerSeries :
  (cLower : ℚ⁺) →
  (c : ℝᶜ) →
  BoundedAwayPositiveᶜ cLower c →
  PowerSeries
divideByPositiveFixedPowerSeries cLower c c-bound =
  finitePowerSeries
    (suc (suc zero))
    (divideByPositiveFixedCoefficient
      (reciprocalPositiveᶜ cLower c c-bound))


divideByPositiveFixedEval :
  (r h : ℝᶜ) →
  finitePowerSeriesEval
    (suc (suc zero))
    (divideByPositiveFixedCoefficient r)
    h
  ≡ h ·ᶜ r
divideByPositiveFixedEval r h =
  add-zero-left (h ·ᶜ (r +ᶜ h ·ᶜ 0ᶜ)) ∙
  cong (h ·ᶜ_)
    (cong (r +ᶜ_) (mulᶜ-zero-right h) ∙
     add-zero-right r)


divideByPositiveFixedHasPowerSeriesAtWith :
  (cLower : ℚ⁺) →
  (c : ℝᶜ) →
  (c-bound : BoundedAwayPositiveᶜ cLower c) →
  (ρ : ℚ⁺) →
  HasPowerSeriesAtWith
    (λ h → divideByPositiveᶜ h cLower c c-bound)
    0ᶜ
    (divideByPositiveFixedPowerSeries cLower c c-bound)
    ρ
    (λ _ → suc (suc zero))
divideByPositiveFixedHasPowerSeriesAtWith cLower c c-bound ρ =
  finitePowerSeriesOnBallWith (suc (suc zero)) coeff ,
  expansion
  where
  r : ℝᶜ
  r =
    reciprocalPositiveᶜ cLower c c-bound

  coeff : Fin.Fin (suc (suc zero)) → ℝᶜ
  coeff =
    divideByPositiveFixedCoefficient r

  expansion :
    (x : ℝᶜ) →
    (inBall : InPowerSeriesBall 0ᶜ ρ x) →
    divideByPositiveᶜ x cLower c c-bound ≡
    centeredPowerSeriesSumOnBall
      (finitePowerSeries (suc (suc zero)) coeff)
      0ᶜ
      ρ
      (λ _ → suc (suc zero))
      (finitePowerSeriesOnBallWith (suc (suc zero)) coeff)
      x
      inBall
  expansion x inBall =
    cong (_·ᶜ r) (sym (centeredDisplacement-zero x)) ∙
    sym
      (divideByPositiveFixedEval r (centeredDisplacement 0ᶜ x)) ∙
    sym
      (centeredFinitePowerSeriesSumOnBall-eval
        (suc (suc zero))
        coeff
        0ᶜ
        x
        inBall)
