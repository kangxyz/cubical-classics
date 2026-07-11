{-

Fixed positive-denominator scaling for global logarithm domains

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.DomainScaling where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.Nat using (zero ; suc)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using (HasPowerSeriesAtWith)
open import Constructive.Analysis.Reals.PowerSeries.Base
  using (PowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.FiniteSeries
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
