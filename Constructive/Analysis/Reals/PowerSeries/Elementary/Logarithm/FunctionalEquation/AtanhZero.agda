{-

Zero normal form for the atanh logarithm transform

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation.AtanhZero where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using (powerSeriesSumOnBall-zero)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Coefficients
  using (atanhPowerSeriesCoefficient-zero)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Convergence
  using (atanhPowerSeriesOnSubunitBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Global
  using (atanhᶜFromSubunitBound)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


atanhᶜFromSubunitBound-zero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (zero-bound : BoundedByᶜ ρ 0ᶜ) →
  atanhᶜFromSubunitBound ρ ρ<1 0ᶜ zero-bound ≡ 0ᶜ
atanhᶜFromSubunitBound-zero ρ ρ<1 zero-bound =
  powerSeriesSumOnBall-zero
    (atanhPowerSeriesOnSubunitBallWith ρ ρ<1)
    zero-bound ∙
  atanhPowerSeriesCoefficient-zero
