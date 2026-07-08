{-

Argument transport for atanh logarithm transforms

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.AtanhTransport where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Convergence
  using (atanhPowerSeriesOnSubunitBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.Global
  using (atanhᶜFromSubunitBound)
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using (powerSeriesSumOnBall-center-path)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


atanhᶜFromSubunitBound-argument-path :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  {z w : ℝᶜ} →
  (p : z ≡ w) →
  (z-bound : BoundedByᶜ ρ z) →
  atanhᶜFromSubunitBound ρ ρ<1 z z-bound ≡
  atanhᶜFromSubunitBound ρ ρ<1 w (subst (BoundedByᶜ ρ) p z-bound)
atanhᶜFromSubunitBound-argument-path ρ ρ<1 p z-bound =
  powerSeriesSumOnBall-center-path
    (atanhPowerSeriesOnSubunitBallWith ρ ρ<1)
    p
    z-bound
    (subst (BoundedByᶜ ρ) p z-bound)
