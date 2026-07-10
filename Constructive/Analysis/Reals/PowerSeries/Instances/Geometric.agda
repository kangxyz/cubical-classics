{-

The geometric power series

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Geometric where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (_,_)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using
    ( positiveGeometricPowerModulus
    ; positiveGeometricPowerModulus-antitone
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using
    ( RealGeometricBound
    ; RealGeometricPowerBounds
    ; realGeometricPowerBoundsFromBound
    ; realGeometricPowerTailBoundFromPowerBounds
    ; realPower
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    alternating-geometric-step :
      (a h p : 𝓡 .fst) →
      (- a) · (h · p) ≡ (- h) · (a · p)
    alternating-geometric-step _ _ _ =
      solve! 𝓡


geometricPowerSeries :
  PowerSeries
geometricPowerSeries _ =
  1ᶜ


geometricPowerSeriesTerm :
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm geometricPowerSeries h n ≡ realPower h n
geometricPowerSeriesTerm h n =
  mulᶜ-one-left (realPower h n)


geometricPowerSeriesTermPath :
  (h : ℝᶜ) →
  powerSeriesTerm geometricPowerSeries h ≡ realPower h
geometricPowerSeriesTermPath h =
  funExt (geometricPowerSeriesTerm h)


alternatingGeometricPowerSeries :
  PowerSeries
alternatingGeometricPowerSeries zero =
  1ᶜ
alternatingGeometricPowerSeries (suc n) =
  -ᶜ alternatingGeometricPowerSeries n


alternatingGeometricPowerSeriesCoefficient-zero :
  alternatingGeometricPowerSeries zero ≡ 1ᶜ
alternatingGeometricPowerSeriesCoefficient-zero =
  refl


alternatingGeometricPowerSeriesCoefficient-suc :
  (n : ℕ) →
  alternatingGeometricPowerSeries (suc n) ≡
  -ᶜ alternatingGeometricPowerSeries n
alternatingGeometricPowerSeriesCoefficient-suc n =
  refl


alternatingGeometricPowerSeriesTerm :
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm alternatingGeometricPowerSeries h n ≡
  realPower (-ᶜ h) n
alternatingGeometricPowerSeriesTerm h zero =
  mulᶜ-one-left 1ᶜ
alternatingGeometricPowerSeriesTerm h (suc n) =
  SolverHelpers.alternating-geometric-step
    CauchyRealsCommRing
    (alternatingGeometricPowerSeries n)
    h
    (realPower h n) ∙
  cong
    ((-ᶜ h) ·ᶜ_)
    (alternatingGeometricPowerSeriesTerm h n)


alternatingGeometricPowerSeriesTermPath :
  (h : ℝᶜ) →
  powerSeriesTerm alternatingGeometricPowerSeries h ≡ realPower (-ᶜ h)
alternatingGeometricPowerSeriesTermPath h =
  funExt (alternatingGeometricPowerSeriesTerm h)


realGeometricBoundOnBall :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  RealGeometricBound h
realGeometricBoundOnBall ρ ρ<1 h h-bound =
  ρ , ρ<1 , h-bound


alternatingRealGeometricBoundOnBall :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  RealGeometricBound (-ᶜ h)
alternatingRealGeometricBoundOnBall ρ ρ<1 h h-bound =
  realGeometricBoundOnBall
    ρ
    ρ<1
    (-ᶜ h)
    (bounded-byᶜ-neg ρ h h-bound)


geometricPowerSeriesTailBoundFromPowerBounds :
  (h : ℝᶜ) →
  (bound : RealGeometricBound h) →
  RealGeometricPowerBounds h bound →
  PowerSeriesTailBound
    geometricPowerSeries
    h
    (positiveGeometricPowerModulus
      (RealGeometricBound.ratioBound bound)
      (RealGeometricBound.ratioBound<1 bound))
geometricPowerSeriesTailBoundFromPowerBounds h bound powerBounds =
  subst
    (λ u → TailBound u μ)
    (sym (geometricPowerSeriesTermPath h))
    (realGeometricPowerTailBoundFromPowerBounds h bound powerBounds)
  where
  μ : ℚ⁺ → ℕ
  μ =
    positiveGeometricPowerModulus
      (RealGeometricBound.ratioBound bound)
      (RealGeometricBound.ratioBound<1 bound)


alternatingGeometricPowerSeriesTailBoundFromPowerBounds :
  (h : ℝᶜ) →
  (bound : RealGeometricBound (-ᶜ h)) →
  RealGeometricPowerBounds (-ᶜ h) bound →
  PowerSeriesTailBound
    alternatingGeometricPowerSeries
    h
    (positiveGeometricPowerModulus
      (RealGeometricBound.ratioBound bound)
      (RealGeometricBound.ratioBound<1 bound))
alternatingGeometricPowerSeriesTailBoundFromPowerBounds h bound powerBounds =
  subst
    (λ u → TailBound u μ)
    (sym (alternatingGeometricPowerSeriesTermPath h))
    (realGeometricPowerTailBoundFromPowerBounds
      (-ᶜ h)
      bound
      powerBounds)
  where
  μ : ℚ⁺ → ℕ
  μ =
    positiveGeometricPowerModulus
      (RealGeometricBound.ratioBound bound)
      (RealGeometricBound.ratioBound<1 bound)


geometricPowerSeriesOnBallWithFromPowerBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  ((h : ℝᶜ) →
    (h-bound : BoundedByᶜ ρ h) →
    RealGeometricPowerBounds h
      (realGeometricBoundOnBall ρ ρ<1 h h-bound)) →
  HasPowerSeriesOnBallWith
    geometricPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
geometricPowerSeriesOnBallWithFromPowerBounds ρ ρ<1 powerBounds =
  hasPowerSeriesOnBallWith
    {a = geometricPowerSeries}
    {ρ = ρ}
    {μ = positiveGeometricPowerModulus ρ ρ<1}
    (positiveGeometricPowerModulus-antitone ρ ρ<1)
    (λ (h : ℝᶜ) (h-bound : BoundedByᶜ ρ h) →
      geometricPowerSeriesTailBoundFromPowerBounds
        h
        (realGeometricBoundOnBall ρ ρ<1 h h-bound)
        (powerBounds h h-bound))


alternatingGeometricPowerSeriesOnBallWithFromPowerBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  ((h : ℝᶜ) →
    (h-bound : BoundedByᶜ ρ h) →
    RealGeometricPowerBounds
      (-ᶜ h)
      (alternatingRealGeometricBoundOnBall ρ ρ<1 h h-bound)) →
  HasPowerSeriesOnBallWith
    alternatingGeometricPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
alternatingGeometricPowerSeriesOnBallWithFromPowerBounds ρ ρ<1 powerBounds =
  hasPowerSeriesOnBallWith
    {a = alternatingGeometricPowerSeries}
    {ρ = ρ}
    {μ = positiveGeometricPowerModulus ρ ρ<1}
    (positiveGeometricPowerModulus-antitone ρ ρ<1)
    (λ (h : ℝᶜ) (h-bound : BoundedByᶜ ρ h) →
      alternatingGeometricPowerSeriesTailBoundFromPowerBounds
        h
        (alternatingRealGeometricBoundOnBall ρ ρ<1 h h-bound)
        (powerBounds h h-bound))


geometricPowerSeriesOnBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBallWith
    geometricPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
geometricPowerSeriesOnBallWith ρ ρ<1 =
  geometricPowerSeriesOnBallWithFromPowerBounds
    ρ
    ρ<1
    λ h h-bound →
      realGeometricPowerBoundsFromBound
        h
        (realGeometricBoundOnBall ρ ρ<1 h h-bound)


alternatingGeometricPowerSeriesOnBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBallWith
    alternatingGeometricPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
alternatingGeometricPowerSeriesOnBallWith ρ ρ<1 =
  alternatingGeometricPowerSeriesOnBallWithFromPowerBounds
    ρ
    ρ<1
    λ h h-bound →
      realGeometricPowerBoundsFromBound
        (-ᶜ h)
        (alternatingRealGeometricBoundOnBall ρ ρ<1 h h-bound)


geometricPowerSeriesOnBallFromPowerBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  ((h : ℝᶜ) →
    (h-bound : BoundedByᶜ ρ h) →
    RealGeometricPowerBounds h
      (realGeometricBoundOnBall ρ ρ<1 h h-bound)) →
  HasPowerSeriesOnBall geometricPowerSeries ρ
geometricPowerSeriesOnBallFromPowerBounds ρ ρ<1 powerBounds =
  positiveGeometricPowerModulus ρ ρ<1 ,
  geometricPowerSeriesOnBallWithFromPowerBounds ρ ρ<1 powerBounds


alternatingGeometricPowerSeriesOnBallFromPowerBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  ((h : ℝᶜ) →
    (h-bound : BoundedByᶜ ρ h) →
    RealGeometricPowerBounds
      (-ᶜ h)
      (alternatingRealGeometricBoundOnBall ρ ρ<1 h h-bound)) →
  HasPowerSeriesOnBall alternatingGeometricPowerSeries ρ
alternatingGeometricPowerSeriesOnBallFromPowerBounds ρ ρ<1 powerBounds =
  positiveGeometricPowerModulus ρ ρ<1 ,
  alternatingGeometricPowerSeriesOnBallWithFromPowerBounds
    ρ
    ρ<1
    powerBounds


geometricPowerSeriesOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBall geometricPowerSeries ρ
geometricPowerSeriesOnBall ρ ρ<1 =
  positiveGeometricPowerModulus ρ ρ<1 ,
  geometricPowerSeriesOnBallWith ρ ρ<1


alternatingGeometricPowerSeriesOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBall alternatingGeometricPowerSeries ρ
alternatingGeometricPowerSeriesOnBall ρ ρ<1 =
  positiveGeometricPowerModulus ρ ρ<1 ,
  alternatingGeometricPowerSeriesOnBallWith ρ ρ<1


geometricPowerSeriesRadius :
  HasPowerSeriesRadius geometricPowerSeries 1⁺
geometricPowerSeriesRadius =
  hasPowerSeriesRadius
    {a = geometricPowerSeries}
    {R = 1⁺}
    (λ ρ ρ<1 →
      geometricPowerSeriesOnBall ρ ρ<1)


alternatingGeometricPowerSeriesRadius :
  HasPowerSeriesRadius alternatingGeometricPowerSeries 1⁺
alternatingGeometricPowerSeriesRadius =
  hasPowerSeriesRadius
    {a = alternatingGeometricPowerSeries}
    {R = 1⁺}
    (λ ρ ρ<1 →
      alternatingGeometricPowerSeriesOnBall ρ ρ<1)
