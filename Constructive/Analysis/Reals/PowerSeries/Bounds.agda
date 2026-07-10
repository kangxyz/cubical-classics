{-

Coefficient bounds for power series

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Bounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using
    ( _·ᶜ_
    ; mulᶜ-rational-rational
    ; mulᶜ-rational-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
  using (scalarMulᶜ ; scalarMulᶜ-assoc ; scalarMulᶜ-one)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.GeometricDecay
  using (positivePower)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


PowerSeriesCoefficientBoundsWith :
  (a : PowerSeries) →
  (ℕ → ℚ⁺) →
  Type₀
PowerSeriesCoefficientBoundsWith a κ =
  (n : ℕ) → BoundedByᶜ (κ n) (a n)


PowerSeriesCoefficientBounds :
  PowerSeries →
  Type₀
PowerSeriesCoefficientBounds a =
  Σ[ κ ∈ (ℕ → ℚ⁺) ] PowerSeriesCoefficientBoundsWith a κ


powerSeriesCoefficientBoundPrecisionFromBallTermBounds :
  ℚ⁺ →
  (ℕ → ℚ⁺) →
  ℕ →
  ℚ⁺
powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ n =
  posInv⁺ (positivePower ρ n) *⁺ κ n


realPower-rational-positive :
  (ρ : ℚ⁺) →
  (n : ℕ) →
  realPower (rational (radius ρ)) n ≡
  rational (radius (positivePower ρ n))
realPower-rational-positive ρ zero =
  refl
realPower-rational-positive ρ (suc n) =
  cong
    (λ p → rational (radius ρ) ·ᶜ p)
    (realPower-rational-positive ρ n) ∙
  mulᶜ-rational-rational (radius ρ) (radius (positivePower ρ n))


powerSeriesCoefficientFromRationalProbe :
  (ρ : ℚ⁺) →
  (a : PowerSeries) →
  (n : ℕ) →
  scalarMulᶜ
    (radius (posInv⁺ (positivePower ρ n)))
    (powerSeriesTerm a (rational (radius ρ)) n)
  ≡ a n
powerSeriesCoefficientFromRationalProbe ρ a n =
  cong
    (scalarMulᶜ invρⁿ)
    (cong (a n ·ᶜ_) (realPower-rational-positive ρ n) ∙
      mulᶜ-rational-right (a n) ρⁿ) ∙
  scalarMulᶜ-assoc invρⁿ ρⁿ (a n) ∙
  cong (λ q → scalarMulᶜ q (a n)) invρⁿ*ρⁿ≡1 ∙
  scalarMulᶜ-one (a n)
  where
  ρⁿ : ℚ
  ρⁿ =
    radius (positivePower ρ n)

  invρⁿ : ℚ
  invρⁿ =
    radius (posInv⁺ (positivePower ρ n))

  invρⁿ*ρⁿ≡1 : invρⁿ ℚ.· ρⁿ ≡ Rational.1ℚ
  invρⁿ*ρⁿ≡1 =
    cong radius (*⁺-posInv-left (positivePower ρ n))


powerSeriesCoefficientBoundsFromRationalProbeTermBoundsWith :
  {a : PowerSeries} →
  {κ : ℕ → ℚ⁺} →
  (ρ : ℚ⁺) →
  ((n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a (rational (radius ρ)) n)) →
  PowerSeriesCoefficientBoundsWith
    a
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
powerSeriesCoefficientBoundsFromRationalProbeTermBoundsWith
  {a = a}
  {κ = κ}
  ρ
  termBounds
  n =
  subst
    (BoundedByᶜ (posInv⁺ ρⁿ⁺ *⁺ κ n))
    (powerSeriesCoefficientFromRationalProbe ρ a n)
    scaledTermBound
  where
  ρⁿ⁺ : ℚ⁺
  ρⁿ⁺ =
    positivePower ρ n

  invρⁿ : ℚ
  invρⁿ =
    radius (posInv⁺ ρⁿ⁺)

  invρⁿ-nonnegative :
    Rational.0ℚ ℚOrder.≤ invρⁿ
  invρⁿ-nonnegative =
    Rational.<→≤
      {p = Rational.0ℚ}
      {q = invρⁿ}
      (posInv⁺ ρⁿ⁺ .snd)

  scaledTermBound :
    BoundedByᶜ
      (posInv⁺ ρⁿ⁺ *⁺ κ n)
      (scalarMulᶜ
        invρⁿ
        (powerSeriesTerm a (rational (radius ρ)) n))
  scaledTermBound =
    bounded-byᶜ-scale-nonnegative
      invρⁿ
      (κ n)
      (posInv⁺ ρⁿ⁺)
      (powerSeriesTerm a (rational (radius ρ)) n)
      invρⁿ-nonnegative
      (Rational.≤-refl invρⁿ)
      (termBounds n)


positiveRationalSelfBounded :
  (ρ : ℚ⁺) →
  BoundedByᶜ ρ (rational (radius ρ))
positiveRationalSelfBounded ρ =
  rational-closed-bound→boundedᶜ
    ρ
    (radius ρ)
    (rational-closed-boundᶜ
      (Rational.≤-refl (radius ρ))
      negρ≤ρ)
  where
  0≤ρ : Rational.0ℚ ℚOrder.≤ radius ρ
  0≤ρ =
    Rational.<→≤
      {p = Rational.0ℚ}
      {q = radius ρ}
      (ρ .snd)

  negρ≤0 : ℚ.- radius ρ ℚOrder.≤ Rational.0ℚ
  negρ≤0 =
    Rational.neg-nonpositive 0≤ρ

  negρ≤ρ : ℚ.- radius ρ ℚOrder.≤ radius ρ
  negρ≤ρ =
    Rational.≤-trans
      {p = ℚ.- radius ρ}
      {q = Rational.0ℚ}
      {r = radius ρ}
      negρ≤0
      0≤ρ


powerSeriesCoefficientBoundsFromBallTermBoundsWith :
  {a : PowerSeries} →
  {κ : ℕ → ℚ⁺} →
  (ρ : ℚ⁺) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  PowerSeriesCoefficientBoundsWith
    a
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
powerSeriesCoefficientBoundsFromBallTermBoundsWith ρ termBounds =
  powerSeriesCoefficientBoundsFromRationalProbeTermBoundsWith
    ρ
    (termBounds
      (rational (radius ρ))
      (positiveRationalSelfBounded ρ))


powerSeriesCoefficientBoundsFromBallTermBounds :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  PowerSeriesCoefficientBounds a
powerSeriesCoefficientBoundsFromBallTermBounds
  {ρ = ρ}
  (κ , termBounds) =
  powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ ,
  powerSeriesCoefficientBoundsFromBallTermBoundsWith ρ termBounds
