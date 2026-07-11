{-

The reciprocal represented by the formal derivative of atanh

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Derivative.Reciprocal where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision
  using
    ( BoundedAwayPositiveᶜ
    ; reciprocalPositiveᶜ
    ; reciprocalPositiveᶜ-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Structures
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Inverse
  using (right-inverse-uniqueᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Convergence
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.Series.Finite using (partialSum)
open import Constructive.Analysis.Reals.Series.Neumann
  using (seriesSumFromFiniteTailBound-neumannRightInverse)
open import Constructive.Analysis.Reals.Series.Tail
  using (TailBound ; partialSum-snoc)
open import Constructive.Analysis.GeometricDecay
  using
    ( positiveGeometricPowerModulus
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    finite-base :
      (z : 𝓡 .fst) →
      (1r + (- (z · z))) · 0r ≡ 1r + (- 1r)
    finite-base _ =
      solve! 𝓡

    finite-distribute :
      (factor E p : 𝓡 .fst) →
      factor · ((E + p) + 0r) ≡ (factor · E) + (factor · p)
    finite-distribute _ _ _ =
      solve! 𝓡

    finite-finish :
      (z p : 𝓡 .fst) →
      (1r + (- p)) + ((1r + (- (z · z))) · p) ≡
      1r + (- (z · (z · p)))
    finite-finish _ _ =
      solve! 𝓡


twice :
  ℕ →
  ℕ
twice zero =
  zero
twice (suc n) =
  suc (suc (twice n))


private
  index≤twice :
    (n : ℕ) →
    NatOrder._≤_ n (twice n)
  index≤twice zero =
    NatOrder.zero-≤
  index≤twice (suc n) =
    NatOrder.suc-≤-suc
      (NatOrder.≤-trans
        (index≤twice n)
        (NatOrder.≤-suc NatOrder.≤-refl))

  evenCoefficient-twice :
    (n : ℕ) →
    evenGeometricPowerSeries (twice n) ≡ 1ᶜ
  evenCoefficient-twice zero =
    refl
  evenCoefficient-twice (suc n) =
    evenCoefficient-twice n

  evenCoefficient-twice-suc :
    (n : ℕ) →
    evenGeometricPowerSeries (suc (twice n)) ≡ 0ᶜ
  evenCoefficient-twice-suc zero =
    refl
  evenCoefficient-twice-suc (suc n) =
    evenCoefficient-twice-suc n

  evenTerm-twice :
    (z : ℝᶜ) →
    (n : ℕ) →
    powerSeriesTerm evenGeometricPowerSeries z (twice n) ≡
    realPower z (twice n)
  evenTerm-twice z n =
    cong
      (_·ᶜ realPower z (twice n))
      (evenCoefficient-twice n) ∙
    mulᶜ-one-left (realPower z (twice n))

  evenTerm-twice-suc :
    (z : ℝᶜ) →
    (n : ℕ) →
    powerSeriesTerm evenGeometricPowerSeries z (suc (twice n)) ≡ 0ᶜ
  evenTerm-twice-suc z n =
    cong
      (_·ᶜ realPower z (suc (twice n)))
      (evenCoefficient-twice-suc n) ∙
    mulᶜ-zero-left (realPower z (suc (twice n)))


evenGeometricPowerSeriesPowerFiniteIdentity :
  (z : ℝᶜ) →
  (n : ℕ) →
  (1ᶜ +ᶜ (-ᶜ (z ·ᶜ z))) ·ᶜ
    partialSum (powerSeriesTerm evenGeometricPowerSeries z) (twice n)
  ≡
  1ᶜ +ᶜ (-ᶜ realPower z (twice n))
evenGeometricPowerSeriesPowerFiniteIdentity z zero =
  SolverHelpers.finite-base CauchyRealsCommRing z
evenGeometricPowerSeriesPowerFiniteIdentity z (suc n) =
  cong
    (factor ·ᶜ_)
    (partialSum-snoc terms (suc (twice n)) ∙
     cong
       (_+ᶜ terms (suc (twice n)))
       (partialSum-snoc terms (twice n)) ∙
     cong₂
       (λ even odd → (partialSum terms (twice n) +ᶜ even) +ᶜ odd)
       (evenTerm-twice z n)
       (evenTerm-twice-suc z n)) ∙
  SolverHelpers.finite-distribute
    CauchyRealsCommRing
    factor
    (partialSum terms (twice n))
    (realPower z (twice n)) ∙
  cong
    (_+ᶜ factor ·ᶜ realPower z (twice n))
    (evenGeometricPowerSeriesPowerFiniteIdentity z n) ∙
  SolverHelpers.finite-finish
    CauchyRealsCommRing
    z
    (realPower z (twice n))
  where
  factor : ℝᶜ
  factor =
    1ᶜ +ᶜ (-ᶜ (z ·ᶜ z))

  terms : ℕ → ℝᶜ
  terms =
    powerSeriesTerm evenGeometricPowerSeries z


evenGeometricPowerSeriesFiniteIdentity :
  (z : ℝᶜ) →
  (n : ℕ) →
  (1ᶜ +ᶜ (-ᶜ (z ·ᶜ z))) ·ᶜ
    partialSum (powerSeriesTerm evenGeometricPowerSeries z) (twice n)
  ≡
  1ᶜ +ᶜ
    (-ᶜ powerSeriesTerm evenGeometricPowerSeries z (twice n))
evenGeometricPowerSeriesFiniteIdentity z n =
  evenGeometricPowerSeriesPowerFiniteIdentity z n ∙
  cong
    (λ term → 1ᶜ +ᶜ (-ᶜ term))
    (sym (evenTerm-twice z n))


evenGeometricPowerSeriesNeumannRightInverseOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (z : ℝᶜ) →
  (z-bound : BoundedByᶜ ρ z) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (1ᶜ +ᶜ (-ᶜ (z ·ᶜ z))) →
  (1ᶜ +ᶜ (-ᶜ (z ·ᶜ z))) ·ᶜ
    powerSeriesSumOnBall
      evenGeometricPowerSeries
      ρ
      (positiveGeometricPowerModulus ρ ρ<1)
      (evenGeometricPowerSeriesOnSubunitBallWith ρ ρ<1)
      z
      z-bound
  ≡
  1ᶜ
evenGeometricPowerSeriesNeumannRightInverseOnBall
  ρ
  ρ<1
  z
  z-bound
  κ
  factorBound =
  seriesSumFromFiniteTailBound-neumannRightInverse
    factor
    κ
    factorBound
    (powerSeriesTerm evenGeometricPowerSeries z)
    μ
    tailBound
    μ-antitone
    twice
    index≤twice
    (evenGeometricPowerSeriesFiniteIdentity z)
  where
  μ : ℚ⁺ → ℕ
  μ =
    positiveGeometricPowerModulus ρ ρ<1

  convergence =
    evenGeometricPowerSeriesOnSubunitBallWith ρ ρ<1

  μ-antitone : AntitoneNatModulus μ
  μ-antitone =
    HasPowerSeriesOnBallWith.antitoneModulus convergence

  tailBound : TailBound (powerSeriesTerm evenGeometricPowerSeries z) μ
  tailBound =
    HasPowerSeriesOnBallWith.tailBound convergence z z-bound

  factor : ℝᶜ
  factor =
    1ᶜ +ᶜ (-ᶜ (z ·ᶜ z))


evenGeometricPowerSeriesReciprocalOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (z : ℝᶜ) →
  (z-bound : BoundedByᶜ ρ z) →
  (factorLower κ : ℚ⁺) →
  (factorAway :
    BoundedAwayPositiveᶜ factorLower (1ᶜ +ᶜ (-ᶜ (z ·ᶜ z)))) →
  BoundedByᶜ κ (1ᶜ +ᶜ (-ᶜ (z ·ᶜ z))) →
  powerSeriesSumOnBall
    evenGeometricPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (evenGeometricPowerSeriesOnSubunitBallWith ρ ρ<1)
    z
    z-bound
  ≡
  reciprocalPositiveᶜ
    factorLower
    (1ᶜ +ᶜ (-ᶜ (z ·ᶜ z)))
    factorAway
evenGeometricPowerSeriesReciprocalOnBall
  ρ ρ<1 z z-bound factorLower κ factorAway factorBound =
  sym
    (right-inverse-uniqueᶜ
      (reciprocalPositiveᶜ-right
        factorLower
        (1ᶜ +ᶜ (-ᶜ (z ·ᶜ z)))
        factorAway)
      (evenGeometricPowerSeriesNeumannRightInverseOnBall
        ρ ρ<1 z z-bound κ factorBound))


atanhDerivativePowerSeriesReciprocalOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (z : ℝᶜ) →
  (z-bound : BoundedByᶜ ρ z) →
  (factorLower κ : ℚ⁺) →
  (factorAway :
    BoundedAwayPositiveᶜ factorLower (1ᶜ +ᶜ (-ᶜ (z ·ᶜ z)))) →
  BoundedByᶜ κ (1ᶜ +ᶜ (-ᶜ (z ·ᶜ z))) →
  powerSeriesSumOnBall
    (derivativePowerSeries atanhPowerSeries)
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (atanhDerivativePowerSeriesOnSubunitBallWith ρ ρ<1)
    z
    z-bound
  ≡
  reciprocalPositiveᶜ
    factorLower
    (1ᶜ +ᶜ (-ᶜ (z ·ᶜ z)))
    factorAway
atanhDerivativePowerSeriesReciprocalOnBall
  ρ ρ<1 z z-bound factorLower κ factorAway factorBound =
  powerSeriesSumOnBall-coefficients-path
    (derivativePowerSeries-atanh)
    derivativeConvergence
    (evenGeometricPowerSeriesOnSubunitBallWith ρ ρ<1)
    z
    z-bound
    z-bound ∙
  evenGeometricPowerSeriesReciprocalOnBall
    ρ ρ<1 z z-bound factorLower κ factorAway factorBound
  where
  derivativeConvergence =
    atanhDerivativePowerSeriesOnSubunitBallWith ρ ρ<1
