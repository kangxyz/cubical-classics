{-

The reciprocal represented by the formal derivative of atanh

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Derivative where

open import Cubical.Foundations.Prelude

open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Derivative.Bounds public
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Derivative.Within public

open import Cubical.Algebra.CommRing
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision
  using
    ( BoundedAwayPositiveᶜ
    ; reciprocalPositiveᶜ
    ; reciprocalPositiveᶜ-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Inverse
  using (right-inverse-uniqueᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (neg-zeroᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Convergence
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.Series
  using
    ( AntitoneTailModulus
    ; TailBound
    ; partialSum
    ; partialSum-snoc
    ; seriesSumFromFiniteTailBound-mul-left-convergesAt
    ; tailSum
    ; tailSum-one
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using
    ( positiveGeometricPowerModulus
    ; positiveGeometricPowerModulus-antitone
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
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
  index≤twiceSuc :
    (n : ℕ) →
    NatOrder._≤_ n (twice (suc n))
  index≤twiceSuc zero =
    NatOrder.zero-≤
  index≤twiceSuc (suc n) =
    NatOrder.suc-≤-suc
      (NatOrder.≤-trans
        (index≤twiceSuc n)
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


evenGeometricPowerSeriesFiniteIdentity :
  (z : ℝᶜ) →
  (n : ℕ) →
  (1ᶜ +ᶜ (-ᶜ (z ·ᶜ z))) ·ᶜ
    partialSum (powerSeriesTerm evenGeometricPowerSeries z) (twice n)
  ≡
  1ᶜ +ᶜ (-ᶜ realPower z (twice n))
evenGeometricPowerSeriesFiniteIdentity z zero =
  SolverHelpers.finite-base CauchyRealsCommRing z
evenGeometricPowerSeriesFiniteIdentity z (suc n) =
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
    (evenGeometricPowerSeriesFiniteIdentity z n) ∙
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
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    product
    1ᶜ
    closeAt
  where
  μ : ℚ⁺ → ℕ
  μ =
    positiveGeometricPowerModulus ρ ρ<1

  μ-antitone : AntitoneTailModulus μ
  μ-antitone =
    positiveGeometricPowerModulus-antitone ρ ρ<1

  convergence =
    evenGeometricPowerSeriesOnSubunitBallWith ρ ρ<1

  tailBound : TailBound (powerSeriesTerm evenGeometricPowerSeries z) μ
  tailBound =
    HasPowerSeriesOnBallWith.tailBound convergence z z-bound

  factor : ℝᶜ
  factor =
    1ᶜ +ᶜ (-ᶜ (z ·ᶜ z))

  sum : ℝᶜ
  sum =
    powerSeriesSumOnBall evenGeometricPowerSeries ρ μ convergence z z-bound

  product : ℝᶜ
  product =
    factor ·ᶜ sum

  closeAt :
    (ε : ℚ⁺) →
    product ∼[ ε ] 1ᶜ
  closeAt ε =
    subst
      (λ precision → product ∼[ precision ] 1ᶜ)
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        product∼partial
        partial∼one)
    where
    η : ℚ⁺
    η =
      half⁺ ε

    productPrecision : ℚ⁺
    productPrecision =
      quarter⁺
        (half⁺
          (fst (mulᶜ-continuous-right-with-bound κ factor factorBound) η))

    tailPrecision : ℚ⁺
    tailPrecision =
      half⁺ η

    productIndex tailIndex baseIndex : ℕ
    productIndex =
      μ productPrecision
    tailIndex =
      μ tailPrecision
    baseIndex =
      productIndex Nat.+ tailIndex

    n : ℕ
    n =
      twice (suc baseIndex)

    baseIndex≤n : NatOrder._≤_ baseIndex n
    baseIndex≤n =
      index≤twiceSuc baseIndex

    productIndex≤n : NatOrder._≤_ productIndex n
    productIndex≤n =
      NatOrder.≤-trans
        (tailIndex , Nat.+-comm tailIndex productIndex)
        baseIndex≤n

    tailIndex≤n : NatOrder._≤_ tailIndex n
    tailIndex≤n =
      NatOrder.≤-trans
        (productIndex , refl)
        baseIndex≤n

    product∼partial :
      product ∼[ η ] factor ·ᶜ partialSum
        (powerSeriesTerm evenGeometricPowerSeries z)
        n
    product∼partial =
      seriesSumFromFiniteTailBound-mul-left-convergesAt
        factor
        κ
        factorBound
        (powerSeriesTerm evenGeometricPowerSeries z)
        μ
        tailBound
        μ-antitone
        η
        n
        productIndex≤n

    termTailBound :
      BoundedByᶜ
        tailPrecision
        (tailSum (powerSeriesTerm evenGeometricPowerSeries z) n (suc zero))
    termTailBound =
      tailBound tailPrecision n (suc zero) tailIndex≤n

    termBound :
      BoundedByᶜ
        tailPrecision
        (powerSeriesTerm evenGeometricPowerSeries z n)
    termBound =
      subst
        (BoundedByᶜ tailPrecision)
        (tailSum-one (powerSeriesTerm evenGeometricPowerSeries z) n)
        termTailBound

    powerBound : BoundedByᶜ tailPrecision (realPower z n)
    powerBound =
      subst
        (BoundedByᶜ tailPrecision)
        (evenTerm-twice z (suc baseIndex))
        termBound

    power∼zero : realPower z n ∼[ η ] 0ᶜ
    power∼zero =
      bounded-byᶜ-close-zero
        tailPrecision
        η
        (realPower z n)
        powerBound
        (half< η)

    oneMinusPower∼one :
      (1ᶜ +ᶜ (-ᶜ realPower z n)) ∼[ η ] 1ᶜ
    oneMinusPower∼one =
      subst
        (λ w → (1ᶜ +ᶜ (-ᶜ realPower z n)) ∼[ η ] w)
        (add-zero-right 1ᶜ)
        (add-close-right
          1ᶜ
          (subst
            (λ w → (-ᶜ realPower z n) ∼[ η ] w)
            neg-zeroᶜ
            (neg-close power∼zero)))

    partial∼one :
      factor ·ᶜ partialSum (powerSeriesTerm evenGeometricPowerSeries z) n
      ∼[ η ] 1ᶜ
    partial∼one =
      subst
        (λ w → w ∼[ η ] 1ᶜ)
        (sym (evenGeometricPowerSeriesFiniteIdentity z (suc baseIndex)))
        oneMinusPower∼one


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
