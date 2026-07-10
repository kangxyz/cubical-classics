{-

Continuity criteria for power-series sums

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Continuity.PartialSums where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Sigma using (_,_)

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
  using (0ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using
    ( _·ᶜ_
    ; mulᶜ-close-left-with-bound
    ; mulᶜ-close-right-with-bound
    ; mulᶜ-rational-rational
    ; mulᶜ-rational-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.Series
  using (seriesSumFromFiniteTailBoundConvergesAt)
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using (bounded-byᶜ-zero ; shiftPowerSeries ; powerSeriesPartialSum-shift)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


module PartialSumProofs where
  scale-precision-cancel :
    (κ ε : ℚ⁺) →
    κ *⁺ (posInv⁺ κ *⁺ ε) ≡ ε
  scale-precision-cancel κ ε =
    sym (*⁺-assoc κ (posInv⁺ κ) ε) ∙
    cong (λ ρ → ρ *⁺ ε) (*⁺-posInv-right κ) ∙
    *⁺-identity-left ε

  scale-precision-mono :
    (κ ε δ : ℚ⁺) →
    ε <⁺ δ →
    κ *⁺ ε <⁺ κ *⁺ δ
  scale-precision-mono κ ε δ ε<δ =
    Rational.mul-left-positive-<
      {a = radius κ}
      {b = radius ε}
      {c = radius δ}
      (κ .snd)
      ε<δ

  scale-half-precision< :
    (κ ε : ℚ⁺) →
    κ *⁺ half⁺ (posInv⁺ κ *⁺ ε) <⁺ ε
  scale-half-precision< κ ε =
    subst
      (λ θ → κ *⁺ half⁺ (posInv⁺ κ *⁺ ε) <⁺ θ)
      (scale-precision-cancel κ ε)
      (scale-precision-mono
        κ
        (half⁺ (posInv⁺ κ *⁺ ε))
        (posInv⁺ κ *⁺ ε)
        (half< (posInv⁺ κ *⁺ ε)))


  powerSeriesPartialSumBoundPrecision :
    (ℕ → ℚ⁺) →
    ℚ⁺ →
    ℕ →
    ℚ⁺
  powerSeriesPartialSumBoundPrecision κ ρ zero =
    1⁺
  powerSeriesPartialSumBoundPrecision κ ρ (suc n) =
    κ zero +⁺
    (ρ *⁺ powerSeriesPartialSumBoundPrecision (λ k → κ (suc k)) ρ n)


  powerSeriesPartialSumModulusFromCoefficientBounds :
    (ℕ → ℚ⁺) →
    ℚ⁺ →
    ℕ →
    PrecisionModulus
  powerSeriesPartialSumModulusFromCoefficientBounds κ ρ zero ε =
    ε
  powerSeriesPartialSumModulusFromCoefficientBounds κ ρ (suc n) ε =
    half⁺
      (min⁺
        (powerSeriesPartialSumModulusFromCoefficientBounds
          (λ k → κ (suc k))
          ρ
          n
          (half⁺ (posInv⁺ ρ *⁺ quarter⁺ ε)))
        (half⁺
          (posInv⁺
            (powerSeriesPartialSumBoundPrecision (λ k → κ (suc k)) ρ n) *⁺
          quarter⁺ ε)))


  PowerSeriesPartialSumBoundedOnBallWith :
    (a : PowerSeries) →
    (ρ : ℚ⁺) →
    ℕ →
    ℚ⁺ →
    Type₀
  PowerSeriesPartialSumBoundedOnBallWith a ρ n κ =
    (h : ℝᶜ) →
    BoundedByᶜ ρ h →
    BoundedByᶜ κ (powerSeriesPartialSum a h n)


  powerSeriesPartialSumBoundedOnBallFromCoefficientBoundsWith :
    {a : PowerSeries} →
    {κ : ℕ → ℚ⁺} →
    {ρ : ℚ⁺} →
    PowerSeriesCoefficientBoundsWith a κ →
    (n : ℕ) →
    PowerSeriesPartialSumBoundedOnBallWith
      a
      ρ
      n
      (powerSeriesPartialSumBoundPrecision κ ρ n)
  powerSeriesPartialSumBoundedOnBallFromCoefficientBoundsWith coeffBounds zero h h-bound =
    bounded-byᶜ-zero 1⁺
  powerSeriesPartialSumBoundedOnBallFromCoefficientBoundsWith
    {a = a}
    {κ = κ}
    {ρ = ρ}
    coeffBounds
    (suc n)
    h
    h-bound =
    subst
      (BoundedByᶜ (powerSeriesPartialSumBoundPrecision κ ρ (suc n)))
      (sym (powerSeriesPartialSum-shift a h n))
      shiftedBound
    where
    shiftPrecision : ℚ⁺
    shiftPrecision =
      powerSeriesPartialSumBoundPrecision (λ k → κ (suc k)) ρ n

    shiftedPartialBound :
      BoundedByᶜ shiftPrecision (powerSeriesPartialSum (shiftPowerSeries a) h n)
    shiftedPartialBound =
      powerSeriesPartialSumBoundedOnBallFromCoefficientBoundsWith
        {a = shiftPowerSeries a}
        {κ = λ k → κ (suc k)}
        {ρ = ρ}
        (λ k → coeffBounds (suc k))
        n
        h
        h-bound

    productBound :
      BoundedByᶜ
        (ρ *⁺ shiftPrecision)
        (h ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) h n)
    productBound =
      bounded-byᶜ-mul
        ρ
        shiftPrecision
        h
        (powerSeriesPartialSum (shiftPowerSeries a) h n)
        h-bound
        shiftedPartialBound

    shiftedBound :
      BoundedByᶜ
        (κ zero +⁺ (ρ *⁺ shiftPrecision))
        (a zero +ᶜ h ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) h n)
    shiftedBound =
      bounded-byᶜ-add
        (κ zero)
        (ρ *⁺ shiftPrecision)
        (a zero)
        (h ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) h n)
        (coeffBounds zero)
        productBound


  PowerSeriesPartialSumUniformlyContinuousOnBallWith :
    (a : PowerSeries) →
    (ρ : ℚ⁺) →
    ℕ →
    PrecisionModulus →
    Type₀
  PowerSeriesPartialSumUniformlyContinuousOnBallWith a ρ n ν =
    (ε : ℚ⁺) →
    {h k : ℝᶜ} →
    (h-bound : BoundedByᶜ ρ h) →
    (k-bound : BoundedByᶜ ρ k) →
    MetricSpace.Close CauchyRealsMetricSpace h (ν ε) k →
    MetricSpace.Close CauchyRealsMetricSpace
      (powerSeriesPartialSum a h n)
      ε
      (powerSeriesPartialSum a k n)


  powerSeriesPartialSumLipschitzOnBallWith :
    {a : PowerSeries} →
    {κ : ℕ → ℚ⁺} →
    {ρ : ℚ⁺} →
    PowerSeriesCoefficientBoundsWith a κ →
    (n : ℕ) →
    PowerSeriesPartialSumUniformlyContinuousOnBallWith
      a
      ρ
      n
      (powerSeriesPartialSumModulusFromCoefficientBounds κ ρ n)
  powerSeriesPartialSumLipschitzOnBallWith
    coeffBounds
    zero
    ε
    h-bound
    k-bound
    h∼k =
    MetricSpace.close-refl CauchyRealsMetricSpace 0ᶜ ε
  powerSeriesPartialSumLipschitzOnBallWith
    {a = a}
    {κ = κ}
    {ρ = ρ}
    coeffBounds
    (suc n)
    ε
    {h = h}
    {k = k}
    h-bound
    k-bound
    h∼k =
    subst2
      (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
      (sym (powerSeriesPartialSum-shift a h n))
      (sym (powerSeriesPartialSum-shift a k n))
      shiftedClose
    where
    α : ℚ⁺
    α =
      quarter⁺ ε

    shiftPrecision : ℚ⁺
    shiftPrecision =
      powerSeriesPartialSumBoundPrecision (λ j → κ (suc j)) ρ n

    shiftedModulus : PrecisionModulus
    shiftedModulus =
      powerSeriesPartialSumModulusFromCoefficientBounds
        (λ j → κ (suc j))
        ρ
        n

    shiftedSourcePrecision : ℚ⁺
    shiftedSourcePrecision =
      shiftedModulus (half⁺ (posInv⁺ ρ *⁺ α))

    variableSourcePrecision : ℚ⁺
    variableSourcePrecision =
      half⁺ (posInv⁺ shiftPrecision *⁺ α)

    h∼k-shifted :
      MetricSpace.Close
        CauchyRealsMetricSpace
        h
        shiftedSourcePrecision
        k
    h∼k-shifted =
      MetricSpace.close-mono
        CauchyRealsMetricSpace
        (half-min⁺<left shiftedSourcePrecision variableSourcePrecision)
        h∼k

    h∼k-variable :
      MetricSpace.Close
        CauchyRealsMetricSpace
        h
        variableSourcePrecision
        k
    h∼k-variable =
      MetricSpace.close-mono
        CauchyRealsMetricSpace
        (half-min⁺<right shiftedSourcePrecision variableSourcePrecision)
        h∼k

    shiftedPartialClose :
      MetricSpace.Close
        CauchyRealsMetricSpace
        (powerSeriesPartialSum (shiftPowerSeries a) h n)
        (half⁺ (posInv⁺ ρ *⁺ α))
        (powerSeriesPartialSum (shiftPowerSeries a) k n)
    shiftedPartialClose =
      powerSeriesPartialSumLipschitzOnBallWith
        {a = shiftPowerSeries a}
        {κ = λ j → κ (suc j)}
        {ρ = ρ}
        (λ j → coeffBounds (suc j))
        n
        (half⁺ (posInv⁺ ρ *⁺ α))
        h-bound
        k-bound
        h∼k-shifted

    productCloseSameLeftRaw :
      MetricSpace.Close
        CauchyRealsMetricSpace
        (h ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) h n)
        (ρ *⁺ half⁺ (posInv⁺ ρ *⁺ α))
        (h ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) k n)
    productCloseSameLeftRaw =
      mulᶜ-close-right-with-bound
        ρ
        h
        h-bound
        shiftedPartialClose

    productCloseSameLeft :
      MetricSpace.Close
        CauchyRealsMetricSpace
        (h ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) h n)
        α
        (h ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) k n)
    productCloseSameLeft =
      MetricSpace.close-mono
        CauchyRealsMetricSpace
        (scale-half-precision< ρ α)
        productCloseSameLeftRaw

    shiftedPartialKBound :
      BoundedByᶜ shiftPrecision (powerSeriesPartialSum (shiftPowerSeries a) k n)
    shiftedPartialKBound =
      powerSeriesPartialSumBoundedOnBallFromCoefficientBoundsWith
        {a = shiftPowerSeries a}
        {κ = λ j → κ (suc j)}
        {ρ = ρ}
        (λ j → coeffBounds (suc j))
        n
        k
        k-bound

    productCloseSameRightRaw :
      MetricSpace.Close
        CauchyRealsMetricSpace
        (h ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) k n)
        (shiftPrecision *⁺ half⁺ (posInv⁺ shiftPrecision *⁺ α))
        (k ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) k n)
    productCloseSameRightRaw =
      mulᶜ-close-left-with-bound
        shiftPrecision
        (powerSeriesPartialSum (shiftPowerSeries a) k n)
        shiftedPartialKBound
        h∼k-variable

    productCloseSameRight :
      MetricSpace.Close
        CauchyRealsMetricSpace
        (h ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) k n)
        α
        (k ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) k n)
    productCloseSameRight =
      MetricSpace.close-mono
        CauchyRealsMetricSpace
        (scale-half-precision< shiftPrecision α)
        productCloseSameRightRaw

    productClose :
      MetricSpace.Close
        CauchyRealsMetricSpace
        (h ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) h n)
        (α +⁺ α)
        (k ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) k n)
    productClose =
      MetricSpace.close-triangle
        CauchyRealsMetricSpace
        productCloseSameLeft
        productCloseSameRight

    shiftedClose :
      MetricSpace.Close
        CauchyRealsMetricSpace
        (a zero +ᶜ h ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) h n)
        ε
        (a zero +ᶜ k ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) k n)
    shiftedClose =
      MetricSpace.close-mono
        CauchyRealsMetricSpace
        (quarter-sum< ε)
        (add-close-right (a zero) productClose)


  PowerSeriesPartialSumsUniformlyContinuousOnBallWith :
    (a : PowerSeries) →
    (ρ : ℚ⁺) →
    (χ : ℚ⁺ → ℕ) →
    PrecisionModulus →
    Type₀
  PowerSeriesPartialSumsUniformlyContinuousOnBallWith a ρ χ ν =
    (ε : ℚ⁺) →
    {h k : ℝᶜ} →
    (h-bound : BoundedByᶜ ρ h) →
    (k-bound : BoundedByᶜ ρ k) →
    MetricSpace.Close CauchyRealsMetricSpace h (ν ε) k →
    MetricSpace.Close CauchyRealsMetricSpace
      (powerSeriesPartialSum a h (χ ε))
      (quarter⁺ ε)
      (powerSeriesPartialSum a k (χ ε))


  powerSeriesPartialSumsModulusFromCoefficientBounds :
    (ℕ → ℚ⁺) →
    ℚ⁺ →
    (ℚ⁺ → ℕ) →
    PrecisionModulus
  powerSeriesPartialSumsModulusFromCoefficientBounds κ ρ χ ε =
    powerSeriesPartialSumModulusFromCoefficientBounds κ ρ (χ ε) (quarter⁺ ε)


  powerSeriesPartialSumsUniformlyContinuousOnBallFromCoefficientBoundsWith :
    {a : PowerSeries} →
    {κ : ℕ → ℚ⁺} →
    {ρ : ℚ⁺} →
    {χ : ℚ⁺ → ℕ} →
    PowerSeriesCoefficientBoundsWith a κ →
    PowerSeriesPartialSumsUniformlyContinuousOnBallWith
      a
      ρ
      χ
      (powerSeriesPartialSumsModulusFromCoefficientBounds κ ρ χ)
  powerSeriesPartialSumsUniformlyContinuousOnBallFromCoefficientBoundsWith
    {χ = χ}
    coeffBounds
    ε =
    powerSeriesPartialSumLipschitzOnBallWith
      coeffBounds
      (χ ε)
      (quarter⁺ ε)



open PartialSumProofs public
  using
    ( PowerSeriesPartialSumsUniformlyContinuousOnBallWith
    ; powerSeriesPartialSumsModulusFromCoefficientBounds
    ; powerSeriesPartialSumsUniformlyContinuousOnBallFromCoefficientBoundsWith
    )
