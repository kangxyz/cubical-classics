{-

Continuity criteria for power-series sums

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Continuity where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Metric.Instances.CauchyReals
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
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
  using (scalarMulᶜ ; scalarMulᶜ-assoc ; scalarMulᶜ-one)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using (positivePower)
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using (bounded-byᶜ-zero ; shiftPowerSeries ; powerSeriesPartialSum-shift)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


powerSeriesLimitApproximationIndex :
  (ℚ⁺ → ℕ) →
  ℚ⁺ →
  ℕ
powerSeriesLimitApproximationIndex μ ε =
  μ (quarter⁺ (half⁺ (quarter⁺ ε)))


private
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


PowerSeriesPartialSumBoundedOnBall :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  ℕ →
  Type₀
PowerSeriesPartialSumBoundedOnBall a ρ n =
  Σ[ κ ∈ ℚ⁺ ] PowerSeriesPartialSumBoundedOnBallWith a ρ n κ


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


powerSeriesPartialSumBoundedOnBallFromCoefficientBounds :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  PowerSeriesCoefficientBounds a →
  (n : ℕ) →
  PowerSeriesPartialSumBoundedOnBall a ρ n
powerSeriesPartialSumBoundedOnBallFromCoefficientBounds
  {ρ = ρ}
  (κ , coeffBounds)
  n =
  powerSeriesPartialSumBoundPrecision κ ρ n ,
  powerSeriesPartialSumBoundedOnBallFromCoefficientBoundsWith coeffBounds n


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


PowerSeriesPartialSumUniformlyContinuousOnBall :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  ℕ →
  Type₀
PowerSeriesPartialSumUniformlyContinuousOnBall a ρ n =
  Σ[ ν ∈ PrecisionModulus ]
    PowerSeriesPartialSumUniformlyContinuousOnBallWith a ρ n ν


powerSeriesPartialSumUniformlyContinuousOnBallFromCoefficientBoundsWith :
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
powerSeriesPartialSumUniformlyContinuousOnBallFromCoefficientBoundsWith
  coeffBounds
  zero
  ε
  h-bound
  k-bound
  h∼k =
  MetricSpace.close-refl CauchyRealsMetricSpace 0ᶜ ε
powerSeriesPartialSumUniformlyContinuousOnBallFromCoefficientBoundsWith
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
    powerSeriesPartialSumUniformlyContinuousOnBallFromCoefficientBoundsWith
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


powerSeriesPartialSumUniformlyContinuousOnBallFromCoefficientBounds :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  PowerSeriesCoefficientBounds a →
  (n : ℕ) →
  PowerSeriesPartialSumUniformlyContinuousOnBall a ρ n
powerSeriesPartialSumUniformlyContinuousOnBallFromCoefficientBounds
  {ρ = ρ}
  (κ , coeffBounds)
  n =
  powerSeriesPartialSumModulusFromCoefficientBounds κ ρ n ,
  powerSeriesPartialSumUniformlyContinuousOnBallFromCoefficientBoundsWith
    coeffBounds
    n


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


PowerSeriesPartialSumsUniformlyContinuousOnBall :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (χ : ℚ⁺ → ℕ) →
  Type₀
PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ =
  Σ[ ν ∈ PrecisionModulus ]
    PowerSeriesPartialSumsUniformlyContinuousOnBallWith a ρ χ ν


powerSeriesPartialSumsModulusFromCoefficientBounds :
  (ℕ → ℚ⁺) →
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  PrecisionModulus
powerSeriesPartialSumsModulusFromCoefficientBounds κ ρ χ ε =
  powerSeriesPartialSumModulusFromCoefficientBounds κ ρ (χ ε) (quarter⁺ ε)


powerSeriesPartialSumsUniformlyContinuousOnBallFromPartialSumModuliWith :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {χ : ℚ⁺ → ℕ} →
  (ω : ℕ → PrecisionModulus) →
  ((n : ℕ) →
    PowerSeriesPartialSumUniformlyContinuousOnBallWith a ρ n (ω n)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBallWith
    a
    ρ
    χ
    (λ ε → ω (χ ε) (quarter⁺ ε))
powerSeriesPartialSumsUniformlyContinuousOnBallFromPartialSumModuliWith
  {χ = χ}
  ω
  partial-cont
  ε =
  partial-cont (χ ε) (quarter⁺ ε)


powerSeriesPartialSumsUniformlyContinuousOnBallFromPartialSumModuli :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {χ : ℚ⁺ → ℕ} →
  ((n : ℕ) → PowerSeriesPartialSumUniformlyContinuousOnBall a ρ n) →
  PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ
powerSeriesPartialSumsUniformlyContinuousOnBallFromPartialSumModuli
  {χ = χ}
  partial-cont =
  (λ ε → partial-cont (χ ε) .fst (quarter⁺ ε)) ,
  powerSeriesPartialSumsUniformlyContinuousOnBallFromPartialSumModuliWith
    (λ n → partial-cont n .fst)
    (λ n → partial-cont n .snd)


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
  coeffBounds =
  powerSeriesPartialSumsUniformlyContinuousOnBallFromPartialSumModuliWith
    _
    (powerSeriesPartialSumUniformlyContinuousOnBallFromCoefficientBoundsWith
      coeffBounds)


powerSeriesPartialSumsUniformlyContinuousOnBallFromCoefficientBounds :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {χ : ℚ⁺ → ℕ} →
  PowerSeriesCoefficientBounds a →
  PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ
powerSeriesPartialSumsUniformlyContinuousOnBallFromCoefficientBounds
  {ρ = ρ}
  {χ = χ}
  (κ , coeffBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds κ ρ χ ,
  powerSeriesPartialSumsUniformlyContinuousOnBallFromCoefficientBoundsWith
    coeffBounds


powerSeriesPartialSumsUniformlyContinuousOnBallFromBallTermBoundsWith :
  {a : PowerSeries} →
  {κ : ℕ → ℚ⁺} →
  {ρ : ℚ⁺} →
  {χ : ℚ⁺ → ℕ} →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBallWith
    a
    ρ
    χ
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      χ)
powerSeriesPartialSumsUniformlyContinuousOnBallFromBallTermBoundsWith
  {ρ = ρ}
  termBounds =
  powerSeriesPartialSumsUniformlyContinuousOnBallFromCoefficientBoundsWith
    (powerSeriesCoefficientBoundsFromBallTermBoundsWith ρ termBounds)


powerSeriesPartialSumsUniformlyContinuousOnBallFromBallTermBounds :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {χ : ℚ⁺ → ℕ} →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ
powerSeriesPartialSumsUniformlyContinuousOnBallFromBallTermBounds
  {ρ = ρ}
  {χ = χ}
  (κ , termBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    χ ,
  powerSeriesPartialSumsUniformlyContinuousOnBallFromBallTermBoundsWith
    termBounds


powerSeriesSumUniformlyContinuousFromPartialSums :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {ν : PrecisionModulus} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBallWith a ρ χ ν →
  PowerSeriesSumUniformlyContinuousOnBallWith a ρ μ convergence ν
powerSeriesSumUniformlyContinuousFromPartialSums
  {a = a}
  {ρ = ρ}
  {μ = μ}
  {χ = χ}
  {convergence = convergence}
  index-large
  partial-cont
  ε
  {h = h}
  {k = k}
  h-bound
  k-bound
  h∼k =
  MetricSpace.close-mono
    CauchyRealsMetricSpace
    (three-quarter< ε)
    sum∼sum
  where
  τ : ℚ⁺
  τ =
    quarter⁺ ε

  n : ℕ
  n =
    χ ε

  tail-h :
    MetricSpace.Close CauchyRealsMetricSpace
      (powerSeriesSumOnBall a ρ μ convergence h h-bound)
      τ
      (powerSeriesPartialSum a h n)
  tail-h =
    seriesSumFromFiniteTailBoundConvergesAt
      (powerSeriesTerm a h)
      μ
      (HasPowerSeriesOnBallWith.tailBound convergence h h-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus convergence)
      τ
      n
      (index-large ε)

  partial-h∼k :
    MetricSpace.Close CauchyRealsMetricSpace
      (powerSeriesPartialSum a h n)
      τ
      (powerSeriesPartialSum a k n)
  partial-h∼k =
    partial-cont ε h-bound k-bound h∼k

  tail-k :
    MetricSpace.Close CauchyRealsMetricSpace
      (powerSeriesSumOnBall a ρ μ convergence k k-bound)
      τ
      (powerSeriesPartialSum a k n)
  tail-k =
    seriesSumFromFiniteTailBoundConvergesAt
      (powerSeriesTerm a k)
      μ
      (HasPowerSeriesOnBallWith.tailBound convergence k k-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus convergence)
      τ
      n
      (index-large ε)

  sum∼partial-k :
    MetricSpace.Close CauchyRealsMetricSpace
      (powerSeriesSumOnBall a ρ μ convergence h h-bound)
      (τ +⁺ τ)
      (powerSeriesPartialSum a k n)
  sum∼partial-k =
    MetricSpace.close-triangle
      CauchyRealsMetricSpace
      tail-h
      partial-h∼k

  sum∼sum :
    MetricSpace.Close CauchyRealsMetricSpace
      (powerSeriesSumOnBall a ρ μ convergence h h-bound)
      ((τ +⁺ τ) +⁺ τ)
      (powerSeriesSumOnBall a ρ μ convergence k k-bound)
  sum∼sum =
    MetricSpace.close-triangle
      CauchyRealsMetricSpace
      sum∼partial-k
      (MetricSpace.close-sym CauchyRealsMetricSpace tail-k)


powerSeriesSumUniformlyContinuousFromPartialSumsΣ :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ →
  PowerSeriesSumUniformlyContinuousOnBall a ρ μ convergence
powerSeriesSumUniformlyContinuousFromPartialSumsΣ index-large (ν , partial-cont) =
  ν ,
  powerSeriesSumUniformlyContinuousFromPartialSums
    index-large
    partial-cont


powerSeriesSumContinuousAtFromPartialSums :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {ν : PrecisionModulus} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBallWith a ρ χ ν →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  PowerSeriesSumContinuousAtWith a ρ μ convergence h h-bound ν
powerSeriesSumContinuousAtFromPartialSums index-large partial-cont =
  uniformlyContinuousPowerSeriesSum→continuousAt
    (powerSeriesSumUniformlyContinuousFromPartialSums
      index-large
      partial-cont)


powerSeriesSumContinuousAtFromPartialSumsΣ :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  PowerSeriesSumContinuousAt a ρ μ convergence h h-bound
powerSeriesSumContinuousAtFromPartialSumsΣ index-large (ν , partial-cont) h h-bound =
  ν ,
  powerSeriesSumContinuousAtFromPartialSums
    index-large
    partial-cont
    h
    h-bound


powerSeriesSumUniformlyContinuousFromCoefficientBoundsWith :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {κ : ℕ → ℚ⁺} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesCoefficientBoundsWith a κ →
  PowerSeriesSumUniformlyContinuousOnBallWith
    a
    ρ
    μ
    convergence
    (powerSeriesPartialSumsModulusFromCoefficientBounds κ ρ χ)
powerSeriesSumUniformlyContinuousFromCoefficientBoundsWith
  index-large
  coeffBounds =
  powerSeriesSumUniformlyContinuousFromPartialSums
    index-large
    (powerSeriesPartialSumsUniformlyContinuousOnBallFromCoefficientBoundsWith
      coeffBounds)


powerSeriesSumUniformlyContinuousFromCoefficientBounds :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesCoefficientBounds a →
  PowerSeriesSumUniformlyContinuousOnBall a ρ μ convergence
powerSeriesSumUniformlyContinuousFromCoefficientBounds
  {ρ = ρ}
  {χ = χ}
  index-large
  (κ , coeffBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds κ ρ χ ,
  powerSeriesSumUniformlyContinuousFromCoefficientBoundsWith
    index-large
    coeffBounds


powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonicalWith :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {κ : ℕ → ℚ⁺} →
  PowerSeriesCoefficientBoundsWith a κ →
  PowerSeriesSumUniformlyContinuousOnBallWith
    a
    ρ
    μ
    convergence
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      κ
      ρ
      (powerSeriesLimitApproximationIndex μ))
powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonicalWith
  {μ = μ}
  coeffBounds =
  powerSeriesSumUniformlyContinuousFromCoefficientBoundsWith
    {χ = powerSeriesLimitApproximationIndex μ}
    (λ _ → NatOrder.≤-refl)
    coeffBounds


powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  PowerSeriesCoefficientBounds a →
  PowerSeriesSumUniformlyContinuousOnBall a ρ μ convergence
powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical
  {ρ = ρ}
  {μ = μ}
  (κ , coeffBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    κ
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonicalWith
    coeffBounds


powerSeriesSumUniformlyContinuousFromBallTermBoundsWith :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {κ : ℕ → ℚ⁺} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  PowerSeriesSumUniformlyContinuousOnBallWith
    a
    ρ
    μ
    convergence
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      χ)
powerSeriesSumUniformlyContinuousFromBallTermBoundsWith
  {ρ = ρ}
  index-large
  termBounds =
  powerSeriesSumUniformlyContinuousFromCoefficientBoundsWith
    index-large
    (powerSeriesCoefficientBoundsFromBallTermBoundsWith ρ termBounds)


powerSeriesSumUniformlyContinuousFromBallTermBounds :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  PowerSeriesSumUniformlyContinuousOnBall a ρ μ convergence
powerSeriesSumUniformlyContinuousFromBallTermBounds
  {ρ = ρ}
  {χ = χ}
  index-large
  (κ , termBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    χ ,
  powerSeriesSumUniformlyContinuousFromBallTermBoundsWith
    index-large
    termBounds


powerSeriesSumUniformlyContinuousFromBallTermBoundsCanonicalWith :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {κ : ℕ → ℚ⁺} →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  PowerSeriesSumUniformlyContinuousOnBallWith
    a
    ρ
    μ
    convergence
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
powerSeriesSumUniformlyContinuousFromBallTermBoundsCanonicalWith
  {μ = μ}
  termBounds =
  powerSeriesSumUniformlyContinuousFromBallTermBoundsWith
    {χ = powerSeriesLimitApproximationIndex μ}
    (λ _ → NatOrder.≤-refl)
    termBounds


powerSeriesSumUniformlyContinuousFromBallTermBoundsCanonical :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  PowerSeriesSumUniformlyContinuousOnBall a ρ μ convergence
powerSeriesSumUniformlyContinuousFromBallTermBoundsCanonical
  {ρ = ρ}
  {μ = μ}
  (κ , termBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  powerSeriesSumUniformlyContinuousFromBallTermBoundsCanonicalWith
    termBounds


powerSeriesSumContinuousAtFromCoefficientBoundsWith :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {κ : ℕ → ℚ⁺} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesCoefficientBoundsWith a κ →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  PowerSeriesSumContinuousAtWith
    a
    ρ
    μ
    convergence
    h
    h-bound
    (powerSeriesPartialSumsModulusFromCoefficientBounds κ ρ χ)
powerSeriesSumContinuousAtFromCoefficientBoundsWith
  index-large
  coeffBounds =
  uniformlyContinuousPowerSeriesSum→continuousAt
    (powerSeriesSumUniformlyContinuousFromCoefficientBoundsWith
      index-large
      coeffBounds)


powerSeriesSumContinuousAtFromCoefficientBounds :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesCoefficientBounds a →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  PowerSeriesSumContinuousAt a ρ μ convergence h h-bound
powerSeriesSumContinuousAtFromCoefficientBounds
  {ρ = ρ}
  {χ = χ}
  index-large
  (κ , coeffBounds)
  h
  h-bound =
  powerSeriesPartialSumsModulusFromCoefficientBounds κ ρ χ ,
  powerSeriesSumContinuousAtFromCoefficientBoundsWith
    index-large
    coeffBounds
    h
    h-bound


powerSeriesSumContinuousAtFromCoefficientBoundsCanonicalWith :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {κ : ℕ → ℚ⁺} →
  PowerSeriesCoefficientBoundsWith a κ →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  PowerSeriesSumContinuousAtWith
    a
    ρ
    μ
    convergence
    h
    h-bound
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      κ
      ρ
      (powerSeriesLimitApproximationIndex μ))
powerSeriesSumContinuousAtFromCoefficientBoundsCanonicalWith
  {μ = μ}
  coeffBounds =
  powerSeriesSumContinuousAtFromCoefficientBoundsWith
    {χ = powerSeriesLimitApproximationIndex μ}
    (λ _ → NatOrder.≤-refl)
    coeffBounds


powerSeriesSumContinuousAtFromCoefficientBoundsCanonical :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  PowerSeriesCoefficientBounds a →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  PowerSeriesSumContinuousAt a ρ μ convergence h h-bound
powerSeriesSumContinuousAtFromCoefficientBoundsCanonical
  {ρ = ρ}
  {μ = μ}
  (κ , coeffBounds)
  h
  h-bound =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    κ
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  powerSeriesSumContinuousAtFromCoefficientBoundsCanonicalWith
    coeffBounds
    h
    h-bound


powerSeriesSumContinuousAtFromBallTermBoundsWith :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {κ : ℕ → ℚ⁺} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  PowerSeriesSumContinuousAtWith
    a
    ρ
    μ
    convergence
    h
    h-bound
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      χ)
powerSeriesSumContinuousAtFromBallTermBoundsWith
  {ρ = ρ}
  index-large
  termBounds =
  powerSeriesSumContinuousAtFromCoefficientBoundsWith
    index-large
    (powerSeriesCoefficientBoundsFromBallTermBoundsWith ρ termBounds)


powerSeriesSumContinuousAtFromBallTermBounds :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  PowerSeriesSumContinuousAt a ρ μ convergence h h-bound
powerSeriesSumContinuousAtFromBallTermBounds
  {ρ = ρ}
  {χ = χ}
  index-large
  (κ , termBounds)
  h
  h-bound =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    χ ,
  powerSeriesSumContinuousAtFromBallTermBoundsWith
    index-large
    termBounds
    h
    h-bound


powerSeriesSumContinuousAtFromBallTermBoundsCanonicalWith :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {κ : ℕ → ℚ⁺} →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  PowerSeriesSumContinuousAtWith
    a
    ρ
    μ
    convergence
    h
    h-bound
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
powerSeriesSumContinuousAtFromBallTermBoundsCanonicalWith
  {μ = μ}
  termBounds =
  powerSeriesSumContinuousAtFromBallTermBoundsWith
    {χ = powerSeriesLimitApproximationIndex μ}
    (λ _ → NatOrder.≤-refl)
    termBounds


powerSeriesSumContinuousAtFromBallTermBoundsCanonical :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  PowerSeriesSumContinuousAt a ρ μ convergence h h-bound
powerSeriesSumContinuousAtFromBallTermBoundsCanonical
  {ρ = ρ}
  {μ = μ}
  (κ , termBounds)
  h
  h-bound =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  powerSeriesSumContinuousAtFromBallTermBoundsCanonicalWith
    termBounds
    h
    h-bound


centeredPowerSeriesSumUniformlyContinuousFromDisplacement :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {ν : PrecisionModulus} →
  PowerSeriesSumUniformlyContinuousOnBallWith a ρ μ convergence ν →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith a c ρ μ convergence ν
centeredPowerSeriesSumUniformlyContinuousFromDisplacement
  {c = c}
  uniform
  ε
  {x = x}
  {y = y}
  x-inBall
  y-inBall
  x∼y =
  uniform
    ε
    (InPowerSeriesBall.displacementBound x-inBall)
    (InPowerSeriesBall.displacementBound y-inBall)
    (add-close-left x∼y (-ᶜ c))


centeredPowerSeriesSumUniformlyContinuousFromDisplacementΣ :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  PowerSeriesSumUniformlyContinuousOnBall a ρ μ convergence →
  CenteredPowerSeriesSumUniformlyContinuousOnBall a c ρ μ convergence
centeredPowerSeriesSumUniformlyContinuousFromDisplacementΣ (ν , uniform) =
  ν ,
  centeredPowerSeriesSumUniformlyContinuousFromDisplacement uniform


centeredPowerSeriesSumUniformlyContinuousFromPartialSums :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {ν : PrecisionModulus} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBallWith a ρ χ ν →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith a c ρ μ convergence ν
centeredPowerSeriesSumUniformlyContinuousFromPartialSums index-large partial-cont =
  centeredPowerSeriesSumUniformlyContinuousFromDisplacement
    (powerSeriesSumUniformlyContinuousFromPartialSums
      index-large
      partial-cont)


centeredPowerSeriesSumUniformlyContinuousFromPartialSumsΣ :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ →
  CenteredPowerSeriesSumUniformlyContinuousOnBall a c ρ μ convergence
centeredPowerSeriesSumUniformlyContinuousFromPartialSumsΣ index-large partial-cont =
  centeredPowerSeriesSumUniformlyContinuousFromDisplacementΣ
    (powerSeriesSumUniformlyContinuousFromPartialSumsΣ
      index-large
      partial-cont)


centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsWith :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {κ : ℕ → ℚ⁺} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesCoefficientBoundsWith a κ →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith
    a
    c
    ρ
    μ
    convergence
    (powerSeriesPartialSumsModulusFromCoefficientBounds κ ρ χ)
centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsWith
  index-large
  coeffBounds =
  centeredPowerSeriesSumUniformlyContinuousFromDisplacement
    (powerSeriesSumUniformlyContinuousFromCoefficientBoundsWith
      index-large
      coeffBounds)


centeredPowerSeriesSumUniformlyContinuousFromCoefficientBounds :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesCoefficientBounds a →
  CenteredPowerSeriesSumUniformlyContinuousOnBall a c ρ μ convergence
centeredPowerSeriesSumUniformlyContinuousFromCoefficientBounds
  index-large
  bounds =
  centeredPowerSeriesSumUniformlyContinuousFromDisplacementΣ
    (powerSeriesSumUniformlyContinuousFromCoefficientBounds
      index-large
      bounds)


centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonicalWith :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {κ : ℕ → ℚ⁺} →
  PowerSeriesCoefficientBoundsWith a κ →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith
    a
    c
    ρ
    μ
    convergence
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      κ
      ρ
      (powerSeriesLimitApproximationIndex μ))
centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonicalWith
  coeffBounds =
  centeredPowerSeriesSumUniformlyContinuousFromDisplacement
    (powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonicalWith
      coeffBounds)


centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  PowerSeriesCoefficientBounds a →
  CenteredPowerSeriesSumUniformlyContinuousOnBall a c ρ μ convergence
centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical
  bounds =
  centeredPowerSeriesSumUniformlyContinuousFromDisplacementΣ
    (powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical
      bounds)


centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsWith :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {κ : ℕ → ℚ⁺} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith
    a
    c
    ρ
    μ
    convergence
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      χ)
centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsWith
  index-large
  termBounds =
  centeredPowerSeriesSumUniformlyContinuousFromDisplacement
    (powerSeriesSumUniformlyContinuousFromBallTermBoundsWith
      index-large
      termBounds)


centeredPowerSeriesSumUniformlyContinuousFromBallTermBounds :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  ((ε : ℚ⁺) →
    NatOrder._≤_ (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  CenteredPowerSeriesSumUniformlyContinuousOnBall a c ρ μ convergence
centeredPowerSeriesSumUniformlyContinuousFromBallTermBounds
  index-large
  bounds =
  centeredPowerSeriesSumUniformlyContinuousFromDisplacementΣ
    (powerSeriesSumUniformlyContinuousFromBallTermBounds
      index-large
      bounds)


centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsCanonicalWith :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {κ : ℕ → ℚ⁺} →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith
    a
    c
    ρ
    μ
    convergence
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsCanonicalWith
  termBounds =
  centeredPowerSeriesSumUniformlyContinuousFromDisplacement
    (powerSeriesSumUniformlyContinuousFromBallTermBoundsCanonicalWith
      termBounds)


centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsCanonical :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  CenteredPowerSeriesSumUniformlyContinuousOnBall a c ρ μ convergence
centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsCanonical
  bounds =
  centeredPowerSeriesSumUniformlyContinuousFromDisplacementΣ
    (powerSeriesSumUniformlyContinuousFromBallTermBoundsCanonical
      bounds)
