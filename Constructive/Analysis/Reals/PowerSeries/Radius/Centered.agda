{-

Part of Constructive.Analysis.Reals.PowerSeries.Radius

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Radius.Centered where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (neg-zeroᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.Radius.Sum
open import Constructive.Analysis.Reals.PowerSeries.Radius.Everywhere

centeredDisplacement :
  ℝᶜ →
  ℝᶜ →
  ℝᶜ
centeredDisplacement c x =
  x +ᶜ (-ᶜ c)


centeredDisplacement-zero :
  (x : ℝᶜ) →
  centeredDisplacement 0ᶜ x ≡ x
centeredDisplacement-zero x =
  cong (x +ᶜ_) neg-zeroᶜ ∙
  add-zero-right x


centeredDisplacement-center-plus :
  (c x : ℝᶜ) →
  centeredDisplacement c (c +ᶜ x) ≡ x
centeredDisplacement-center-plus c x =
  sym (add-assoc c x (-ᶜ c)) ∙
  cong (c +ᶜ_) (add-comm x (-ᶜ c)) ∙
  add-assoc c (-ᶜ c) x ∙
  cong (_+ᶜ x) (add-inverse-right c) ∙
  add-zero-left x


add-center-centeredDisplacement :
  (c x : ℝᶜ) →
  c +ᶜ centeredDisplacement c x ≡ x
add-center-centeredDisplacement c x =
  cong (c +ᶜ_) (add-comm x (-ᶜ c)) ∙
  add-assoc c (-ᶜ c) x ∙
  cong (_+ᶜ x) (add-inverse-right c) ∙
  add-zero-left x


add-center-centeredDisplacement-forward :
  (c x h : ℝᶜ) →
  c +ᶜ (centeredDisplacement c x +ᶜ h) ≡ x +ᶜ h
add-center-centeredDisplacement-forward c x h =
  add-assoc c (centeredDisplacement c x) h ∙
  cong (_+ᶜ h) (add-center-centeredDisplacement c x)


record InPowerSeriesBall
    (c : ℝᶜ)
    (ρ : ℚ⁺)
    (x : ℝᶜ) :
    Type₀ where
  no-eta-equality

  field
    displacementBound :
      BoundedByᶜ ρ (centeredDisplacement c x)


inPowerSeriesBallAtZeroFromBound :
  {ρ : ℚ⁺} →
  {x : ℝᶜ} →
  BoundedByᶜ ρ x →
  InPowerSeriesBall 0ᶜ ρ x
inPowerSeriesBallAtZeroFromBound {ρ = ρ} {x = x} x-bound =
  record
    { displacementBound =
        subst
          (BoundedByᶜ ρ)
          (sym (centeredDisplacement-zero x))
          x-bound
    }


inPowerSeriesBallAtZero→bound :
  {ρ : ℚ⁺} →
  {x : ℝᶜ} →
  InPowerSeriesBall 0ᶜ ρ x →
  BoundedByᶜ ρ x
inPowerSeriesBallAtZero→bound {ρ = ρ} {x = x} inBall =
  subst
    (BoundedByᶜ ρ)
    (centeredDisplacement-zero x)
    (InPowerSeriesBall.displacementBound inBall)


inPowerSeriesBallAtCenterPlusFromBound :
  {ρ : ℚ⁺} →
  (c : ℝᶜ) →
  {x : ℝᶜ} →
  BoundedByᶜ ρ x →
  InPowerSeriesBall c ρ (c +ᶜ x)
inPowerSeriesBallAtCenterPlusFromBound {ρ = ρ} c {x = x} x-bound =
  record
    { displacementBound =
        subst
          (BoundedByᶜ ρ)
          (sym (centeredDisplacement-center-plus c x))
          x-bound
    }


centeredPowerSeriesSumOnBall :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  (x : ℝᶜ) →
  InPowerSeriesBall c ρ x →
  ℝᶜ
centeredPowerSeriesSumOnBall a c ρ μ convergence x inBall =
  powerSeriesSumOnBall
    a
    ρ
    μ
    convergence
    (centeredDisplacement c x)
    (InPowerSeriesBall.displacementBound inBall)


centeredPowerSeriesSumOnBallAtZero-path :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (x : ℝᶜ) →
  (x-bound : BoundedByᶜ ρ x) →
  centeredPowerSeriesSumOnBall
    a
    0ᶜ
    ρ
    μ
    convergence
    x
    (inPowerSeriesBallAtZeroFromBound x-bound)
  ≡
  powerSeriesSumOnBall a ρ μ convergence x x-bound
centeredPowerSeriesSumOnBallAtZero-path convergence x x-bound =
  powerSeriesSumOnBall-center-path
    convergence
    (centeredDisplacement-zero x)
    _
    x-bound


centeredPowerSeriesSumOnBallAtCenterPlus-path :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (c x : ℝᶜ) →
  (x-bound : BoundedByᶜ ρ x) →
  centeredPowerSeriesSumOnBall
    a
    c
    ρ
    μ
    convergence
    (c +ᶜ x)
    (inPowerSeriesBallAtCenterPlusFromBound c x-bound)
  ≡
  powerSeriesSumOnBall a ρ μ convergence x x-bound
centeredPowerSeriesSumOnBallAtCenterPlus-path convergence c x x-bound =
  powerSeriesSumOnBall-center-path
    convergence
    (centeredDisplacement-center-plus c x)
    _
    x-bound


centeredPowerSeriesSumOnBall-inBall-independent :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (x : ℝᶜ) →
  (x-inBall y-inBall : InPowerSeriesBall c ρ x) →
  centeredPowerSeriesSumOnBall a c ρ μ convergence x x-inBall ≡
  centeredPowerSeriesSumOnBall a c ρ μ convergence x y-inBall
centeredPowerSeriesSumOnBall-inBall-independent convergence x x-inBall y-inBall =
  powerSeriesSumOnBall-bound-independent
    convergence
    _
    (InPowerSeriesBall.displacementBound x-inBall)
    (InPowerSeriesBall.displacementBound y-inBall)


centeredPowerSeriesSumOnBall-data-independent :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ ν : ℚ⁺ → ℕ} →
  (left : HasPowerSeriesOnBallWith a ρ μ) →
  (right : HasPowerSeriesOnBallWith a σ ν) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  (y-inBall : InPowerSeriesBall c σ x) →
  centeredPowerSeriesSumOnBall a c ρ μ left x x-inBall ≡
  centeredPowerSeriesSumOnBall a c σ ν right x y-inBall
centeredPowerSeriesSumOnBall-data-independent left right x x-inBall y-inBall =
  powerSeriesSumOnBall-data-independent
    left
    right
    _
    (InPowerSeriesBall.displacementBound x-inBall)
    (InPowerSeriesBall.displacementBound y-inBall)


centeredPowerSeriesSumOnBallFrom :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  HasPowerSeriesOnBall a ρ →
  (x : ℝᶜ) →
  InPowerSeriesBall c ρ x →
  ℝᶜ
centeredPowerSeriesSumOnBallFrom a c ρ (μ , convergence) x inBall =
  centeredPowerSeriesSumOnBall a c ρ μ convergence x inBall


centeredPowerSeriesSumOnBallFrom-data-independent :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  (left : HasPowerSeriesOnBall a ρ) →
  (right : HasPowerSeriesOnBall a σ) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  (y-inBall : InPowerSeriesBall c σ x) →
  centeredPowerSeriesSumOnBallFrom a c ρ left x x-inBall ≡
  centeredPowerSeriesSumOnBallFrom a c σ right x y-inBall
centeredPowerSeriesSumOnBallFrom-data-independent
  (μ , left)
  (ν , right)
  x
  x-inBall
  y-inBall =
  centeredPowerSeriesSumOnBall-data-independent
    left
    right
    x
    x-inBall
    y-inBall


centeredPowerSeriesSumEverywhere :
  (a : PowerSeries) →
  ℝᶜ →
  HasInfinitePowerSeriesRadius a →
  ℝᶜ →
  ℝᶜ
centeredPowerSeriesSumEverywhere a c radiusData x =
  powerSeriesSumEverywhere a radiusData (centeredDisplacement c x)


centeredPowerSeriesSumEverywhere-bound-path :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  centeredPowerSeriesSumEverywhere a c radiusData x ≡
  centeredPowerSeriesSumOnBallFrom a c ρ (radiusData ρ) x x-inBall
centeredPowerSeriesSumEverywhere-bound-path
  a
  c
  radiusData
  ρ
  x
  x-inBall =
  powerSeriesSumEverywhere-bound-path
    a
    radiusData
    ρ
    (centeredDisplacement c x)
    (InPowerSeriesBall.displacementBound x-inBall)


centeredPowerSeriesSumEverywhere-coefficients-path :
  {a b : PowerSeries} →
  ((n : ℕ) → a n ≡ b n) →
  (leftRadius : HasInfinitePowerSeriesRadius a) →
  (rightRadius : HasInfinitePowerSeriesRadius b) →
  (c x : ℝᶜ) →
  centeredPowerSeriesSumEverywhere a c leftRadius x ≡
  centeredPowerSeriesSumEverywhere b c rightRadius x
centeredPowerSeriesSumEverywhere-coefficients-path
  coeff≡
  leftRadius
  rightRadius
  c
  x =
  powerSeriesSumEverywhere-coefficients-path
    coeff≡
    leftRadius
    rightRadius
    (centeredDisplacement c x)


centeredPowerSeriesSumOnBall-constantModulusPartialSum :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  (N : ℕ) →
  (convergence : HasPowerSeriesOnBallWith a ρ (λ _ → N)) →
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  centeredPowerSeriesSumOnBall a c ρ (λ _ → N) convergence x inBall ≡
  powerSeriesPartialSum a (centeredDisplacement c x) N
centeredPowerSeriesSumOnBall-constantModulusPartialSum
  {c = c}
  N
  convergence
  x
  inBall =
  powerSeriesSumOnBall-constantModulusPartialSum
    N
    convergence
    (centeredDisplacement c x)
    (InPowerSeriesBall.displacementBound inBall)


CenteredPowerSeriesSumUniformlyContinuousOnBallWith :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  PrecisionModulus →
  Type₀
CenteredPowerSeriesSumUniformlyContinuousOnBallWith a c ρ μ convergence ν =
  (ε : ℚ⁺) →
  {x y : ℝᶜ} →
  (x-inBall : InPowerSeriesBall c ρ x) →
  (y-inBall : InPowerSeriesBall c ρ y) →
  MetricSpace.Close CauchyRealsMetricSpace x (ν ε) y →
  MetricSpace.Close CauchyRealsMetricSpace
    (centeredPowerSeriesSumOnBall a c ρ μ convergence x x-inBall)
    ε
    (centeredPowerSeriesSumOnBall a c ρ μ convergence y y-inBall)


CenteredPowerSeriesSumUniformlyContinuousOnBall :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  Type₀
CenteredPowerSeriesSumUniformlyContinuousOnBall a c ρ μ convergence =
  Σ[ ν ∈ PrecisionModulus ]
    CenteredPowerSeriesSumUniformlyContinuousOnBallWith
      a
      c
      ρ
      μ
      convergence
      ν
