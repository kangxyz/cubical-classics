{-

Power-series convergence on bounded balls

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Radius where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; max)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)

import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Metric.Instances.CauchyReals
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Data.PositiveRationals


record HasPowerSeriesOnBallWith
    (a : PowerSeries)
    (ρ : ℚ⁺)
    (μ : ℚ⁺ → ℕ) :
    Type₀ where
  no-eta-equality

  field
    antitoneModulus :
      AntitoneTailModulus μ
    tailBound :
      (h : ℝᶜ) →
      BoundedByᶜ ρ h →
      PowerSeriesTailBound a h μ


HasPowerSeriesOnBall :
  PowerSeries →
  ℚ⁺ →
  Type₀
HasPowerSeriesOnBall a ρ =
  Σ[ μ ∈ (ℚ⁺ → ℕ) ] HasPowerSeriesOnBallWith a ρ μ


powerSeriesSumOnBall :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  ℝᶜ
powerSeriesSumOnBall a ρ μ convergence h h-bound =
  powerSeriesSumFromFiniteTailBound
    a
    h
    μ
    (HasPowerSeriesOnBallWith.tailBound convergence h h-bound)
    (HasPowerSeriesOnBallWith.antitoneModulus convergence)


powerSeriesConvergesOnBall :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (powerSeriesTerm a h)
      μ
      (HasPowerSeriesOnBallWith.tailBound convergence h h-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus convergence))
    (powerSeriesSumOnBall a ρ μ convergence h h-bound)
powerSeriesConvergesOnBall a ρ μ convergence h h-bound =
  powerSeriesConvergesFromFiniteTailBound
    a
    h
    μ
    (HasPowerSeriesOnBallWith.tailBound convergence h h-bound)
    (HasPowerSeriesOnBallWith.antitoneModulus convergence)


powerSeriesSumOnBallFrom :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  HasPowerSeriesOnBall a ρ →
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  ℝᶜ
powerSeriesSumOnBallFrom a ρ (μ , convergence) h h-bound =
  powerSeriesSumOnBall a ρ μ convergence h h-bound


powerSeriesConvergesOnBallFrom :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (convergence : HasPowerSeriesOnBall a ρ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (powerSeriesTerm a h)
      (fst convergence)
      (HasPowerSeriesOnBallWith.tailBound (snd convergence) h h-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus (snd convergence)))
    (powerSeriesSumOnBallFrom a ρ convergence h h-bound)
powerSeriesConvergesOnBallFrom a ρ (μ , convergence) h h-bound =
  powerSeriesConvergesOnBall a ρ μ convergence h h-bound


PowerSeriesSumContinuousAtWith :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  PrecisionModulus →
  Type₀
PowerSeriesSumContinuousAtWith a ρ μ convergence h h-bound ν =
  (ε : ℚ⁺) →
  {k : ℝᶜ} →
  (k-bound : BoundedByᶜ ρ k) →
  MetricSpace.Close CauchyRealsMetricSpace h (ν ε) k →
  MetricSpace.Close CauchyRealsMetricSpace
    (powerSeriesSumOnBall a ρ μ convergence h h-bound)
    ε
    (powerSeriesSumOnBall a ρ μ convergence k k-bound)


PowerSeriesSumContinuousAt :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  Type₀
PowerSeriesSumContinuousAt a ρ μ convergence h h-bound =
  Σ[ ν ∈ PrecisionModulus ]
    PowerSeriesSumContinuousAtWith a ρ μ convergence h h-bound ν


PowerSeriesSumUniformlyContinuousOnBallWith :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  PrecisionModulus →
  Type₀
PowerSeriesSumUniformlyContinuousOnBallWith a ρ μ convergence ν =
  (ε : ℚ⁺) →
  {h k : ℝᶜ} →
  (h-bound : BoundedByᶜ ρ h) →
  (k-bound : BoundedByᶜ ρ k) →
  MetricSpace.Close CauchyRealsMetricSpace h (ν ε) k →
  MetricSpace.Close CauchyRealsMetricSpace
    (powerSeriesSumOnBall a ρ μ convergence h h-bound)
    ε
    (powerSeriesSumOnBall a ρ μ convergence k k-bound)


PowerSeriesSumUniformlyContinuousOnBall :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  Type₀
PowerSeriesSumUniformlyContinuousOnBall a ρ μ convergence =
  Σ[ ν ∈ PrecisionModulus ]
    PowerSeriesSumUniformlyContinuousOnBallWith a ρ μ convergence ν


uniformlyContinuousPowerSeriesSum→continuousAt :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  {ν : PrecisionModulus} →
  PowerSeriesSumUniformlyContinuousOnBallWith a ρ μ convergence ν →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  PowerSeriesSumContinuousAtWith a ρ μ convergence h h-bound ν
uniformlyContinuousPowerSeriesSum→continuousAt uniform h h-bound ε k-bound =
  uniform ε h-bound k-bound


powerSeriesSumOnBall-constantModulusPartialSum :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  (N : ℕ) →
  (convergence : HasPowerSeriesOnBallWith a ρ (λ _ → N)) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall a ρ (λ _ → N) convergence h h-bound ≡
  powerSeriesPartialSum a h N
powerSeriesSumOnBall-constantModulusPartialSum N convergence h h-bound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    (powerSeriesSumOnBall _ _ (λ _ → N) convergence h h-bound)
    (powerSeriesPartialSum _ h N)
    (λ ε →
      seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm _ h)
        (λ _ → N)
        (HasPowerSeriesOnBallWith.tailBound convergence h h-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus convergence)
        ε
        N
        NatOrder.≤-refl)


powerSeriesSumOnBall-bound-independent :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (h : ℝᶜ) →
  (h-bound k-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall a ρ μ convergence h h-bound ≡
  powerSeriesSumOnBall a ρ μ convergence h k-bound
powerSeriesSumOnBall-bound-independent {a = a} {ρ = ρ} {μ = μ}
  convergence
  h
  h-bound
  k-bound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    leftSum
    rightSum
    (λ ε →
      subst
        (λ κ → MetricSpace.Close CauchyRealsMetricSpace leftSum κ rightSum)
        (half⁺+half⁺≡ ε)
        (MetricSpace.close-triangle
          CauchyRealsMetricSpace
          (leftTail ε)
          (MetricSpace.close-sym CauchyRealsMetricSpace (rightTail ε))))
  where
  leftSum : ℝᶜ
  leftSum =
    powerSeriesSumOnBall a ρ μ convergence h h-bound

  rightSum : ℝᶜ
  rightSum =
    powerSeriesSumOnBall a ρ μ convergence h k-bound

  tailClose :
    (h-bound' : BoundedByᶜ ρ h) →
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace
      (powerSeriesSumOnBall a ρ μ convergence h h-bound')
      (half⁺ ε)
      (powerSeriesPartialSum
        a
        h
        (μ (quarter⁺ (half⁺ (half⁺ ε)))))
  tailClose h-bound' ε =
    seriesSumFromFiniteTailBoundConvergesAt
      (powerSeriesTerm a h)
      μ
      (HasPowerSeriesOnBallWith.tailBound convergence h h-bound')
      (HasPowerSeriesOnBallWith.antitoneModulus convergence)
      (half⁺ ε)
      (μ (quarter⁺ (half⁺ (half⁺ ε))))
      NatOrder.≤-refl

  leftTail :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace
      leftSum
      (half⁺ ε)
      (powerSeriesPartialSum
        a
        h
        (μ (quarter⁺ (half⁺ (half⁺ ε)))))
  leftTail =
    tailClose h-bound

  rightTail :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace
      rightSum
      (half⁺ ε)
      (powerSeriesPartialSum
        a
        h
        (μ (quarter⁺ (half⁺ (half⁺ ε)))))
  rightTail =
    tailClose k-bound


powerSeriesSumOnBall-data-independent :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ ν : ℚ⁺ → ℕ} →
  (left : HasPowerSeriesOnBallWith a ρ μ) →
  (right : HasPowerSeriesOnBallWith a σ ν) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (k-bound : BoundedByᶜ σ h) →
  powerSeriesSumOnBall a ρ μ left h h-bound ≡
  powerSeriesSumOnBall a σ ν right h k-bound
powerSeriesSumOnBall-data-independent
  {a = a}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {ν = ν}
  left
  right
  h
  h-bound
  k-bound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    leftSum
    rightSum
    (λ ε →
      subst
        (λ κ → MetricSpace.Close CauchyRealsMetricSpace leftSum κ rightSum)
        (half⁺+half⁺≡ ε)
        (MetricSpace.close-triangle
          CauchyRealsMetricSpace
          (leftTail ε)
          (MetricSpace.close-sym CauchyRealsMetricSpace (rightTail ε))))
  where
  approximationIndex :
    ℚ⁺ →
    ℕ
  approximationIndex ε =
    max
      (μ (quarter⁺ (half⁺ (half⁺ ε))))
      (ν (quarter⁺ (half⁺ (half⁺ ε))))

  leftSum : ℝᶜ
  leftSum =
    powerSeriesSumOnBall a ρ μ left h h-bound

  rightSum : ℝᶜ
  rightSum =
    powerSeriesSumOnBall a σ ν right h k-bound

  leftTail :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace
      leftSum
      (half⁺ ε)
      (powerSeriesPartialSum a h (approximationIndex ε))
  leftTail ε =
    seriesSumFromFiniteTailBoundConvergesAt
      (powerSeriesTerm a h)
      μ
      (HasPowerSeriesOnBallWith.tailBound left h h-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus left)
      (half⁺ ε)
      (approximationIndex ε)
      (NatOrder.left-≤-max
        {m = μ (quarter⁺ (half⁺ (half⁺ ε)))}
        {n = ν (quarter⁺ (half⁺ (half⁺ ε)))})

  rightTail :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace
      rightSum
      (half⁺ ε)
      (powerSeriesPartialSum a h (approximationIndex ε))
  rightTail ε =
    seriesSumFromFiniteTailBoundConvergesAt
      (powerSeriesTerm a h)
      ν
      (HasPowerSeriesOnBallWith.tailBound right h k-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus right)
      (half⁺ ε)
      (approximationIndex ε)
      (NatOrder.right-≤-max
        {n = ν (quarter⁺ (half⁺ (half⁺ ε)))}
        {m = μ (quarter⁺ (half⁺ (half⁺ ε)))})


powerSeriesSumOnBallFrom-data-independent :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  (left : HasPowerSeriesOnBall a ρ) →
  (right : HasPowerSeriesOnBall a σ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (k-bound : BoundedByᶜ σ h) →
  powerSeriesSumOnBallFrom a ρ left h h-bound ≡
  powerSeriesSumOnBallFrom a σ right h k-bound
powerSeriesSumOnBallFrom-data-independent
  (μ , left)
  (ν , right)
  h
  h-bound
  k-bound =
  powerSeriesSumOnBall-data-independent
    left
    right
    h
    h-bound
    k-bound


hasPowerSeriesOnBallWith-cong :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  ((n : ℕ) → a n ≡ b n) →
  HasPowerSeriesOnBallWith a ρ μ →
  HasPowerSeriesOnBallWith b ρ μ
hasPowerSeriesOnBallWith-cong {a = a} {b = b} {μ = μ} coeff≡ convergence =
  record
    { antitoneModulus =
        HasPowerSeriesOnBallWith.antitoneModulus convergence
    ; tailBound =
        λ h h-bound →
          subst
            (λ u → TailBound u μ)
            (powerSeriesTerm-cong-coefficients coeff≡ h)
            (HasPowerSeriesOnBallWith.tailBound convergence h h-bound)
    }


hasPowerSeriesOnBall-cong :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  ((n : ℕ) → a n ≡ b n) →
  HasPowerSeriesOnBall a ρ →
  HasPowerSeriesOnBall b ρ
hasPowerSeriesOnBall-cong coeff≡ (μ , convergence) =
  μ , hasPowerSeriesOnBallWith-cong coeff≡ convergence


hasPowerSeriesOnSubballWith :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  radius ρ ℚOrder.≤ radius σ →
  HasPowerSeriesOnBallWith a σ μ →
  HasPowerSeriesOnBallWith a ρ μ
hasPowerSeriesOnSubballWith {ρ = ρ} {σ = σ} ρ≤σ convergence =
  record
    { antitoneModulus =
        HasPowerSeriesOnBallWith.antitoneModulus convergence
    ; tailBound =
        λ h h-bound →
          HasPowerSeriesOnBallWith.tailBound
            convergence
            h
            (bounded-byᶜ-monotone ρ≤σ h-bound)
    }


hasPowerSeriesOnSmallerBallWith :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  radius ρ ℚOrder.< radius σ →
  HasPowerSeriesOnBallWith a σ μ →
  HasPowerSeriesOnBallWith a ρ μ
hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ =
  hasPowerSeriesOnSubballWith
    (ℚOrder.<Weaken≤ (radius ρ) (radius σ) ρ<σ)


hasPowerSeriesOnSubball :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  radius ρ ℚOrder.≤ radius σ →
  HasPowerSeriesOnBall a σ →
  HasPowerSeriesOnBall a ρ
hasPowerSeriesOnSubball ρ≤σ (μ , convergence) =
  μ , hasPowerSeriesOnSubballWith ρ≤σ convergence


hasPowerSeriesOnSmallerBall :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  radius ρ ℚOrder.< radius σ →
  HasPowerSeriesOnBall a σ →
  HasPowerSeriesOnBall a ρ
hasPowerSeriesOnSmallerBall {ρ = ρ} {σ = σ} ρ<σ =
  hasPowerSeriesOnSubball
    (ℚOrder.<Weaken≤ (radius ρ) (radius σ) ρ<σ)


record HasPowerSeriesRadius
    (a : PowerSeries)
    (R : ℚ⁺) :
    Type₀ where
  no-eta-equality

  field
    onSubball :
      (ρ : ℚ⁺) →
      radius ρ ℚOrder.< radius R →
      HasPowerSeriesOnBall a ρ


HasInfinitePowerSeriesRadius :
  PowerSeries →
  Type₀
HasInfinitePowerSeriesRadius a =
  (ρ : ℚ⁺) → HasPowerSeriesOnBall a ρ


hasInfinitePowerSeriesRadius→radius :
  {a : PowerSeries} →
  (R : ℚ⁺) →
  HasInfinitePowerSeriesRadius a →
  HasPowerSeriesRadius a R
hasInfinitePowerSeriesRadius→radius R radiusData =
  record
    { onSubball =
        λ ρ _ →
          radiusData ρ
    }


hasPowerSeriesRadius-cong :
  {a b : PowerSeries} →
  {R : ℚ⁺} →
  ((n : ℕ) → a n ≡ b n) →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius b R
hasPowerSeriesRadius-cong coeff≡ radiusData =
  record
    { onSubball =
        λ ρ ρ<R →
          hasPowerSeriesOnBall-cong
            coeff≡
            (HasPowerSeriesRadius.onSubball radiusData ρ ρ<R)
    }


hasInfinitePowerSeriesRadius-cong :
  {a b : PowerSeries} →
  ((n : ℕ) → a n ≡ b n) →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius b
hasInfinitePowerSeriesRadius-cong coeff≡ radiusData ρ =
  hasPowerSeriesOnBall-cong coeff≡ (radiusData ρ)


centeredDisplacement :
  ℝᶜ →
  ℝᶜ →
  ℝᶜ
centeredDisplacement c x =
  x +ᶜ (-ᶜ c)


record InPowerSeriesBall
    (c : ℝᶜ)
    (ρ : ℚ⁺)
    (x : ℝᶜ) :
    Type₀ where
  no-eta-equality

  field
    displacementBound :
      BoundedByᶜ ρ (centeredDisplacement c x)


centeredPowerSeriesTerm :
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  ℕ →
  ℝᶜ
centeredPowerSeriesTerm a c x =
  powerSeriesTerm a (centeredDisplacement c x)


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


centeredPowerSeriesConvergesOnBall :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (centeredPowerSeriesTerm a c x)
      μ
      (HasPowerSeriesOnBallWith.tailBound
        convergence
        (centeredDisplacement c x)
        (InPowerSeriesBall.displacementBound inBall))
      (HasPowerSeriesOnBallWith.antitoneModulus convergence))
    (centeredPowerSeriesSumOnBall a c ρ μ convergence x inBall)
centeredPowerSeriesConvergesOnBall a c ρ μ convergence x inBall =
  powerSeriesConvergesOnBall
    a
    ρ
    μ
    convergence
    (centeredDisplacement c x)
    (InPowerSeriesBall.displacementBound inBall)


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


centeredPowerSeriesConvergesOnBallFrom :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (convergence : HasPowerSeriesOnBall a ρ) →
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (centeredPowerSeriesTerm a c x)
      (fst convergence)
      (HasPowerSeriesOnBallWith.tailBound
        (snd convergence)
        (centeredDisplacement c x)
        (InPowerSeriesBall.displacementBound inBall))
      (HasPowerSeriesOnBallWith.antitoneModulus (snd convergence)))
    (centeredPowerSeriesSumOnBallFrom a c ρ convergence x inBall)
centeredPowerSeriesConvergesOnBallFrom a c ρ (μ , convergence) x inBall =
  centeredPowerSeriesConvergesOnBall a c ρ μ convergence x inBall


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
