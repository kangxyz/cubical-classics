{-

Part of Constructive.Analysis.Reals.PowerSeries.Radius

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Radius.Sum where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; max)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd ; _×_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁)

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
import Constructive.Analysis.Metric.Cauchy as MetricCauchy
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
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Data.PositiveRationals



HasPowerSeriesOnBallWith :
  PowerSeries →
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
HasPowerSeriesOnBallWith a ρ μ =
  AntitoneNatModulus μ ×
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    PowerSeriesTailBound a h μ)


hasPowerSeriesOnBallWith :
  {a : PowerSeries} {ρ : ℚ⁺} {μ : ℚ⁺ → ℕ} →
  AntitoneNatModulus μ →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    PowerSeriesTailBound a h μ) →
  HasPowerSeriesOnBallWith a ρ μ
hasPowerSeriesOnBallWith antitone tail =
  antitone , tail


module HasPowerSeriesOnBallWith
    {a : PowerSeries}
    {ρ : ℚ⁺}
    {μ : ℚ⁺ → ℕ}
    (convergence : HasPowerSeriesOnBallWith a ρ μ) where
  antitoneModulus :
    AntitoneNatModulus μ
  antitoneModulus =
    convergence .fst

  tailBound :
    (h : ℝᶜ) →
    BoundedByᶜ ρ h →
    PowerSeriesTailBound a h μ
  tailBound =
    convergence .snd


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


powerSeriesSumOnBall-center-path :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  {h k : ℝᶜ} →
  h ≡ k →
  (h-bound : BoundedByᶜ ρ h) →
  (k-bound : BoundedByᶜ ρ k) →
  powerSeriesSumOnBall a ρ μ convergence h h-bound ≡
  powerSeriesSumOnBall a ρ μ convergence k k-bound
powerSeriesSumOnBall-center-path
  {a = a}
  {ρ = ρ}
  {μ = μ}
  convergence
  {h = h}
  p
  h-bound
  k-bound =
  subst
    (λ z →
      (z-bound : BoundedByᶜ ρ z) →
      powerSeriesSumOnBall a ρ μ convergence h h-bound ≡
      powerSeriesSumOnBall a ρ μ convergence z z-bound)
    p
    (λ z-bound →
      powerSeriesSumOnBall-bound-independent
        convergence
        h
        h-bound
        z-bound)
    k-bound


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


powerSeriesSumOnBall-coefficients-path :
  {a b : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ ν : ℚ⁺ → ℕ} →
  ((n : ℕ) → a n ≡ b n) →
  (left : HasPowerSeriesOnBallWith a ρ μ) →
  (right : HasPowerSeriesOnBallWith b σ ν) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (k-bound : BoundedByᶜ σ h) →
  powerSeriesSumOnBall a ρ μ left h h-bound ≡
  powerSeriesSumOnBall b σ ν right h k-bound
powerSeriesSumOnBall-coefficients-path
  {a = a}
  {b = b}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {ν = ν}
  coeff≡
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
    powerSeriesSumOnBall b σ ν right h k-bound

  leftTail :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace
      leftSum
      (half⁺ ε)
      (powerSeriesPartialSum b h (approximationIndex ε))
  leftTail ε =
    subst
      (λ partial →
        MetricSpace.Close CauchyRealsMetricSpace
          leftSum
          (half⁺ ε)
          partial)
      (powerSeriesPartialSum-cong coeff≡ refl (approximationIndex ε))
      (seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm a h)
        μ
        (HasPowerSeriesOnBallWith.tailBound left h h-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus left)
        (half⁺ ε)
        (approximationIndex ε)
        (NatOrder.left-≤-max
          {m = μ (quarter⁺ (half⁺ (half⁺ ε)))}
          {n = ν (quarter⁺ (half⁺ (half⁺ ε)))}))

  rightTail :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace
      rightSum
      (half⁺ ε)
      (powerSeriesPartialSum b h (approximationIndex ε))
  rightTail ε =
    seriesSumFromFiniteTailBoundConvergesAt
      (powerSeriesTerm b h)
      ν
      (HasPowerSeriesOnBallWith.tailBound right h k-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus right)
      (half⁺ ε)
      (approximationIndex ε)
      (NatOrder.right-≤-max
        {n = ν (quarter⁺ (half⁺ (half⁺ ε)))}
        {m = μ (quarter⁺ (half⁺ (half⁺ ε)))})


powerSeriesSumOnBallFrom-coefficients-path :
  {a b : PowerSeries} →
  {ρ σ : ℚ⁺} →
  ((n : ℕ) → a n ≡ b n) →
  (left : HasPowerSeriesOnBall a ρ) →
  (right : HasPowerSeriesOnBall b σ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (k-bound : BoundedByᶜ σ h) →
  powerSeriesSumOnBallFrom a ρ left h h-bound ≡
  powerSeriesSumOnBallFrom b σ right h k-bound
powerSeriesSumOnBallFrom-coefficients-path
  coeff≡
  (μ , left)
  (ν , right)
  h
  h-bound
  k-bound =
  powerSeriesSumOnBall-coefficients-path
    coeff≡
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
  hasPowerSeriesOnBallWith
    (HasPowerSeriesOnBallWith.antitoneModulus convergence)
    (λ h h-bound →
      subst
        (λ u → TailBound u μ)
        (powerSeriesTerm-cong-coefficients coeff≡ h)
        (HasPowerSeriesOnBallWith.tailBound convergence h h-bound))


hasPowerSeriesOnBall-cong :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  ((n : ℕ) → a n ≡ b n) →
  HasPowerSeriesOnBall a ρ →
  HasPowerSeriesOnBall b ρ
hasPowerSeriesOnBall-cong coeff≡ (μ , convergence) =
  μ , hasPowerSeriesOnBallWith-cong coeff≡ convergence


hasPowerSeriesOnSmallerBallWith :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  radius ρ ℚOrder.< radius σ →
  HasPowerSeriesOnBallWith a σ μ →
  HasPowerSeriesOnBallWith a ρ μ
hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence =
  hasPowerSeriesOnBallWith
    (HasPowerSeriesOnBallWith.antitoneModulus convergence)
    (λ h h-bound →
      HasPowerSeriesOnBallWith.tailBound
        convergence
        h
        (bounded-byᶜ-monotone
          (ℚOrder.<Weaken≤ (radius ρ) (radius σ) ρ<σ)
          h-bound))


HasPowerSeriesRadius :
  PowerSeries →
  ℚ⁺ →
  Type₀
HasPowerSeriesRadius a R =
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< radius R →
  HasPowerSeriesOnBall a ρ
