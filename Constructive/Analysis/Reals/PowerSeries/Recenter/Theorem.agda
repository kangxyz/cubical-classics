{-

Theorem-level re-centering results.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.Theorem where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Metric.Base
  using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
  using (_+ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
  using (0ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using (_·ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using
    ( BoundedByᶜ
    ; bounded-byᶜ-close-zero
    ; bounded-byᶜ-monotone
    )
open import Constructive.Analysis.Reals.Series
  using (diff-close-zero→close ; seriesSumFromFiniteTailBoundConvergesAt)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Bounds
  using (positiveRationalSelfBounded)
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using (PowerSeriesMajorizedOnBall ; majorizedOnBall→hasPowerSeriesOnBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using
    ( HasPowerSeriesOnBall
    ; HasPowerSeriesOnBallWith
    ; hasPowerSeriesOnBallWith
    ; powerSeriesSumOnBall
    )
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Base
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Binomial
  using (triangularRowsSumᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.CoefficientConvergence
  using (recenterPowerSeriesDataFromMajorizedOnStrictSubballδ<σ)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.FiniteIdentity
  using (powerSeriesPartialSum-recenterTriangle-shifted)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.PrefixLimit
  using (recenterPrefixTriangleDifferenceBoundFromMajorizedOnStrictSubballLimit)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.StrictSubball
  using (recenterStrictSubballModulus ; recenterShiftedDisplacementBound)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.StripFinite
  using (recenterOuterTailApproxBoundFromMajorizedOnStrictSubball)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.StripTail
  using (recenterTailBoundFromOuterApproxBounds)
open import Constructive.Data.PositiveRationals
  using
    ( ℚ⁺
    ; radius
    ; _<⁺_
    ; <⁺-trans
    ; _+⁺_
    ; half⁺
    ; half<
    ; quarter⁺
    ; quarter<
    ; summand-left<sum
    ; three-quarter<
    )


private
  strict-left-margin :
    (δ τ σ : ℚ⁺) →
    radius (δ +⁺ τ) ℚOrder.< radius σ →
    radius δ ℚOrder.< radius σ
  strict-left-margin δ τ σ margin =
    ℚOrder.isTrans<
      (radius δ)
      (radius (δ +⁺ τ))
      (radius σ)
      (summand-left<sum δ τ)
      margin


recenterPowerSeriesDataFromMajorizedOnStrictSubball :
  {a : PowerSeries} →
  {δ τ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  {d : ℝᶜ} →
  BoundedByᶜ δ d →
  radius (δ +⁺ τ) ℚOrder.< radius σ →
  PowerSeriesMajorizedOnBall a σ v ν →
  RecenterPowerSeriesData a d
recenterPowerSeriesDataFromMajorizedOnStrictSubball
    {a = a}
    {δ = δ}
    {τ = τ}
    {σ = σ}
    {v = v}
    {ν = ν}
    {d = d}
    d-bound
    margin
    majorized =
  recenterPowerSeriesDataFromMajorizedOnStrictSubballδ<σ
    {a = a}
    {δ = δ}
    {σ = σ}
    {v = v}
    {ν = ν}
    d
    d-bound
    (strict-left-margin δ τ σ margin)
    majorized


recenterPowerSeriesOnStrictSubballFromMajorizedOnBall :
  {a : PowerSeries} →
  {δ τ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  {d : ℝᶜ} →
  (d-bound : BoundedByᶜ δ d) →
  (margin : radius (δ +⁺ τ) ℚOrder.< radius σ) →
  (majorized : PowerSeriesMajorizedOnBall a σ v ν) →
  HasPowerSeriesOnBallWith
    (recenterPowerSeriesWith a d
      (recenterPowerSeriesDataFromMajorizedOnStrictSubball
        d-bound
        margin
        majorized))
    τ
    (recenterStrictSubballModulus δ τ σ ν)
recenterPowerSeriesOnStrictSubballFromMajorizedOnBall
    {a = a}
    {δ = δ}
    {τ = τ}
    {σ = σ}
    {v = v}
    {ν = ν}
    {d = d}
    d-bound
    margin
    majorized =
  hasPowerSeriesOnBallWith
    {a = recenterPowerSeriesWith a d recenterData}
    {ρ = τ}
    {μ = recenterStrictSubballModulus δ τ σ ν}
    (PowerSeriesMajorizedOnBall.majorAntitone
      {a = a}
      {ρ = σ}
      {v = v}
      {μ = ν}
      majorized)
    (λ (h : ℝᶜ) (h-bound : BoundedByᶜ τ h) →
      recenterTailBoundFromOuterApproxBounds
        recenterData
        h-bound
        (λ ε m k N ν≤m →
          recenterOuterTailApproxBoundFromMajorizedOnStrictSubball
            d-bound
            h-bound
            probe-bound
            majorized
            ε
            m
            k
            N
            ν≤m))
  where
  recenterData : RecenterPowerSeriesData a d
  recenterData =
    recenterPowerSeriesDataFromMajorizedOnStrictSubball
      d-bound
      margin
      majorized

  probe-bound : BoundedByᶜ σ (rational (radius (δ +⁺ τ)))
  probe-bound =
    bounded-byᶜ-monotone
      (ℚOrder.<Weaken≤ (radius (δ +⁺ τ)) (radius σ) margin)
      (positiveRationalSelfBounded (δ +⁺ τ))


centeredPowerSeriesSumRecenteredOnStrictSubball :
  {a : PowerSeries} →
  {δ τ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  {d h : ℝᶜ} →
  (d-bound : BoundedByᶜ δ d) →
  (h-bound : BoundedByᶜ τ h) →
  (margin : radius (δ +⁺ τ) ℚOrder.< radius σ) →
  (majorized : PowerSeriesMajorizedOnBall a σ v ν) →
  powerSeriesSumOnBall
    a
    σ
    ν
    (majorizedOnBall→hasPowerSeriesOnBallWith majorized)
    (d +ᶜ h)
    (recenterShiftedDisplacementBound d-bound h-bound margin)
  ≡
  powerSeriesSumOnBall
    (recenterPowerSeriesWith a d
      (recenterPowerSeriesDataFromMajorizedOnStrictSubball
        d-bound
        margin
        majorized))
    τ
    (recenterStrictSubballModulus δ τ σ ν)
    (recenterPowerSeriesOnStrictSubballFromMajorizedOnBall
      d-bound
      margin
      majorized)
    h
    h-bound
centeredPowerSeriesSumRecenteredOnStrictSubball
    {a = a}
    {δ = δ}
    {τ = τ}
    {σ = σ}
    {v = v}
    {ν = ν}
    {d = d}
    {h = h}
    d-bound
    h-bound
    margin
    majorized =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    oldSum
    newSum
    closeAt
  where
  recenterData : RecenterPowerSeriesData a d
  recenterData =
    recenterPowerSeriesDataFromMajorizedOnStrictSubball
      d-bound
      margin
      majorized

  oldConvergence : HasPowerSeriesOnBallWith a σ ν
  oldConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith majorized

  newConvergence :
    HasPowerSeriesOnBallWith
      (recenterPowerSeriesWith a d recenterData)
      τ
      (recenterStrictSubballModulus δ τ σ ν)
  newConvergence =
    recenterPowerSeriesOnStrictSubballFromMajorizedOnBall
      d-bound
      margin
      majorized

  shifted-bound : BoundedByᶜ σ (d +ᶜ h)
  shifted-bound =
    recenterShiftedDisplacementBound d-bound h-bound margin

  probe-bound : BoundedByᶜ σ (rational (radius (δ +⁺ τ)))
  probe-bound =
    bounded-byᶜ-monotone
      (ℚOrder.<Weaken≤ (radius (δ +⁺ τ)) (radius σ) margin)
      (positiveRationalSelfBounded (δ +⁺ τ))

  oldSum : ℝᶜ
  oldSum =
    powerSeriesSumOnBall
      a
      σ
      ν
      oldConvergence
      (d +ᶜ h)
      shifted-bound

  newSum : ℝᶜ
  newSum =
    powerSeriesSumOnBall
      (recenterPowerSeriesWith a d recenterData)
      τ
      (recenterStrictSubballModulus δ τ σ ν)
      newConvergence
      h
      h-bound

  closeAt :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace oldSum ε newSum
  closeAt ε =
    MetricSpace.close-mono
      CauchyRealsMetricSpace
      (three-quarter< ε)
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        (MetricSpace.close-triangle
          CauchyRealsMetricSpace
          old-to-triangle
          triangle-to-new-partial)
        new-partial-to-sum)
    where
    α : ℚ⁺
    α =
      quarter⁺ ε

    β : ℚ⁺
    β =
      quarter⁺ (half⁺ α)

    N : ℕ
    N =
      ν β

    νβ≤N : NatOrder._≤_ (ν β) N
    νβ≤N =
      NatOrder.≤-refl

    β<α : β <⁺ α
    β<α =
      <⁺-trans
        {ε = β}
        {δ = half⁺ α}
        {η = α}
        (quarter< (half⁺ α))
        (half< α)

    triangle : ℝᶜ
    triangle =
      triangularRowsSumᶜ
        (λ n k →
          recenterCoefficientTerm a d n k ·ᶜ
          realPower h n)
        N

    recenteredPartial : ℝᶜ
    recenteredPartial =
      powerSeriesPartialSum
        (recenterPowerSeriesWith a d recenterData)
        h
        N

    old-to-partial :
      MetricSpace.Close CauchyRealsMetricSpace
        oldSum
        α
        (powerSeriesPartialSum a (d +ᶜ h) N)
    old-to-partial =
      seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm a (d +ᶜ h))
        ν
        (HasPowerSeriesOnBallWith.tailBound
          oldConvergence
          (d +ᶜ h)
          shifted-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus oldConvergence)
        α
        N
        νβ≤N

    old-to-triangle :
      MetricSpace.Close CauchyRealsMetricSpace
        oldSum
        α
        triangle
    old-to-triangle =
      subst
        (λ x →
          MetricSpace.Close CauchyRealsMetricSpace
            oldSum
            α
            x)
        (powerSeriesPartialSum-recenterTriangle-shifted a d h N)
        old-to-partial

    prefix-close :
      MetricSpace.Close CauchyRealsMetricSpace
        recenteredPartial
        α
        triangle
    prefix-close =
      diff-close-zero→close
        (bounded-byᶜ-close-zero
          β
          α
          (recenteredPartial +ᶜ (-ᶜ triangle))
          (recenterPrefixTriangleDifferenceBoundFromMajorizedOnStrictSubballLimit
            recenterData
            d-bound
            h-bound
            probe-bound
            majorized
            β
            N
            νβ≤N)
          β<α)

    triangle-to-new-partial :
      MetricSpace.Close CauchyRealsMetricSpace
        triangle
        α
        recenteredPartial
    triangle-to-new-partial =
      MetricSpace.close-sym CauchyRealsMetricSpace prefix-close

    new-tail :
      MetricSpace.Close CauchyRealsMetricSpace
        newSum
        α
        recenteredPartial
    new-tail =
      seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm (recenterPowerSeriesWith a d recenterData) h)
        (recenterStrictSubballModulus δ τ σ ν)
        (HasPowerSeriesOnBallWith.tailBound
          newConvergence
          h
          h-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus newConvergence)
        α
        N
        νβ≤N

    new-partial-to-sum :
      MetricSpace.Close CauchyRealsMetricSpace
        recenteredPartial
        α
        newSum
    new-partial-to-sum =
      MetricSpace.close-sym CauchyRealsMetricSpace new-tail


recenterPowerSeriesAtZeroOnBallWith :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a ρ μ →
  HasPowerSeriesOnBallWith
    (recenterPowerSeriesWith a 0ᶜ (recenterPowerSeriesDataAtZero a))
    ρ
    μ
recenterPowerSeriesAtZeroOnBallWith {a = a} {ρ = ρ} {μ = μ} convergence =
  subst
    (λ b → HasPowerSeriesOnBallWith b ρ μ)
    (sym (recenterPowerSeriesWithAtZero-path a))
    convergence


recenterPowerSeriesAtZeroOnBall :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall a ρ →
  HasPowerSeriesOnBall
    (recenterPowerSeriesWith a 0ᶜ (recenterPowerSeriesDataAtZero a))
    ρ
recenterPowerSeriesAtZeroOnBall {a = a} {ρ = ρ} (μ , convergence) =
  μ , recenterPowerSeriesAtZeroOnBallWith {a = a} {ρ = ρ} {μ = μ} convergence
