{-

Cauchy completeness of closed intervals of HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Interval.Completeness where

open import Cubical.Foundations.Prelude

open import Constructive.Analysis.Metric.Base
import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Lattice
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.Interval.Base
open import Constructive.Data.PositiveRationals


projectIntervalApproximation :
  {a b : ℝᶜ} →
  MetricCauchy.CauchyApproximation (IntervalMetric a b) →
  MetricCauchy.CauchyApproximation CauchyRealsMetricSpace
projectIntervalApproximation {a = a} {b = b} x =
  MetricCauchy.cauchy-approximation
    (λ ε → pointᶜ {a = a} {b = b} (MetricCauchy.approximate x ε))
    (λ ε δ → MetricCauchy.isRegular x ε δ)


limitLowerBoundClosed :
  {a : ℝᶜ} →
  (x : MetricCauchy.CauchyApproximation CauchyRealsMetricSpace) →
  ((δ : ℚ⁺) → a ≤ᶜ MetricCauchy.approximate x δ) →
  a ≤ᶜ MetricCauchy.limitPoint (CauchyRealsIsCauchyComplete x)
limitLowerBoundClosed {a = a} x lower =
  MetricSpace.close-separated CauchyRealsMetricSpace (a ⊓ᶜ L) a closeAt
  where
  realLimit : MetricCauchy.CauchyLimit x
  realLimit =
    CauchyRealsIsCauchyComplete x

  L : ℝᶜ
  L =
    MetricCauchy.limitPoint realLimit

  closeAt :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace (a ⊓ᶜ L) ε a
  closeAt ε =
    MetricSpace.close-mono CauchyRealsMetricSpace
      (half< ε)
      (subst
        (λ y →
          MetricSpace.Close CauchyRealsMetricSpace (a ⊓ᶜ L) (half⁺ ε) y)
        (lower δ)
        (min-close-right a (MetricCauchy.converges realLimit (half⁺ ε) δ δ<half)))
    where
    δ : ℚ⁺
    δ =
      quarter⁺ ε

    δ<half : δ <⁺ half⁺ ε
    δ<half =
      half< (half⁺ ε)


limitUpperBoundClosed :
  {b : ℝᶜ} →
  (x : MetricCauchy.CauchyApproximation CauchyRealsMetricSpace) →
  ((δ : ℚ⁺) → MetricCauchy.approximate x δ ≤ᶜ b) →
  MetricCauchy.limitPoint (CauchyRealsIsCauchyComplete x) ≤ᶜ b
limitUpperBoundClosed {b = b} x upper =
  MetricSpace.close-separated CauchyRealsMetricSpace (L ⊓ᶜ b) L closeAt
  where
  realLimit : MetricCauchy.CauchyLimit x
  realLimit =
    CauchyRealsIsCauchyComplete x

  L : ℝᶜ
  L =
    MetricCauchy.limitPoint realLimit

  closeAt :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace (L ⊓ᶜ b) ε L
  closeAt ε =
    subst
      (λ ρ → MetricSpace.Close CauchyRealsMetricSpace (L ⊓ᶜ b) ρ L)
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle CauchyRealsMetricSpace leftClose rightClose)
    where
    α : ℚ⁺
    α =
      half⁺ ε

    δ : ℚ⁺
    δ =
      quarter⁺ ε

    δ<α : δ <⁺ α
    δ<α =
      half< α

    L∼xδ :
      MetricSpace.Close
        CauchyRealsMetricSpace
        L
        α
        (MetricCauchy.approximate x δ)
    L∼xδ =
      MetricCauchy.converges realLimit α δ δ<α

    leftClose :
      MetricSpace.Close
        CauchyRealsMetricSpace
        (L ⊓ᶜ b)
        α
        (MetricCauchy.approximate x δ)
    leftClose =
      subst
        (λ y → MetricSpace.Close CauchyRealsMetricSpace (L ⊓ᶜ b) α y)
        (upper δ)
        (min-close-left L∼xδ b)

    rightClose :
      MetricSpace.Close
        CauchyRealsMetricSpace
        (MetricCauchy.approximate x δ)
        α
        L
    rightClose =
      MetricSpace.close-sym CauchyRealsMetricSpace L∼xδ


intervalComplete :
  {a b : ℝᶜ} →
  a ≤ᶜ b →
  MetricCauchy.IsCauchyComplete (IntervalMetric a b)
intervalComplete {a = a} {b = b} _ x =
  MetricCauchy.cauchy-limit limitInterval limitConverges
  where
  realApproximation :
    MetricCauchy.CauchyApproximation CauchyRealsMetricSpace
  realApproximation =
    projectIntervalApproximation x

  realLimit : MetricCauchy.CauchyLimit realApproximation
  realLimit =
    CauchyRealsIsCauchyComplete realApproximation

  L : ℝᶜ
  L =
    MetricCauchy.limitPoint realLimit

  lowerAt :
    (δ : ℚ⁺) →
    a ≤ᶜ MetricCauchy.approximate realApproximation δ
  lowerAt δ =
    lowerBoundᶜ {a = a} {b = b} (MetricCauchy.approximate x δ)

  upperAt :
    (δ : ℚ⁺) →
    MetricCauchy.approximate realApproximation δ ≤ᶜ b
  upperAt δ =
    upperBoundᶜ {a = a} {b = b} (MetricCauchy.approximate x δ)

  limitInterval : [ a , b ]ᶜ
  limitInterval =
    L ,
    limitLowerBoundClosed {a = a} realApproximation lowerAt ,
    limitUpperBoundClosed {b = b} realApproximation upperAt

  limitConverges :
    MetricCauchy.ConvergesTo x limitInterval
  limitConverges ε δ δ<ε =
    MetricCauchy.converges realLimit ε δ δ<ε
