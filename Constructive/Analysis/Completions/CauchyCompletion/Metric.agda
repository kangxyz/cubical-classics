{-

Metric-space structure on Cauchy completions

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Completions.CauchyCompletion.Metric where

open import Cubical.Foundations.Prelude

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Completions.CauchyCompletion.Base
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness.ReflexiveSymmetric
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness.Computed
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness.Rounded
open import Constructive.Data.PositiveRationals

private
  variable
    ℓ ℓ' : Level


module MetricSpaceOf (𝓜 : MetricSpace ℓ ℓ') where
  open CompletionOf 𝓜
  open ClosenessOf 𝓜
  open ComputedOf 𝓜
    using (close→computed ; close-triangle)
  open RoundedOf 𝓜

  CauchyCompletionMetricSpace : MetricSpace (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  CauchyCompletionMetricSpace .MetricSpace.Carrier =
    Completion
  CauchyCompletionMetricSpace .MetricSpace.isSetCarrier =
    isSetCompletion
  CauchyCompletionMetricSpace .MetricSpace.Close x ε y =
    x ∼[ ε ] y
  CauchyCompletionMetricSpace .MetricSpace.isPropClose x y ε =
    squash
  CauchyCompletionMetricSpace .MetricSpace.close-refl =
    close-refl
  CauchyCompletionMetricSpace .MetricSpace.close-sym =
    close-sym
  CauchyCompletionMetricSpace .MetricSpace.close-mono =
    close-mono
  CauchyCompletionMetricSpace .MetricSpace.close-triangle =
    close-triangle
  CauchyCompletionMetricSpace .MetricSpace.close-rounded =
    close-rounded
  CauchyCompletionMetricSpace .MetricSpace.close-separated =
    path


  pointNonexpanding :
    IsNonexpanding 𝓜 CauchyCompletionMetricSpace point
  pointNonexpanding {x = a} {y = b} {ε = ε} =
    point-point-close a b ε


  pointReflecting :
    {a b : MetricSpace.Carrier 𝓜} {ε : ℚ⁺} →
    point a ∼[ ε ] point b →
    MetricSpace.Close 𝓜 a ε b
  pointReflecting =
    close→computed
