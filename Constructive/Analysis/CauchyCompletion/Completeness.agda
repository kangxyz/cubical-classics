{-

Cauchy completeness of Cauchy completions

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.CauchyCompletion.Completeness where

open import Cubical.Foundations.Prelude

import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.CauchyCompletion.Base
open import Constructive.Analysis.CauchyCompletion.Closeness.ReflexiveSymmetric
open import Constructive.Analysis.CauchyCompletion.Extension.Unary
open import Constructive.Analysis.CauchyCompletion.MetricSpace
open import Constructive.Data.PositiveRationals

private
  variable
    ℓ ℓ' : Level


module CompletenessOf (𝓜 : MetricSpace ℓ ℓ') where
  open CompletionOf 𝓜
  open ClosenessOf 𝓜
    using (close-refl)
  open ExtensionOf 𝓜
    using (limit-close-intro)
  open MetricSpaceOf 𝓜

  toCauchyApproximation :
    MetricCauchy.CauchyApproximation CauchyCompletionMetricSpace →
    CauchyApproximation
  toCauchyApproximation x =
    cauchy-approximation
      (MetricCauchy.CauchyApproximation.approximate x)
      (MetricCauchy.CauchyApproximation.isRegular x)


  isCauchyComplete :
    MetricCauchy.IsCauchyComplete CauchyCompletionMetricSpace
  isCauchyComplete x =
    MetricCauchy.cauchy-limit
      (limit xᶜ)
      λ ε δ δ<ε →
        limit-close-intro xᶜ (MetricCauchy.CauchyApproximation.approximate x δ)
          ε δ δ<ε
          (close-refl
            (MetricCauchy.CauchyApproximation.approximate x δ)
            (ε ⊖ δ [ δ<ε ]))
    where
    xᶜ : CauchyApproximation
    xᶜ =
      toCauchyApproximation x
