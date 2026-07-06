{-

The Cauchy-real metric space

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Metric.Instances.CauchyReals where

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Cauchy
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Completions.CauchyCompletion.Completeness
open import Constructive.Analysis.Completions.CauchyCompletion.MetricSpace


CauchyRealsMetricSpace : MetricSpace _ _
CauchyRealsMetricSpace =
  MetricSpaceOf.CauchyCompletionMetricSpace RationalsMetricSpace


CauchyRealsIsCauchyComplete : IsCauchyComplete CauchyRealsMetricSpace
CauchyRealsIsCauchyComplete =
  CompletenessOf.isCauchyComplete RationalsMetricSpace
