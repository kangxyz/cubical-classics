{-

The Cauchy-real metric space

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Metric.Instances.CauchyReals where

open import Constructive.Analysis.CauchyCompletion.Complete
open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Instances.Rationals


CauchyRealsMetricSpace : MetricSpace _ _
CauchyRealsMetricSpace =
  CompleteOf.CauchyCompletionMetricSpace RationalsMetricSpace
