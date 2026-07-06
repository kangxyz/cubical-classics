{-

Cauchy completeness for precision-indexed metric spaces

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Metric.Complete where

open import Cubical.Foundations.Prelude

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Cauchy public
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.CauchyCompletion.Complete


CauchyRealsIsComplete : IsComplete CauchyRealsMetricSpace
CauchyRealsIsComplete =
  CompleteOf.isComplete RationalsMetricSpace
