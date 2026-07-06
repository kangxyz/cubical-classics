{-

The rational metric space

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Metric.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals using (ℚ ; isSetℚ)

open import Constructive.Analysis.Metric.Base
open import Constructive.Data.Rationals.Closeness


RationalsMetricSpace : MetricSpace ℓ-zero ℓ-zero
RationalsMetricSpace .MetricSpace.Carrier =
  ℚ
RationalsMetricSpace .MetricSpace.isSetCarrier =
  isSetℚ
RationalsMetricSpace .MetricSpace.Close q ε r =
  Closeℚ q ε r
RationalsMetricSpace .MetricSpace.isPropClose q r ε =
  isPropCloseℚ q ε r
RationalsMetricSpace .MetricSpace.close-refl =
  rational-close-refl
RationalsMetricSpace .MetricSpace.close-sym {x = q} {y = r} {ε = ε} =
  rational-close-sym q r ε
RationalsMetricSpace .MetricSpace.close-mono {x = q} {y = r} {ε = ε} {δ = δ} =
  rational-close-mono q r ε δ
RationalsMetricSpace .MetricSpace.close-triangle
  {x = q} {y = r} {z = s} {ε = ε} {δ = δ} =
  rational-close-triangle q r s ε δ
RationalsMetricSpace .MetricSpace.close-rounded {x = q} {y = r} {ε = ε} =
  rational-close-rounded q r ε
RationalsMetricSpace .MetricSpace.close-separated =
  rational-close-separated
