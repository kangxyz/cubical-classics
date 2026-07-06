{-

Uniform-continuity data for interval IVT arguments

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.IVT.Uniform where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Sigma using (Σ-syntax)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.Interval
open import Constructive.Analysis.Reals.Locator.Map
open import Constructive.Data.PositiveRationals

open ClosenessOf RationalsMetricSpace


UniformlyContinuousOnInterval :
  (a b : ℝᶜ) →
  ([ a , b ]ᶜ → ℝᶜ) →
  Type₀
UniformlyContinuousOnInterval a b f =
  IsUniformlyContinuous (IntervalMetric a b) CauchyRealsMetricSpace f


uniformModulus :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
  UniformlyContinuousOnInterval a b f →
  PrecisionModulus
uniformModulus (μ , _) =
  μ


uniformClose :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
  (uc : UniformlyContinuousOnInterval a b f) →
  (ε : ℚ⁺) →
  {x y : [ a , b ]ᶜ} →
  MetricSpace.Close
    (IntervalMetric a b)
    x
    (uniformModulus {a = a} {b = b} {f = f} uc ε)
    y →
  MetricSpace.Close CauchyRealsMetricSpace (f x) ε (f y)
uniformClose (μ , f-cont) ε =
  f-cont ε


record IVTFunctionData
    (a b : ℝᶜ)
    (f : [ a , b ]ᶜ → ℝᶜ) :
    Type₀ where
  no-eta-equality

  field
    approxEvaluable : ApproxEvaluable f
    uniformlyContinuous : UniformlyContinuousOnInterval a b f


locatedIVTFunctionData :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
  LocatedMap f →
  UniformlyContinuousOnInterval a b f →
  IVTFunctionData a b f
locatedIVTFunctionData located uc .IVTFunctionData.approxEvaluable =
  locatedMap→ApproxEvaluable located
locatedIVTFunctionData located uc .IVTFunctionData.uniformlyContinuous =
  uc


approximateValue :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
  IVTFunctionData a b f →
  (x : [ a , b ]ᶜ) →
  (ε : ℚ⁺) →
  Σ[ q ∈ ℚ ] f x ∼[ ε ] rational q
approximateValue ivtData =
  IVTFunctionData.approxEvaluable ivtData
