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
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.Interval.Base
open import Constructive.Analysis.Reals.Locator
open import Constructive.Data.PositiveRationals

open ClosenessOf RationalsMetricSpace


isUniformlyContinuousOnInterval :
  (a b : ℝᶜ) →
  ([ a , b ]ᶜ → ℝᶜ) →
  Type₀
isUniformlyContinuousOnInterval a b f =
  IsUniformlyContinuous (IntervalMetric a b) CauchyRealsMetricSpace f


uniformModulus :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
  isUniformlyContinuousOnInterval a b f →
  PrecisionModulus
uniformModulus (μ , _) =
  μ


uniformClose :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
  (uc : isUniformlyContinuousOnInterval a b f) →
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


IVTFunctionData :
  (a b : ℝᶜ) →
  ([ a , b ]ᶜ → ℝᶜ) →
  Type₀
IVTFunctionData a b f =
  Σ[ approxEvaluable ∈ ApproxEvaluable f ]
    isUniformlyContinuousOnInterval a b f


module IVTFunctionData where
  approxEvaluable :
    {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
    IVTFunctionData a b f →
    ApproxEvaluable f
  approxEvaluable ivtData =
    ivtData .fst

  uniformlyContinuous :
    {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
    IVTFunctionData a b f →
    isUniformlyContinuousOnInterval a b f
  uniformlyContinuous ivtData =
    ivtData .snd


locatedIVTFunctionData :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
  LocatedMap f →
  isUniformlyContinuousOnInterval a b f →
  IVTFunctionData a b f
locatedIVTFunctionData located uc =
  locatedMap→ApproxEvaluable located , uc


approximateValue :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
  IVTFunctionData a b f →
  (x : [ a , b ]ᶜ) →
  (ε : ℚ⁺) →
  Σ[ q ∈ ℚ ] f x ∼[ ε ] rational q
approximateValue {a = a} {b = b} {f = f} ivtData =
  IVTFunctionData.approxEvaluable {a = a} {b = b} {f = f} ivtData
