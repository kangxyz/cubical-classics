{-

Maps of Cauchy-real sequences

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Sequences.Map where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.Sequences.Base
open import Constructive.Analysis.Reals.Sequences.Cauchy
open import Constructive.Analysis.Reals.Sequences.Convergence

open ClosenessOf RationalsMetricSpace


mapSequence :
  (ℝᶜ → ℝᶜ) →
  Sequence →
  Sequence
mapSequence f u n =
  f (u n)


mapSequence-id :
  (u : Sequence) →
  mapSequence (λ x → x) u ≡ u
mapSequence-id u =
  refl


mapSequence-comp :
  (f g : ℝᶜ → ℝᶜ) →
  (u : Sequence) →
  mapSequence f (mapSequence g u) ≡
  mapSequence (λ x → f (g x)) u
mapSequence-comp f g u =
  refl


mapConstantSequence :
  (f : ℝᶜ → ℝᶜ) →
  (x : ℝᶜ) →
  mapSequence f (constantSequence x) ≡ constantSequence (f x)
mapConstantSequence f x =
  refl


mapUniformlyContinuousWithConverges :
  {f : ℝᶜ → ℝᶜ} →
  {u : Sequence} →
  {x : ℝᶜ} →
  {μf : PrecisionModulus} →
  {μu : NatModulus} →
  IsUniformlyContinuousWith
    CauchyRealsMetricSpace
    CauchyRealsMetricSpace
    μf
    f →
  ConvergesWithModulus u x μu →
  ConvergesWithModulus (mapSequence f u) (f x) (λ ε → μu (μf ε))
mapUniformlyContinuousWithConverges {μf = μf} f-cont u→x ε n μ≤n =
  f-cont ε (u→x (μf ε) n μ≤n)


mapUniformlyContinuousConverges :
  {f : ℝᶜ → ℝᶜ} →
  {u : Sequence} →
  {x : ℝᶜ} →
  {μu : NatModulus} →
  IsUniformlyContinuous
    CauchyRealsMetricSpace
    CauchyRealsMetricSpace
    f →
  ConvergesWithModulus u x μu →
  ConvergesTo (mapSequence f u) (f x)
mapUniformlyContinuousConverges {μu = μu} (μf , f-cont) u→x =
  (λ ε → μu (μf ε)) ,
  mapUniformlyContinuousWithConverges
    {μf = μf}
    {μu = μu}
    f-cont
    u→x


mapUniformlyContinuousWithCauchy :
  {f : ℝᶜ → ℝᶜ} →
  {u : Sequence} →
  {μf : PrecisionModulus} →
  {μu : NatModulus} →
  IsUniformlyContinuousWith
    CauchyRealsMetricSpace
    CauchyRealsMetricSpace
    μf
    f →
  CauchyWithModulus u μu →
  CauchyWithModulus (mapSequence f u) (λ ε → μu (μf ε))
mapUniformlyContinuousWithCauchy {μf = μf} f-cont u-cauchy ε m n μ≤m μ≤n =
  f-cont ε (u-cauchy (μf ε) m n μ≤m μ≤n)


mapUniformlyContinuousCauchy :
  {f : ℝᶜ → ℝᶜ} →
  {u : Sequence} →
  {μu : NatModulus} →
  IsUniformlyContinuous
    CauchyRealsMetricSpace
    CauchyRealsMetricSpace
    f →
  CauchyWithModulus u μu →
  Σ[ μ ∈ NatModulus ] CauchyWithModulus (mapSequence f u) μ
mapUniformlyContinuousCauchy {μu = μu} (μf , f-cont) u-cauchy =
  (λ ε → μu (μf ε)) ,
  mapUniformlyContinuousWithCauchy
    {μf = μf}
    {μu = μu}
    f-cont
    u-cauchy


mapNonexpandingConverges :
  {f : ℝᶜ → ℝᶜ} →
  {u : Sequence} →
  {x : ℝᶜ} →
  {μ : NatModulus} →
  IsNonexpanding CauchyRealsMetricSpace CauchyRealsMetricSpace f →
  ConvergesWithModulus u x μ →
  ConvergesWithModulus (mapSequence f u) (f x) μ
mapNonexpandingConverges f-ne u→x ε n μ≤n =
  f-ne (u→x ε n μ≤n)


mapNonexpandingCauchy :
  {f : ℝᶜ → ℝᶜ} →
  {u : Sequence} →
  {μ : NatModulus} →
  IsNonexpanding CauchyRealsMetricSpace CauchyRealsMetricSpace f →
  CauchyWithModulus u μ →
  CauchyWithModulus (mapSequence f u) μ
mapNonexpandingCauchy f-ne u-cauchy ε m n μ≤m μ≤n =
  f-ne (u-cauchy ε m n μ≤m μ≤n)
