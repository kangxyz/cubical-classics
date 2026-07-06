{-

Cauchy completeness for precision-indexed Cauchy approximations

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Completeness where

open import Cubical.Foundations.Prelude

import Constructive.Analysis.Metric.Complete as MetricComplete
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.CauchyReals.Base

private
  variable
    ℓ : Level


record CauchyStructure (A : Type ℓ) : Type (ℓ-suc ℓ) where
  no-eta-equality
  field
    Close : A → ℚ⁺ → A → Type ℓ


record CauchyApproximationIn
  (A : Type ℓ) {{S : CauchyStructure A}} : Type ℓ where
  constructor cauchy-approximation-in
  field
    approximate : ℚ⁺ → A
    isRegular :
      (ε δ : ℚ⁺) →
      CauchyStructure.Close S (approximate ε) (ε +⁺ δ) (approximate δ)


record CauchyLimitIn
  {A : Type ℓ} {{S : CauchyStructure A}}
  (x : CauchyApproximationIn A) : Type ℓ where
  constructor cauchy-limit-in
  field
    limitPoint : A
    converges :
      (ε δ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      CauchyStructure.Close S
        limitPoint
        ε
        (CauchyApproximationIn.approximate x δ)


isCauchyComplete :
  (A : Type ℓ) →
  {{S : CauchyStructure A}} →
  Type ℓ
isCauchyComplete A {{S}} =
  (x : CauchyApproximationIn A) → CauchyLimitIn x


isCauchyCompleteWith :
  (A : Type ℓ) →
  CauchyStructure A →
  Type ℓ
isCauchyCompleteWith A S =
  (x : CauchyApproximationIn A {{S}}) → CauchyLimitIn {{S}} x


instance
  CauchyRealsCauchyStructure : CauchyStructure CauchyReals
  CauchyRealsCauchyStructure .CauchyStructure.Close x ε y =
    x ∼[ ε ] y


toMetricCauchyApproximationᶜ :
  CauchyApproximationIn CauchyReals →
  MetricComplete.CauchyApproximation CauchyRealsMetricSpace
toMetricCauchyApproximationᶜ x =
  MetricComplete.cauchy-approximation
    (CauchyApproximationIn.approximate x)
    (CauchyApproximationIn.isRegular x)


isCauchyComplete-CauchyReals :
  isCauchyComplete CauchyReals
isCauchyComplete-CauchyReals x =
  cauchy-limit-in
    (MetricComplete.limitPoint metricLimit)
    (MetricComplete.converges metricLimit)
  where
  metricApproximation :
    MetricComplete.CauchyApproximation CauchyRealsMetricSpace
  metricApproximation =
    toMetricCauchyApproximationᶜ x

  metricLimit : MetricComplete.CauchyLimit metricApproximation
  metricLimit =
    MetricComplete.CauchyRealsIsComplete metricApproximation


CauchyRealsIsCauchyComplete :
  isCauchyComplete CauchyReals
CauchyRealsIsCauchyComplete =
  isCauchyComplete-CauchyReals
