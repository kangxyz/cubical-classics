{-

Basic symmetry facts for the Cauchy-real closeness relation

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Closeness.ReflexiveSymmetric where

open import Cubical.Foundations.Prelude

open import Constructive.Analysis.CauchyCompletion.Closeness.ReflexiveSymmetric
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.CauchyReals.Base

open ClosenessOf RationalsMetricSpace public


isSetℝᶜ : isSet ℝᶜ
isSetℝᶜ =
  isSetCompletion
