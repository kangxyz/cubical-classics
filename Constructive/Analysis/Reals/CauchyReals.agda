{-

Constructive Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.CauchyReals where

open import Constructive.Data.PositiveRationals public
open import Constructive.Data.Rationals.Closeness public
open import Constructive.Analysis.Completions.CauchyCompletion.Definitions public
open import Constructive.Analysis.Completions.CauchyCompletion.Induction public
open import Constructive.Analysis.Completions.CauchyCompletion.Recursion public
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness public
open import Constructive.Analysis.Metric.Instances.CauchyReals public
  using (CauchyRealsIsCauchyComplete)
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Base public
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic public
open import Constructive.Analysis.Reals.CauchyReals.Order public
open import Constructive.Analysis.Reals.CauchyReals.Archimedean public

open DefinitionsOf RationalsMetricSpace public
open InductionOf RationalsMetricSpace public
open RecursionOf RationalsMetricSpace public
open ClosenessOf RationalsMetricSpace public
open ComputedOf RationalsMetricSpace public
open RoundedOf RationalsMetricSpace public
