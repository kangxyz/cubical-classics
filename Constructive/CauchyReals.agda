{-

Constructive Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals where

open import Constructive.Data.PositiveRationals public
open import Constructive.Data.Rationals.Closeness public
open import Constructive.Analysis.CauchyCompletion.Definitions public
open import Constructive.Analysis.CauchyCompletion.Induction public
open import Constructive.Analysis.CauchyCompletion.Recursion public
open import Constructive.Analysis.CauchyCompletion.Closeness public
open import Constructive.Analysis.Metric.Instances.CauchyReals public
  using (CauchyRealsIsCauchyComplete)
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.CauchyReals.Base public
open import Constructive.CauchyReals.Arithmetic public
open import Constructive.CauchyReals.Order public

open DefinitionsOf RationalsMetricSpace public
open InductionOf RationalsMetricSpace public
open RecursionOf RationalsMetricSpace public
open ClosenessOf RationalsMetricSpace public
open ComputedOf RationalsMetricSpace public
open RoundedOf RationalsMetricSpace public
