{-

Induction interfaces for Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Induction where

open import Constructive.Analysis.CauchyCompletion.Induction
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.CauchyReals.Definitions public

open InductionOf RationalsMetricSpace public
