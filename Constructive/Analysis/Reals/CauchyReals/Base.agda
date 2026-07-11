{-

HoTT-style Cauchy reals

The Cauchy reals are the Cauchy completion of the rational metric space.

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.CauchyReals.Base where

open import Cubical.Foundations.Prelude

import Constructive.Analysis.Completions.CauchyCompletion.Base as Completion
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Data.PositiveRationals public
open import Constructive.Data.Rationals.Closeness public


open Completion.CompletionOf RationalsMetricSpace
  renaming
    ( Completion to ℝᶜ
    ; point to rational
    )
  public
