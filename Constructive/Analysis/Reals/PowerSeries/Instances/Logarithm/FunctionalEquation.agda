{-

Logarithm functional equations

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation where

open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.Core
  public
  using (logOnePlusᶜWithinSubunitBall-global)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.LogOnePlusDerivative
  public
  using (logOnePlusᶜWithinSubunitBallHasDerivativeWithinDomainAtWith)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.LogOnePlusGlobal
  public
  using (logOnePlusᶜWithinSubunitBall-global-eq)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.GlobalDerivative
  public
  using
    ( PositiveWindowᶜ
    ; logᶜ-positive-window
    ; logᶜ-positive-windowHasDerivativeWithinDomainAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.LocalAdd
  public
  using (logᶜ-positive-bounded-add-local)
