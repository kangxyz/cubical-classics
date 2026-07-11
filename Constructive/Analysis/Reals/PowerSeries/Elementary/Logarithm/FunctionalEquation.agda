{-

Logarithm functional equations

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation where

open import Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation.Algebra
  public
  using (logOnePlusᶜWithinSubunitBall-global)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation.LogOnePlusDerivative
  public
  using (logOnePlusᶜWithinSubunitBallHasDerivativeWithinDomainAtWith)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation.LogOnePlusGlobal
  public
  using (logOnePlusᶜWithinSubunitBall-global-eq)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation.GlobalDerivative
  public
  using
    ( PositiveWindowᶜ
    ; logᶜ-positive-window
    ; logᶜ-data-independent
    ; logᶜ-positive-windowHasDerivativeWithinDomainAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation.LocalAdd
  public
  using (logᶜ-add-local)
