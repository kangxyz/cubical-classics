{-

Derivative convergence on strict subballs from naked ball convergence.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.StrictSubball.OnBall where

open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.StrictSubball.OnBall.Base
  public
  using
    ( derivativeStrictSubballFromOnBallModulus
    )
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.StrictSubball.OnBall.Tail
  public
  using
    ( derivativePowerSeriesOnStrictSubballWith
    ; derivativePowerSeriesOnStrictSubball
    )
