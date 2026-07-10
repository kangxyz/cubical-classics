{-

Reusable estimates for derivative-convergence consumers

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.Estimates where

open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.Internal public
  using
    ( absᶜ-mul≤product
    ; absᶜ-rational-nonnegative
    ; absᶜ-scalarMul≤
    ; derivativeStrictSubballCoefficient≤Scale
    ; derivativeStrictSubballModulus
    ; derivativeStrictSubballRatio
    ; derivativeStrictSubballRatio<1
    ; derivativeStrictSubballScale
    ; geometricLinearCoefficient≤
    ; mulᶜ-nonnegative
    ; naturalRealBound
    ; rationalRatioPowerTimesPower
    ; ratioPowerTimesScalePower
    ; tripleScalarProductPath
    )
