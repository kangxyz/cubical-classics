{-

Reciprocal-factorial coefficient and majorant bounds

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds where

open import Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds.Coefficients
  public
  using
    ( reciprocalFactorialClosedBoundOne
    ; reciprocalFactorial⁺
    ; reciprocalFactorialClosedBoundSelf
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds.Majorant
  public
  using
    ( factorialMajorantRadius
    ; factorialMajorantTerm
    ; factorialMajorantTerm-nonnegative
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds.Tail
  public
  using
    ( factorialMajorantModulus
    ; factorialMajorantTailBound
    ; factorialMajorantModulusAntitone
    )
