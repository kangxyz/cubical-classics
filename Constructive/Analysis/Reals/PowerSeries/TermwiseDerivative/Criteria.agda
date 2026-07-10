{-

Reusable criteria for termwise differentiation of power series

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Criteria where

open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Index public
  using (termwiseConvergenceIndex)
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.IteratedBounds public
  using
    ( PowerSeriesIteratedFormalPartialDerivativeBounds
    ; positivePartialSum
    ; powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
    ; powerSeriesFormalPartialSumsDerivativeModulus
    ; powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    )
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.PartialSums public
  using (PowerSeriesPartialSumsDerivativeModulusLarge)
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Theorem public
  using
    ( centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
    ; hasDerivativeAtWith-derivative-path
    ; hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndCoefficientBoundsOnSubballCanonicalIndex
    ; hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex
    )
