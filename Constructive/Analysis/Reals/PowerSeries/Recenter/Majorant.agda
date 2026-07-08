{-

Majorant data for re-centered power series.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.Majorant where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)

open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.Series
  using
    ( AntitoneTailModulus
    ; SeriesMajorizedBy
    ; TailBound
    ; comparisonTest
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Base
open import Constructive.Data.PositiveRationals
  using (ℚ⁺)


record RecenterCoefficientMajorantData
    (a : PowerSeries)
    (d : ℝᶜ)
    (n : ℕ)
    : Type₀ where
  field
    coefficientMajorant :
      ℕ →
      ℝᶜ

    coefficientModulus :
      ℚ⁺ →
      ℕ

    coefficientMajorized :
      SeriesMajorizedBy
        (recenterCoefficientTerm a d n)
        coefficientMajorant

    coefficientMajorTail :
      TailBound coefficientMajorant coefficientModulus

    coefficientMajorAntitone :
      AntitoneTailModulus coefficientModulus


open RecenterCoefficientMajorantData public


recenterCoefficientConvergenceDataFromMajorant :
  {a : PowerSeries} →
  {d : ℝᶜ} →
  {n : ℕ} →
  RecenterCoefficientMajorantData a d n →
  RecenterCoefficientConvergenceData a d n
modulus (recenterCoefficientConvergenceDataFromMajorant majorantData) =
  coefficientModulus majorantData
tailBound (recenterCoefficientConvergenceDataFromMajorant majorantData) =
  comparisonTest
    (coefficientMajorized majorantData)
    (coefficientMajorTail majorantData)
modulus-antitone (recenterCoefficientConvergenceDataFromMajorant majorantData) =
  coefficientMajorAntitone majorantData


record RecenterCoefficientMajorants
    (a : PowerSeries)
    (d : ℝᶜ)
    : Type₀ where
  field
    coefficientMajorantData :
      (n : ℕ) →
      RecenterCoefficientMajorantData a d n


open RecenterCoefficientMajorants public


recenterPowerSeriesDataFromCoefficientMajorants :
  {a : PowerSeries} →
  {d : ℝᶜ} →
  RecenterCoefficientMajorants a d →
  RecenterPowerSeriesData a d
coefficientData
    (recenterPowerSeriesDataFromCoefficientMajorants coefficientMajorants)
    n =
  recenterCoefficientConvergenceDataFromMajorant
    (coefficientMajorantData coefficientMajorants n)


recenterPowerSeriesFromCoefficientMajorants :
  (a : PowerSeries) →
  (d : ℝᶜ) →
  RecenterCoefficientMajorants a d →
  PowerSeries
recenterPowerSeriesFromCoefficientMajorants a d coefficientMajorants =
  recenterPowerSeriesWith
    a
    d
    (recenterPowerSeriesDataFromCoefficientMajorants coefficientMajorants)
