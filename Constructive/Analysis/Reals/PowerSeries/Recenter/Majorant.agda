{-

Majorant data for re-centered power series.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.Majorant where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.Series
  using
    ( SeriesMajorizedBy
    ; TailBound
    ; comparisonTest
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Base
open import Constructive.Data.PositiveRationals
  using (ℚ⁺)


RecenterCoefficientMajorantData :
  (a : PowerSeries) →
  (d : ℝᶜ) →
  (n : ℕ) →
  Type₀
RecenterCoefficientMajorantData a d n =
  Σ[ coefficientMajorant ∈ (ℕ → ℝᶜ) ]
    Σ[ coefficientModulus ∈ (ℚ⁺ → ℕ) ]
      Σ[ coefficientMajorized ∈
          SeriesMajorizedBy
            (recenterCoefficientTerm a d n)
            coefficientMajorant ]
        Σ[ coefficientMajorTail ∈
            TailBound coefficientMajorant coefficientModulus ]
          AntitoneNatModulus coefficientModulus


module RecenterCoefficientMajorantData where
  coefficientMajorant :
    {a : PowerSeries} →
    {d : ℝᶜ} →
    {n : ℕ} →
    RecenterCoefficientMajorantData a d n →
    ℕ →
    ℝᶜ
  coefficientMajorant majorantData =
    majorantData .fst

  coefficientModulus :
    {a : PowerSeries} →
    {d : ℝᶜ} →
    {n : ℕ} →
    RecenterCoefficientMajorantData a d n →
    ℚ⁺ →
    ℕ
  coefficientModulus majorantData =
    majorantData .snd .fst

  coefficientMajorized :
    {a : PowerSeries} →
    {d : ℝᶜ} →
    {n : ℕ} →
    (majorantData : RecenterCoefficientMajorantData a d n) →
    SeriesMajorizedBy
      (recenterCoefficientTerm a d n)
      (coefficientMajorant majorantData)
  coefficientMajorized majorantData =
    majorantData .snd .snd .fst

  coefficientMajorTail :
    {a : PowerSeries} →
    {d : ℝᶜ} →
    {n : ℕ} →
    (majorantData : RecenterCoefficientMajorantData a d n) →
    TailBound
      (coefficientMajorant majorantData)
      (coefficientModulus majorantData)
  coefficientMajorTail majorantData =
    majorantData .snd .snd .snd .fst

  coefficientMajorAntitone :
    {a : PowerSeries} →
    {d : ℝᶜ} →
    {n : ℕ} →
    (majorantData : RecenterCoefficientMajorantData a d n) →
    AntitoneNatModulus (coefficientModulus majorantData)
  coefficientMajorAntitone majorantData =
    majorantData .snd .snd .snd .snd


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


RecenterCoefficientMajorants :
  (a : PowerSeries) →
  (d : ℝᶜ) →
  Type₀
RecenterCoefficientMajorants a d =
  (n : ℕ) →
  RecenterCoefficientMajorantData a d n


module RecenterCoefficientMajorants where
  coefficientMajorantData :
    {a : PowerSeries} →
    {d : ℝᶜ} →
    RecenterCoefficientMajorants a d →
    (n : ℕ) →
    RecenterCoefficientMajorantData a d n
  coefficientMajorantData coefficientMajorants =
    coefficientMajorants


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
