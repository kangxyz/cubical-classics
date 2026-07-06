{-

Real geometric series from explicit majorants

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Instances.Geometric.Real where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax)
import Cubical.Data.Sum as Sum
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Series
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.Reals.Series.Instances.Geometric.Rational
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Majorant

record RealGeometricBound (x : ℝᶜ) : Type₀ where
  no-eta-equality

  field
    ratioBound : ℚ⁺
    ratioBound<1 : radius ratioBound ℚOrder.< Rational.1ℚ
    termBound : BoundedByᶜ ratioBound x


record RealGeometricTerms (x : ℝᶜ) : Type₀ where
  no-eta-equality

  field
    term : ℕ → ℝᶜ
    firstTerm : term zero ≡ rationalGeometricTerm Rational.1ℚ zero


realPower :
  ℝᶜ →
  ℕ →
  ℝᶜ
realPower x zero =
  1ᶜ
realPower x (suc n) =
  x ·ᶜ realPower x n


realPower-zero :
  (x : ℝᶜ) →
  realPower x zero ≡ 1ᶜ
realPower-zero x =
  refl


realPower-suc :
  (x : ℝᶜ) →
  (n : ℕ) →
  realPower x (suc n) ≡ x ·ᶜ realPower x n
realPower-suc x n =
  refl


realGeometricPowerTerms :
  (x : ℝᶜ) →
  RealGeometricTerms x
realGeometricPowerTerms x =
  record
    { term = realPower x
    ; firstTerm = refl
    }


RealGeometricPowerTailBound :
  (x : ℝᶜ) →
  (ℚ⁺ → ℕ) →
  Type₀
RealGeometricPowerTailBound x μ =
  SeriesTailBound (realPower x) μ


RealGeometricTailBound :
  (x : ℝᶜ) →
  RealGeometricTerms x →
  (ℚ⁺ → ℕ) →
  Type₀
RealGeometricTailBound x terms μ =
  SeriesTailBound (RealGeometricTerms.term terms) μ


RealGeometricFiniteTailBound :
  (x : ℝᶜ) →
  RealGeometricTerms x →
  (ℚ⁺ → ℕ) →
  Type₀
RealGeometricFiniteTailBound x terms μ =
  TailBound (RealGeometricTerms.term terms) μ


record RealGeometricPowerMajorant
  (x : ℝᶜ)
  (terms : RealGeometricTerms x)
  (bound : RealGeometricBound x) : Type₀ where
  no-eta-equality

  field
    termsMajorized :
      SeriesMajorizedBy
        (RealGeometricTerms.term terms)
        (positiveGeometricTerm (RealGeometricBound.ratioBound bound))


realGeometricTailBoundFromMajorant :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  {μ : ℚ⁺ → ℕ} →
  PositiveGeometricFiniteTailBound
    (RealGeometricBound.ratioBound bound)
    μ →
  RealGeometricFiniteTailBound x terms μ
realGeometricTailBoundFromMajorant x terms bound majorant =
  comparisonTest (RealGeometricPowerMajorant.termsMajorized majorant)


realGeometricSeriesTailBoundFromMajorant :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  {μ : ℚ⁺ → ℕ} →
  PositiveGeometricFiniteTailBound
    (RealGeometricBound.ratioBound bound)
    μ →
  AntitoneTailModulus μ →
  RealGeometricTailBound x terms (λ ε → μ (half⁺ ε))
realGeometricSeriesTailBoundFromMajorant x terms bound majorant majorTail μ-antitone =
  tailBound→SeriesTailBound
    (realGeometricTailBoundFromMajorant x terms bound majorant majorTail)
    μ-antitone


realGeometricSeriesTailBoundFromPositiveData :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  (tailData : PositiveGeometricTailData (RealGeometricBound.ratioBound bound)) →
  RealGeometricTailBound x terms
    (λ ε →
      PositiveGeometricTailData.modulus
        tailData
        (half⁺ ε))
realGeometricSeriesTailBoundFromPositiveData x terms bound majorant tailData =
  realGeometricSeriesTailBoundFromMajorant
    x
    terms
    bound
    majorant
    (PositiveGeometricTailData.finiteTailBound tailData)
    (PositiveGeometricTailData.modulusAntitone tailData)


realGeometricTailBoundFromRatio :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  RealGeometricFiniteTailBound
    x
    terms
    (positiveGeometricPowerModulus
      (RealGeometricBound.ratioBound bound)
      (RealGeometricBound.ratioBound<1 bound))
realGeometricTailBoundFromRatio x terms bound majorant =
  realGeometricTailBoundFromMajorant
    x
    terms
    bound
    majorant
    (positiveGeometricFiniteTailBoundFromRatio
      ρ
      ρ<1)
  where
  ρ : ℚ⁺
  ρ =
    RealGeometricBound.ratioBound bound

  ρ<1 : radius ρ ℚOrder.< Rational.1ℚ
  ρ<1 =
    RealGeometricBound.ratioBound<1 bound


realGeometricSumFromMajorant :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  (μ : ℚ⁺ → ℕ) →
  PositiveGeometricFiniteTailBound
    (RealGeometricBound.ratioBound bound)
    μ →
  AntitoneTailModulus μ →
  ℝᶜ
realGeometricSumFromMajorant x terms bound majorant μ majorTail μ-antitone =
  seriesSumFromFiniteTailBound
    (RealGeometricTerms.term terms)
    μ
    (realGeometricTailBoundFromMajorant x terms bound majorant majorTail)
    μ-antitone


realGeometricSumFromPositiveData :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  PositiveGeometricTailData (RealGeometricBound.ratioBound bound) →
  ℝᶜ
realGeometricSumFromPositiveData x terms bound majorant tailData =
  realGeometricSumFromMajorant
    x
    terms
    bound
    majorant
    (PositiveGeometricTailData.modulus tailData)
    (PositiveGeometricTailData.finiteTailBound tailData)
    (PositiveGeometricTailData.modulusAntitone tailData)


realGeometricConvergesFromPositiveData :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  (majorant : RealGeometricPowerMajorant x terms bound) →
  (tailData : PositiveGeometricTailData
    (RealGeometricBound.ratioBound bound)) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (RealGeometricTerms.term terms)
      (PositiveGeometricTailData.modulus tailData)
      (realGeometricTailBoundFromMajorant
        x
        terms
        bound
        majorant
        (PositiveGeometricTailData.finiteTailBound tailData))
      (PositiveGeometricTailData.modulusAntitone tailData))
    (realGeometricSumFromPositiveData x terms bound majorant tailData)
realGeometricConvergesFromPositiveData x terms bound majorant tailData =
  seriesSumFromFiniteTailBoundConverges
    (RealGeometricTerms.term terms)
    (PositiveGeometricTailData.modulus tailData)
    (realGeometricTailBoundFromMajorant
      x
      terms
      bound
      majorant
        (PositiveGeometricTailData.finiteTailBound tailData))
    (PositiveGeometricTailData.modulusAntitone tailData)


realGeometricTailBoundFromUpperData :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  (upperData : PositiveGeometricTailUpperData
    (RealGeometricBound.ratioBound bound)) →
  RealGeometricFiniteTailBound x terms
    (PositiveGeometricTailUpperData.modulus upperData)
realGeometricTailBoundFromUpperData x terms bound majorant upperData =
  realGeometricTailBoundFromMajorant
    x
    terms
    bound
    majorant
    (positiveGeometricFiniteTailBoundFromUpper
      (RealGeometricBound.ratioBound bound)
      (PositiveGeometricTailUpperData.tailUpperBound upperData))


realGeometricSeriesTailBoundFromUpperData :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  (upperData : PositiveGeometricTailUpperData
    (RealGeometricBound.ratioBound bound)) →
  RealGeometricTailBound x terms
    (λ ε →
      PositiveGeometricTailUpperData.modulus
        upperData
        (half⁺ ε))
realGeometricSeriesTailBoundFromUpperData x terms bound majorant upperData =
  realGeometricSeriesTailBoundFromPositiveData
    x
    terms
    bound
    majorant
    (positiveGeometricTailDataFromUpperData
      (RealGeometricBound.ratioBound bound)
      upperData)


realGeometricSumFromUpperData :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  PositiveGeometricTailUpperData (RealGeometricBound.ratioBound bound) →
  ℝᶜ
realGeometricSumFromUpperData x terms bound majorant upperData =
  realGeometricSumFromPositiveData
    x
    terms
    bound
    majorant
    (positiveGeometricTailDataFromUpperData
      (RealGeometricBound.ratioBound bound)
      upperData)


RealGeometricPowerMajorized :
  (x : ℝᶜ) →
  RealGeometricBound x →
  Type₀
RealGeometricPowerMajorized x bound =
  RealGeometricPowerMajorant x (realGeometricPowerTerms x) bound


realGeometricPowerSeriesTailBoundFromPositiveData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  (tailData : PositiveGeometricTailData
    (RealGeometricBound.ratioBound bound)) →
  RealGeometricPowerTailBound x
    (λ ε → PositiveGeometricTailData.modulus tailData (half⁺ ε))
realGeometricPowerSeriesTailBoundFromPositiveData x bound majorant tailData =
  realGeometricSeriesTailBoundFromPositiveData
    x
    (realGeometricPowerTerms x)
    bound
    majorant
    tailData


realGeometricPowerSumFromPositiveData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  PositiveGeometricTailData (RealGeometricBound.ratioBound bound) →
  ℝᶜ
realGeometricPowerSumFromPositiveData x bound majorant tailData =
  realGeometricSumFromPositiveData
    x
    (realGeometricPowerTerms x)
    bound
    majorant
    tailData


realGeometricPowerConvergesFromPositiveData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  (majorant : RealGeometricPowerMajorized x bound) →
  (tailData : PositiveGeometricTailData
    (RealGeometricBound.ratioBound bound)) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (realPower x)
      (PositiveGeometricTailData.modulus tailData)
      (realGeometricTailBoundFromMajorant
        x
        (realGeometricPowerTerms x)
        bound
        majorant
        (PositiveGeometricTailData.finiteTailBound tailData))
      (PositiveGeometricTailData.modulusAntitone tailData))
    (realGeometricPowerSumFromPositiveData x bound majorant tailData)
realGeometricPowerConvergesFromPositiveData x bound majorant tailData =
  realGeometricConvergesFromPositiveData
    x
    (realGeometricPowerTerms x)
    bound
    majorant
    tailData


realGeometricPowerSeriesTailBoundFromUpperData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  (upperData : PositiveGeometricTailUpperData
    (RealGeometricBound.ratioBound bound)) →
  RealGeometricPowerTailBound x
    (λ ε → PositiveGeometricTailUpperData.modulus upperData (half⁺ ε))
realGeometricPowerSeriesTailBoundFromUpperData x bound majorant upperData =
  realGeometricSeriesTailBoundFromUpperData
    x
    (realGeometricPowerTerms x)
    bound
    majorant
    upperData


realGeometricPowerSumFromUpperData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  PositiveGeometricTailUpperData (RealGeometricBound.ratioBound bound) →
  ℝᶜ
realGeometricPowerSumFromUpperData x bound majorant upperData =
  realGeometricSumFromUpperData
    x
    (realGeometricPowerTerms x)
    bound
    majorant
    upperData


realGeometricPowerSeriesTailBoundFromSegmentData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  (segmentData : PositiveGeometricSegmentUpperData
    (RealGeometricBound.ratioBound bound)) →
  RealGeometricPowerTailBound x
    (λ ε → PositiveGeometricSegmentUpperData.modulus segmentData (half⁺ ε))
realGeometricPowerSeriesTailBoundFromSegmentData x bound majorant segmentData =
  realGeometricPowerSeriesTailBoundFromUpperData
    x
    bound
    majorant
    (positiveGeometricTailUpperDataFromSegmentData
      (RealGeometricBound.ratioBound bound)
      segmentData)


realGeometricPowerSumFromSegmentData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  PositiveGeometricSegmentUpperData (RealGeometricBound.ratioBound bound) →
  ℝᶜ
realGeometricPowerSumFromSegmentData x bound majorant segmentData =
  realGeometricPowerSumFromUpperData
    x
    bound
    majorant
    (positiveGeometricTailUpperDataFromSegmentData
      (RealGeometricBound.ratioBound bound)
      segmentData)


realGeometricPowerSeriesTailBoundFromPowerData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  (powerData : PositiveGeometricPowerScaledUpperData
    (RealGeometricBound.ratioBound bound)) →
  RealGeometricPowerTailBound x
    (λ ε → PositiveGeometricPowerScaledUpperData.modulus powerData (half⁺ ε))
realGeometricPowerSeriesTailBoundFromPowerData x bound majorant powerData =
  realGeometricPowerSeriesTailBoundFromPositiveData
    x
    bound
    majorant
    (positiveGeometricTailDataFromPowerData
      (RealGeometricBound.ratioBound bound)
      powerData)


realGeometricPowerSumFromPowerData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  PositiveGeometricPowerScaledUpperData (RealGeometricBound.ratioBound bound) →
  ℝᶜ
realGeometricPowerSumFromPowerData x bound majorant powerData =
  realGeometricPowerSumFromPositiveData
    x
    bound
    majorant
    (positiveGeometricTailDataFromPowerData
      (RealGeometricBound.ratioBound bound)
      powerData)


realGeometricCauchyApproximation :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (μ : ℚ⁺ → ℕ) →
  RealGeometricTailBound x terms μ →
  MetricCauchy.CauchyApproximation CauchyRealsMetricSpace
realGeometricCauchyApproximation x terms μ tailBound =
  seriesCauchyApproximationFromTailBound
    (RealGeometricTerms.term terms)
    μ
    tailBound


realGeometricSum :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (μ : ℚ⁺ → ℕ) →
  RealGeometricTailBound x terms μ →
  ℝᶜ
realGeometricSum x terms μ tailBound =
  seriesSum (RealGeometricTerms.term terms) μ tailBound


realGeometricConverges :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : RealGeometricTailBound x terms μ) →
  MetricCauchy.ConvergesTo
    (realGeometricCauchyApproximation x terms μ tailBound)
    (realGeometricSum x terms μ tailBound)
realGeometricConverges x terms μ tailBound =
  seriesSumConverges (RealGeometricTerms.term terms) μ tailBound


RealGeometricConvergesWith :
  (x : ℝᶜ) →
  RealGeometricTerms x →
  Type₀
RealGeometricConvergesWith x terms =
  Σ[ μ ∈ (ℚ⁺ → ℕ) ] RealGeometricTailBound x terms μ
