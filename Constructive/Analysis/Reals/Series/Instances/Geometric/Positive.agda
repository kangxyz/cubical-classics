{-

Positive rational majorants for geometric series

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Instances.Geometric.Positive where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.GeometricDecay.Modulus
open import Constructive.Analysis.GeometricDecay.Rate
  hiding
    ( scaledGeometricSegmentModulus
    ; scaledGeometricSegmentModulus-antitone
    ; scaled-target-cancel
    ; scaledGeometricSegmentUpperBound
    ; scaledGeometricSegment
    ; scaledGeometricSegment-radius
    ; scaledGeometricSegmentUpperBound⁺
    )
open import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Reals.CauchyReals.Metric
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
open import Constructive.Analysis.Reals.Series.Cauchy
open import Constructive.Analysis.Reals.Series.Tail
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.Reals.Series.Instances.Geometric.Rational


positiveGeometricTerm :
  ℚ⁺ →
  ℕ →
  ℝᶜ
positiveGeometricTerm ρ n =
  rational (radius (positivePower ρ n))


positiveGeometricTerm-rational :
  (ρ : ℚ⁺) →
  (n : ℕ) →
  positiveGeometricTerm ρ n ≡ rationalGeometricTerm (radius ρ) n
positiveGeometricTerm-rational ρ n =
  cong rational (positivePower-radius ρ n)


positiveGeometricTerm-nonnegative :
  (ρ : ℚ⁺) →
  (n : ℕ) →
  0ᶜ ≤ᶜ positiveGeometricTerm ρ n
positiveGeometricTerm-nonnegative ρ n =
  ≤ℚ→rational≤ᶜ
    {q = Rational.0ℚ}
    {r = radius (positivePower ρ n)}
    (ℚOrder.<Weaken≤
      Rational.0ℚ
      (radius (positivePower ρ n))
      (positivePower ρ n .snd))


PositiveGeometricFiniteTailBound :
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
PositiveGeometricFiniteTailBound ρ μ =
  TailBound (positiveGeometricTerm ρ) μ


PositiveGeometricTailBound :
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
PositiveGeometricTailBound ρ μ =
  SeriesTailBound (positiveGeometricTerm ρ) μ


PositiveGeometricTailUpperBound :
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
PositiveGeometricTailUpperBound ρ μ =
  (ε : ℚ⁺) →
  (m k : ℕ) →
  NatOrder._≤_ (μ ε) m →
  tailSum (positiveGeometricTerm ρ) m k ≤ᶜ rational (radius ε)


positiveGeometricTailSum-segment :
  (ρ : ℚ⁺) →
  (m k : ℕ) →
  tailSum (positiveGeometricTerm ρ) m k ≡
  rationalGeometricSegmentSumᶜ (radius ρ) m k
positiveGeometricTailSum-segment ρ m k =
  cong
    (λ u → tailSum u m k)
    (funExt (positiveGeometricTerm-rational ρ)) ∙
  rationalGeometricSegmentTailSum (radius ρ) m k


positiveGeometricTailUpperBoundFromSegment :
  (ρ : ℚ⁺) →
  {μ : ℚ⁺ → ℕ} →
  PositiveGeometricSegmentUpperBound ρ μ →
  PositiveGeometricTailUpperBound ρ μ
positiveGeometricTailUpperBoundFromSegment ρ segmentUpper ε m k μ≤m =
  subst
    (λ x → x ≤ᶜ rational (radius ε))
    (sym (positiveGeometricTailSum-segment ρ m k))
    (≤ℚ→rational≤ᶜ (segmentUpper ε m k μ≤m))


positiveGeometricFiniteTailBoundFromUpper :
  (ρ : ℚ⁺) →
  {μ : ℚ⁺ → ℕ} →
  PositiveGeometricTailUpperBound ρ μ →
  PositiveGeometricFiniteTailBound ρ μ
positiveGeometricFiniteTailBoundFromUpper ρ upper =
  nonnegative-tail-upper→TailBound
    (positiveGeometricTerm-nonnegative ρ)
    upper


positiveGeometricTailUpperBoundFromRatio :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PositiveGeometricTailUpperBound
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
positiveGeometricTailUpperBoundFromRatio ρ ρ<1 =
  positiveGeometricTailUpperBoundFromSegment
    ρ
    (positiveGeometricSegmentUpperBoundFromRatio ρ ρ<1)


positiveGeometricFiniteTailBoundFromRatio :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PositiveGeometricFiniteTailBound
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
positiveGeometricFiniteTailBoundFromRatio ρ ρ<1 =
  positiveGeometricFiniteTailBoundFromUpper
    ρ
    (positiveGeometricTailUpperBoundFromRatio ρ ρ<1)


record PositiveGeometricTailData (ρ : ℚ⁺) : Type₀ where
  no-eta-equality

  field
    ratioBound<1 : radius ρ ℚOrder.< Rational.1ℚ
    modulus : ℚ⁺ → ℕ
    finiteTailBound : PositiveGeometricFiniteTailBound ρ modulus
    modulusAntitone : AntitoneNatModulus modulus


record PositiveGeometricTailUpperData (ρ : ℚ⁺) : Type₀ where
  no-eta-equality

  field
    ratioBound<1 : radius ρ ℚOrder.< Rational.1ℚ
    modulus : ℚ⁺ → ℕ
    tailUpperBound : PositiveGeometricTailUpperBound ρ modulus
    modulusAntitone : AntitoneNatModulus modulus


record PositiveGeometricSegmentUpperData (ρ : ℚ⁺) : Type₀ where
  no-eta-equality

  field
    ratioBound<1 : radius ρ ℚOrder.< Rational.1ℚ
    modulus : ℚ⁺ → ℕ
    segmentUpperBound : PositiveGeometricSegmentUpperBound ρ modulus
    modulusAntitone : AntitoneNatModulus modulus


record PositiveGeometricScaledSegmentUpperData (ρ : ℚ⁺) : Type₀ where
  no-eta-equality

  field
    ratioBound<1 : radius ρ ℚOrder.< Rational.1ℚ
    modulus : ℚ⁺ → ℕ
    scaledSegmentUpperBound : PositiveGeometricScaledSegmentUpperBound ρ modulus
    modulusAntitone : AntitoneNatModulus modulus


record PositiveGeometricPowerScaledUpperData (ρ : ℚ⁺) : Type₀ where
  no-eta-equality

  field
    ratioBound<1 : radius ρ ℚOrder.< Rational.1ℚ
    modulus : ℚ⁺ → ℕ
    powerScaledUpperBound : PositiveGeometricPowerScaledUpperBound ρ modulus
    modulusAntitone : AntitoneNatModulus modulus


positiveGeometricScaledSegmentUpperDataFromPowerData :
  (ρ : ℚ⁺) →
  PositiveGeometricPowerScaledUpperData ρ →
  PositiveGeometricScaledSegmentUpperData ρ
positiveGeometricScaledSegmentUpperDataFromPowerData ρ powerData =
  record
    { ratioBound<1 =
        PositiveGeometricPowerScaledUpperData.ratioBound<1 powerData
    ; modulus =
        PositiveGeometricPowerScaledUpperData.modulus powerData
    ; scaledSegmentUpperBound =
        positiveGeometricScaledSegmentUpperBoundFromPower
          ρ
          (PositiveGeometricPowerScaledUpperData.powerScaledUpperBound powerData)
    ; modulusAntitone =
        PositiveGeometricPowerScaledUpperData.modulusAntitone powerData
    }


positiveGeometricSegmentUpperDataFromScaledData :
  (ρ : ℚ⁺) →
  PositiveGeometricScaledSegmentUpperData ρ →
  PositiveGeometricSegmentUpperData ρ
positiveGeometricSegmentUpperDataFromScaledData ρ scaledData =
  record
    { ratioBound<1 =
        PositiveGeometricScaledSegmentUpperData.ratioBound<1 scaledData
    ; modulus =
        PositiveGeometricScaledSegmentUpperData.modulus scaledData
    ; segmentUpperBound =
        positiveGeometricSegmentUpperBoundFromScaled
          ρ
          (PositiveGeometricScaledSegmentUpperData.ratioBound<1 scaledData)
          (PositiveGeometricScaledSegmentUpperData.scaledSegmentUpperBound scaledData)
    ; modulusAntitone =
        PositiveGeometricScaledSegmentUpperData.modulusAntitone scaledData
    }


positiveGeometricTailUpperDataFromSegmentData :
  (ρ : ℚ⁺) →
  PositiveGeometricSegmentUpperData ρ →
  PositiveGeometricTailUpperData ρ
positiveGeometricTailUpperDataFromSegmentData ρ segmentData =
  record
    { ratioBound<1 =
        PositiveGeometricSegmentUpperData.ratioBound<1 segmentData
    ; modulus =
        PositiveGeometricSegmentUpperData.modulus segmentData
    ; tailUpperBound =
        positiveGeometricTailUpperBoundFromSegment
          ρ
          (PositiveGeometricSegmentUpperData.segmentUpperBound segmentData)
    ; modulusAntitone =
        PositiveGeometricSegmentUpperData.modulusAntitone segmentData
    }


positiveGeometricTailDataFromUpperData :
  (ρ : ℚ⁺) →
  PositiveGeometricTailUpperData ρ →
  PositiveGeometricTailData ρ
positiveGeometricTailDataFromUpperData ρ upperData =
  record
    { ratioBound<1 =
        PositiveGeometricTailUpperData.ratioBound<1 upperData
    ; modulus =
        PositiveGeometricTailUpperData.modulus upperData
    ; finiteTailBound =
        positiveGeometricFiniteTailBoundFromUpper
          ρ
          (PositiveGeometricTailUpperData.tailUpperBound upperData)
    ; modulusAntitone =
        PositiveGeometricTailUpperData.modulusAntitone upperData
    }


positiveGeometricTailDataFromSegmentData :
  (ρ : ℚ⁺) →
  PositiveGeometricSegmentUpperData ρ →
  PositiveGeometricTailData ρ
positiveGeometricTailDataFromSegmentData ρ segmentData =
  positiveGeometricTailDataFromUpperData
    ρ
    (positiveGeometricTailUpperDataFromSegmentData ρ segmentData)


positiveGeometricSegmentUpperDataFromPowerData :
  (ρ : ℚ⁺) →
  PositiveGeometricPowerScaledUpperData ρ →
  PositiveGeometricSegmentUpperData ρ
positiveGeometricSegmentUpperDataFromPowerData ρ powerData =
  positiveGeometricSegmentUpperDataFromScaledData
    ρ
    (positiveGeometricScaledSegmentUpperDataFromPowerData ρ powerData)


positiveGeometricTailDataFromPowerData :
  (ρ : ℚ⁺) →
  PositiveGeometricPowerScaledUpperData ρ →
  PositiveGeometricTailData ρ
positiveGeometricTailDataFromPowerData ρ powerData =
  positiveGeometricTailDataFromSegmentData
    ρ
    (positiveGeometricSegmentUpperDataFromPowerData ρ powerData)


positiveGeometricPowerScaledUpperDataFromRatio :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PositiveGeometricPowerScaledUpperData ρ
positiveGeometricPowerScaledUpperDataFromRatio ρ ρ<1 =
  record
    { ratioBound<1 = ρ<1
    ; modulus = positiveGeometricPowerModulus ρ ρ<1
    ; powerScaledUpperBound =
        positiveGeometricPowerScaledUpperBoundFromRatio ρ ρ<1
    ; modulusAntitone =
        positiveGeometricPowerModulus-antitone ρ ρ<1
    }


positiveGeometricScaledSegmentUpperDataFromRatio :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PositiveGeometricScaledSegmentUpperData ρ
positiveGeometricScaledSegmentUpperDataFromRatio ρ ρ<1 =
  positiveGeometricScaledSegmentUpperDataFromPowerData
    ρ
    (positiveGeometricPowerScaledUpperDataFromRatio ρ ρ<1)


positiveGeometricSegmentUpperDataFromRatio :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PositiveGeometricSegmentUpperData ρ
positiveGeometricSegmentUpperDataFromRatio ρ ρ<1 =
  positiveGeometricSegmentUpperDataFromPowerData
    ρ
    (positiveGeometricPowerScaledUpperDataFromRatio ρ ρ<1)


positiveGeometricTailUpperDataFromRatio :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PositiveGeometricTailUpperData ρ
positiveGeometricTailUpperDataFromRatio ρ ρ<1 =
  positiveGeometricTailUpperDataFromSegmentData
    ρ
    (positiveGeometricSegmentUpperDataFromRatio ρ ρ<1)


positiveGeometricTailDataFromRatio :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PositiveGeometricTailData ρ
positiveGeometricTailDataFromRatio ρ ρ<1 =
  positiveGeometricTailDataFromPowerData
    ρ
    (positiveGeometricPowerScaledUpperDataFromRatio ρ ρ<1)


positiveGeometricSeriesTailBound :
  (ρ : ℚ⁺) →
  (tailData : PositiveGeometricTailData ρ) →
  PositiveGeometricTailBound ρ
    (λ ε → PositiveGeometricTailData.modulus tailData (half⁺ ε))
positiveGeometricSeriesTailBound ρ tailData =
  tailBound→SeriesTailBound
    (PositiveGeometricTailData.finiteTailBound tailData)
    (PositiveGeometricTailData.modulusAntitone tailData)


positiveGeometricSum :
  (ρ : ℚ⁺) →
  PositiveGeometricTailData ρ →
  ℝᶜ
positiveGeometricSum ρ tailData =
  seriesSumFromFiniteTailBound
    (positiveGeometricTerm ρ)
    (PositiveGeometricTailData.modulus tailData)
    (PositiveGeometricTailData.finiteTailBound tailData)
    (PositiveGeometricTailData.modulusAntitone tailData)


positiveGeometricConverges :
  (ρ : ℚ⁺) →
  (tailData : PositiveGeometricTailData ρ) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (positiveGeometricTerm ρ)
      (PositiveGeometricTailData.modulus tailData)
      (PositiveGeometricTailData.finiteTailBound tailData)
      (PositiveGeometricTailData.modulusAntitone tailData))
    (positiveGeometricSum ρ tailData)
positiveGeometricConverges ρ tailData =
  seriesSumFromFiniteTailBoundConverges
    (positiveGeometricTerm ρ)
    (PositiveGeometricTailData.modulus tailData)
    (PositiveGeometricTailData.finiteTailBound tailData)
    (PositiveGeometricTailData.modulusAntitone tailData)


positiveGeometricSeriesTailBoundFromUpperData :
  (ρ : ℚ⁺) →
  (upperData : PositiveGeometricTailUpperData ρ) →
  PositiveGeometricTailBound ρ
    (λ ε → PositiveGeometricTailUpperData.modulus upperData (half⁺ ε))
positiveGeometricSeriesTailBoundFromUpperData ρ upperData =
  positiveGeometricSeriesTailBound
    ρ
    (positiveGeometricTailDataFromUpperData ρ upperData)


positiveGeometricSumFromUpperData :
  (ρ : ℚ⁺) →
  PositiveGeometricTailUpperData ρ →
  ℝᶜ
positiveGeometricSumFromUpperData ρ upperData =
  positiveGeometricSum
    ρ
    (positiveGeometricTailDataFromUpperData ρ upperData)


positiveGeometricConvergesFromUpperData :
  (ρ : ℚ⁺) →
  (upperData : PositiveGeometricTailUpperData ρ) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (positiveGeometricTerm ρ)
      (PositiveGeometricTailUpperData.modulus upperData)
      (positiveGeometricFiniteTailBoundFromUpper
        ρ
        (PositiveGeometricTailUpperData.tailUpperBound upperData))
      (PositiveGeometricTailUpperData.modulusAntitone upperData))
    (positiveGeometricSumFromUpperData ρ upperData)
positiveGeometricConvergesFromUpperData ρ upperData =
  positiveGeometricConverges
    ρ
    (positiveGeometricTailDataFromUpperData ρ upperData)


positiveGeometricSeriesTailBoundFromSegmentData :
  (ρ : ℚ⁺) →
  (segmentData : PositiveGeometricSegmentUpperData ρ) →
  PositiveGeometricTailBound ρ
    (λ ε → PositiveGeometricSegmentUpperData.modulus segmentData (half⁺ ε))
positiveGeometricSeriesTailBoundFromSegmentData ρ segmentData =
  positiveGeometricSeriesTailBound
    ρ
    (positiveGeometricTailDataFromSegmentData ρ segmentData)


positiveGeometricSumFromSegmentData :
  (ρ : ℚ⁺) →
  PositiveGeometricSegmentUpperData ρ →
  ℝᶜ
positiveGeometricSumFromSegmentData ρ segmentData =
  positiveGeometricSum
    ρ
    (positiveGeometricTailDataFromSegmentData ρ segmentData)


positiveGeometricSeriesTailBoundFromPowerData :
  (ρ : ℚ⁺) →
  (powerData : PositiveGeometricPowerScaledUpperData ρ) →
  PositiveGeometricTailBound ρ
    (λ ε → PositiveGeometricPowerScaledUpperData.modulus powerData (half⁺ ε))
positiveGeometricSeriesTailBoundFromPowerData ρ powerData =
  positiveGeometricSeriesTailBound
    ρ
    (positiveGeometricTailDataFromPowerData ρ powerData)


positiveGeometricSumFromPowerData :
  (ρ : ℚ⁺) →
  PositiveGeometricPowerScaledUpperData ρ →
  ℝᶜ
positiveGeometricSumFromPowerData ρ powerData =
  positiveGeometricSum
    ρ
    (positiveGeometricTailDataFromPowerData ρ powerData)
