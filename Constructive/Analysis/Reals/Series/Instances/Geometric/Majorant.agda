{-

Rational geometric series from positive majorants

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Instances.Geometric.Majorant where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
import Cubical.Data.Sum as Sum
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.GeometricDecay
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
open import Constructive.Analysis.Reals.Series.Comparison
open import Constructive.Analysis.Reals.Series.Tail
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.Reals.Series.Instances.Geometric.Rational
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive

bounded-byᶜ-abs :
  {κ : ℚ⁺} {x : ℝᶜ} →
  BoundedByᶜ κ x →
  absᶜ x ≤ᶜ rational (radius κ)
bounded-byᶜ-abs {κ = κ} {x = x} x-bound =
  absᶜ-least
    x
    (rational (radius κ))
    (≤ℚ→rational≤ᶜ
      {q = Rational.0ℚ}
      {r = radius κ}
      (ℚOrder.<Weaken≤ Rational.0ℚ (radius κ) (κ .snd)))
    (upperᶜ x-bound)
    (lowerᶜ x-bound)


bounded-byᶜ-scale-rational-closed-bound :
  (a : ℚ) (κ μ : ℚ⁺) (x : ℝᶜ) →
  RationalClosedBoundᶜ μ a →
  BoundedByᶜ κ x →
  BoundedByᶜ (μ *⁺ κ) (scalarMulᶜ a x)
bounded-byᶜ-scale-rational-closed-bound a κ μ x a-bound x-bound =
  Sum.rec negativeCase nonnegativeCase (Rational.negative-or-nonnegative a)
  where
  scalar-a≡neg-scale--a :
    scalarMulᶜ a x ≡ -ᶜ (scalarMulᶜ (ℚ.- a) x)
  scalar-a≡neg-scale--a =
    sym (cong (λ s → scalarMulᶜ s x) (ℚ.-Invol a)) ∙
    scalarMulᶜ-neg-scalar (ℚ.- a) x

  nonnegativeCase :
    Rational.0ℚ ℚOrder.≤ a →
    BoundedByᶜ (μ *⁺ κ) (scalarMulᶜ a x)
  nonnegativeCase 0≤a =
    bounded-byᶜ-scale-nonnegative
      a
      κ
      μ
      x
      0≤a
      (upper≤ℚ a-bound)
      x-bound

  negativeCase :
    a ℚOrder.< Rational.0ℚ →
    BoundedByᶜ (μ *⁺ κ) (scalarMulᶜ a x)
  negativeCase a<0 =
    subst
      (BoundedByᶜ (μ *⁺ κ))
      (sym scalar-a≡neg-scale--a)
      (bounded-byᶜ-neg
        (μ *⁺ κ)
        (scalarMulᶜ (ℚ.- a) x)
        (bounded-byᶜ-scale-nonnegative
          (ℚ.- a)
          κ
          μ
          x
          (Rational.<→≤ {p = Rational.0ℚ} {q = ℚ.- a}
            (Rational.neg-positive {q = a} a<0))
          (lower≤ℚ a-bound)
          x-bound))


rationalPower-bounded :
  (r : ℚ) →
  (ρ : ℚ⁺) →
  RationalClosedBoundᶜ ρ r →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (rationalGeometricTerm r n)
rationalPower-bounded r ρ r-bound zero =
  rational-closed-bound→boundedᶜ
    1⁺
    Rational.1ℚ
    (rational-closed-boundᶜ
      (Rational.≤-refl Rational.1ℚ)
      (Rational.<→≤
        {p = Rational.-1ℚ}
        {q = Rational.1ℚ}
        (ℚOrder.isTrans<
          Rational.-1ℚ
          Rational.0ℚ
          Rational.1ℚ
          Rational.-1<0
          Rational.0<1)))
rationalPower-bounded r ρ r-bound (suc n) =
  subst
    (BoundedByᶜ (positivePower ρ (suc n)))
    (scalarMulᶜ-rational r (rationalPower r n))
    (bounded-byᶜ-scale-rational-closed-bound
      r
      (positivePower ρ n)
      ρ
      (rationalGeometricTerm r n)
      r-bound
      (rationalPower-bounded r ρ r-bound n))


record RationalGeometricBound (r : ℚ) : Type₀ where
  no-eta-equality

  field
    ratioBound : ℚ⁺
    ratioBound<1 : radius ratioBound ℚOrder.< Rational.1ℚ
    termBound : RationalClosedBoundᶜ ratioBound r


rationalGeometricMajorizedByPositive :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  SeriesMajorizedBy
    (rationalGeometricTerm r)
    (positiveGeometricTerm (RationalGeometricBound.ratioBound bound))
rationalGeometricMajorizedByPositive r bound =
  termMajorized , majorantNonnegative
  where
  ρ : ℚ⁺
  ρ =
    RationalGeometricBound.ratioBound bound

  r-bound : RationalClosedBoundᶜ ρ r
  r-bound =
    RationalGeometricBound.termBound bound

  termMajorized :
    (m n : ℕ) →
    absᶜ (drop m (rationalGeometricTerm r) n) ≤ᶜ
    drop m (positiveGeometricTerm ρ) n
  termMajorized m n =
    subst2
      (λ x y → absᶜ x ≤ᶜ y)
      (sym (drop-index m (rationalGeometricTerm r) n))
      (sym (drop-index m (positiveGeometricTerm ρ) n))
      (bounded-byᶜ-abs
        (rationalPower-bounded r ρ r-bound (m Nat.+ n)))

  majorantNonnegative :
    (m n : ℕ) →
    0ᶜ ≤ᶜ drop m (positiveGeometricTerm ρ) n
  majorantNonnegative m n =
    subst
      (λ x → 0ᶜ ≤ᶜ x)
      (sym (drop-index m (positiveGeometricTerm ρ) n))
      (positiveGeometricTerm-nonnegative ρ (m Nat.+ n))


RationalGeometricTailBound :
  ℚ →
  (ℚ⁺ → ℕ) →
  Type₀
RationalGeometricTailBound r μ =
  SeriesTailBound (rationalGeometricTerm r) μ


RationalGeometricFiniteTailBound :
  ℚ →
  (ℚ⁺ → ℕ) →
  Type₀
RationalGeometricFiniteTailBound r μ =
  TailBound (rationalGeometricTerm r) μ


rationalGeometricTailBoundFromMajorant :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  {μ : ℚ⁺ → ℕ} →
  TailBound
    (positiveGeometricTerm (RationalGeometricBound.ratioBound bound))
    μ →
  RationalGeometricFiniteTailBound r μ
rationalGeometricTailBoundFromMajorant r bound =
  comparisonTest (rationalGeometricMajorizedByPositive r bound)


rationalGeometricTailBoundFromPositiveData :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  (tailData : PositiveGeometricTailData
    (RationalGeometricBound.ratioBound bound)) →
  RationalGeometricFiniteTailBound r
    (PositiveGeometricTailData.modulus tailData)
rationalGeometricTailBoundFromPositiveData r bound tailData =
  rationalGeometricTailBoundFromMajorant r bound
    (PositiveGeometricTailData.finiteTailBound tailData)


rationalGeometricTailBoundFromRatio :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  RationalGeometricFiniteTailBound
    r
    (positiveGeometricPowerModulus
      (RationalGeometricBound.ratioBound bound)
      (RationalGeometricBound.ratioBound<1 bound))
rationalGeometricTailBoundFromRatio r bound =
  rationalGeometricTailBoundFromMajorant
    r
    bound
    (positiveGeometricFiniteTailBoundFromRatio
      ρ
      ρ<1)
  where
  ρ : ℚ⁺
  ρ =
    RationalGeometricBound.ratioBound bound

  ρ<1 : radius ρ ℚOrder.< Rational.1ℚ
  ρ<1 =
    RationalGeometricBound.ratioBound<1 bound


rationalGeometricSeriesTailBoundFromMajorant :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  {μ : ℚ⁺ → ℕ} →
  TailBound
    (positiveGeometricTerm (RationalGeometricBound.ratioBound bound))
    μ →
  AntitoneNatModulus μ →
  RationalGeometricTailBound r (λ ε → μ (half⁺ ε))
rationalGeometricSeriesTailBoundFromMajorant r bound majorTail μ-antitone =
  tailBound→SeriesTailBound
    (rationalGeometricTailBoundFromMajorant r bound majorTail)
    μ-antitone


rationalGeometricSeriesTailBoundFromPositiveData :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  (tailData : PositiveGeometricTailData (RationalGeometricBound.ratioBound bound)) →
  RationalGeometricTailBound r
    (λ ε →
      PositiveGeometricTailData.modulus
        tailData
        (half⁺ ε))
rationalGeometricSeriesTailBoundFromPositiveData r bound tailData =
  rationalGeometricSeriesTailBoundFromMajorant
    r
    bound
    (PositiveGeometricTailData.finiteTailBound tailData)
    (PositiveGeometricTailData.modulusAntitone tailData)


rationalGeometricSeriesTailBoundFromRatio :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  RationalGeometricTailBound r
    (λ ε →
      positiveGeometricPowerModulus
        (RationalGeometricBound.ratioBound bound)
        (RationalGeometricBound.ratioBound<1 bound)
        (half⁺ ε))
rationalGeometricSeriesTailBoundFromRatio r bound =
  rationalGeometricSeriesTailBoundFromPositiveData
    r
    bound
    (positiveGeometricTailDataFromRatio ρ ρ<1)
  where
  ρ : ℚ⁺
  ρ =
    RationalGeometricBound.ratioBound bound

  ρ<1 : radius ρ ℚOrder.< Rational.1ℚ
  ρ<1 =
    RationalGeometricBound.ratioBound<1 bound


rationalGeometricSumFromMajorant :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  (μ : ℚ⁺ → ℕ) →
  TailBound
    (positiveGeometricTerm (RationalGeometricBound.ratioBound bound))
    μ →
  AntitoneNatModulus μ →
  ℝᶜ
rationalGeometricSumFromMajorant r bound μ majorTail μ-antitone =
  seriesSumFromFiniteTailBound
    (rationalGeometricTerm r)
    μ
    (rationalGeometricTailBoundFromMajorant r bound majorTail)
    μ-antitone


rationalGeometricSumFromPositiveData :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  PositiveGeometricTailData (RationalGeometricBound.ratioBound bound) →
  ℝᶜ
rationalGeometricSumFromPositiveData r bound tailData =
  rationalGeometricSumFromMajorant
    r
    bound
    (PositiveGeometricTailData.modulus tailData)
    (PositiveGeometricTailData.finiteTailBound tailData)
    (PositiveGeometricTailData.modulusAntitone tailData)


rationalGeometricSumFromRatio :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  ℝᶜ
rationalGeometricSumFromRatio r bound =
  rationalGeometricSumFromPositiveData
    r
    bound
    (positiveGeometricTailDataFromRatio ρ ρ<1)
  where
  ρ : ℚ⁺
  ρ =
    RationalGeometricBound.ratioBound bound

  ρ<1 : radius ρ ℚOrder.< Rational.1ℚ
  ρ<1 =
    RationalGeometricBound.ratioBound<1 bound


rationalGeometricConvergesFromPositiveData :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  (tailData : PositiveGeometricTailData
    (RationalGeometricBound.ratioBound bound)) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (rationalGeometricTerm r)
      (PositiveGeometricTailData.modulus tailData)
      (rationalGeometricTailBoundFromPositiveData r bound tailData)
      (PositiveGeometricTailData.modulusAntitone tailData))
    (rationalGeometricSumFromPositiveData r bound tailData)
rationalGeometricConvergesFromPositiveData r bound tailData =
  seriesSumFromFiniteTailBoundConverges
    (rationalGeometricTerm r)
    (PositiveGeometricTailData.modulus tailData)
    (rationalGeometricTailBoundFromPositiveData r bound tailData)
    (PositiveGeometricTailData.modulusAntitone tailData)


rationalGeometricConvergesFromRatio :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (rationalGeometricTerm r)
      (positiveGeometricPowerModulus
        (RationalGeometricBound.ratioBound bound)
        (RationalGeometricBound.ratioBound<1 bound))
      (rationalGeometricTailBoundFromRatio r bound)
      (positiveGeometricPowerModulus-antitone
        (RationalGeometricBound.ratioBound bound)
        (RationalGeometricBound.ratioBound<1 bound)))
    (rationalGeometricSumFromRatio r bound)
rationalGeometricConvergesFromRatio r bound =
  rationalGeometricConvergesFromPositiveData
    r
    bound
    (positiveGeometricTailDataFromRatio ρ ρ<1)
  where
  ρ : ℚ⁺
  ρ =
    RationalGeometricBound.ratioBound bound

  ρ<1 : radius ρ ℚOrder.< Rational.1ℚ
  ρ<1 =
    RationalGeometricBound.ratioBound<1 bound


rationalGeometricTailBoundFromUpperData :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  (upperData : PositiveGeometricTailUpperData
    (RationalGeometricBound.ratioBound bound)) →
  RationalGeometricFiniteTailBound r
    (PositiveGeometricTailUpperData.modulus upperData)
rationalGeometricTailBoundFromUpperData r bound upperData =
  rationalGeometricTailBoundFromPositiveData
    r
    bound
    (positiveGeometricTailDataFromUpperData
      (RationalGeometricBound.ratioBound bound)
      upperData)


rationalGeometricSeriesTailBoundFromUpperData :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  (upperData : PositiveGeometricTailUpperData
    (RationalGeometricBound.ratioBound bound)) →
  RationalGeometricTailBound r
    (λ ε →
      PositiveGeometricTailUpperData.modulus
        upperData
        (half⁺ ε))
rationalGeometricSeriesTailBoundFromUpperData r bound upperData =
  rationalGeometricSeriesTailBoundFromPositiveData
    r
    bound
    (positiveGeometricTailDataFromUpperData
      (RationalGeometricBound.ratioBound bound)
      upperData)


rationalGeometricSumFromUpperData :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  PositiveGeometricTailUpperData (RationalGeometricBound.ratioBound bound) →
  ℝᶜ
rationalGeometricSumFromUpperData r bound upperData =
  rationalGeometricSumFromPositiveData
    r
    bound
    (positiveGeometricTailDataFromUpperData
      (RationalGeometricBound.ratioBound bound)
      upperData)


rationalGeometricSeriesTailBoundFromSegmentData :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  (segmentData : PositiveGeometricSegmentUpperData
    (RationalGeometricBound.ratioBound bound)) →
  RationalGeometricTailBound r
    (λ ε →
      PositiveGeometricSegmentUpperData.modulus
        segmentData
        (half⁺ ε))
rationalGeometricSeriesTailBoundFromSegmentData r bound segmentData =
  rationalGeometricSeriesTailBoundFromPositiveData
    r
    bound
    (positiveGeometricTailDataFromSegmentData
      (RationalGeometricBound.ratioBound bound)
      segmentData)


rationalGeometricSumFromSegmentData :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  PositiveGeometricSegmentUpperData (RationalGeometricBound.ratioBound bound) →
  ℝᶜ
rationalGeometricSumFromSegmentData r bound segmentData =
  rationalGeometricSumFromPositiveData
    r
    bound
    (positiveGeometricTailDataFromSegmentData
      (RationalGeometricBound.ratioBound bound)
      segmentData)


rationalGeometricSeriesTailBoundFromPowerData :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  (powerData : PositiveGeometricPowerScaledUpperData
    (RationalGeometricBound.ratioBound bound)) →
  RationalGeometricTailBound r
    (λ ε →
      PositiveGeometricPowerScaledUpperData.modulus
        powerData
        (half⁺ ε))
rationalGeometricSeriesTailBoundFromPowerData r bound powerData =
  rationalGeometricSeriesTailBoundFromPositiveData
    r
    bound
    (positiveGeometricTailDataFromPowerData
      (RationalGeometricBound.ratioBound bound)
      powerData)


rationalGeometricSumFromPowerData :
  (r : ℚ) →
  (bound : RationalGeometricBound r) →
  PositiveGeometricPowerScaledUpperData (RationalGeometricBound.ratioBound bound) →
  ℝᶜ
rationalGeometricSumFromPowerData r bound powerData =
  rationalGeometricSumFromPositiveData
    r
    bound
    (positiveGeometricTailDataFromPowerData
      (RationalGeometricBound.ratioBound bound)
      powerData)


rationalGeometricCauchyApproximation :
  (r : ℚ) →
  (μ : ℚ⁺ → ℕ) →
  RationalGeometricTailBound r μ →
  MetricCauchy.CauchyApproximation CauchyRealsMetricSpace
rationalGeometricCauchyApproximation r μ tailBound =
  seriesCauchyApproximationFromTailBound
    (rationalGeometricTerm r)
    μ
    tailBound


rationalGeometricSum :
  (r : ℚ) →
  (μ : ℚ⁺ → ℕ) →
  RationalGeometricTailBound r μ →
  ℝᶜ
rationalGeometricSum r μ tailBound =
  seriesSum (rationalGeometricTerm r) μ tailBound


rationalGeometricConverges :
  (r : ℚ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : RationalGeometricTailBound r μ) →
  MetricCauchy.ConvergesTo
    (rationalGeometricCauchyApproximation r μ tailBound)
    (rationalGeometricSum r μ tailBound)
rationalGeometricConverges r μ tailBound =
  seriesSumConverges (rationalGeometricTerm r) μ tailBound


RationalGeometricConvergesWith :
  ℚ →
  Type₀
RationalGeometricConvergesWith r =
  Σ[ μ ∈ (ℚ⁺ → ℕ) ] RationalGeometricTailBound r μ
