{-

Series comparison infrastructure for HoTT Cauchy reals

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Comparison where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Data.Sum using (inl ; inr)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Base
import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
  using (≤ᶜ-add ; negᶜ-pres≤ᶜ)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace

open import Constructive.Analysis.Reals.Series.Finite
open import Constructive.Analysis.Reals.Series.Cauchy
open import Constructive.Analysis.Reals.Series.Tail

SeriesMajorizedBy :
  (u v : ℕ → ℝᶜ) →
  Type₀
SeriesMajorizedBy u v =
  Σ[ termMajorized ∈
      ((m n : ℕ) → absᶜ (drop m u n) ≤ᶜ drop m v n) ]
    ((m n : ℕ) → 0ᶜ ≤ᶜ drop m v n)


module SeriesMajorizedBy where
  termMajorized :
    {u v : ℕ → ℝᶜ} →
    SeriesMajorizedBy u v →
    (m n : ℕ) →
    absᶜ (drop m u n) ≤ᶜ drop m v n
  termMajorized majorized =
    majorized .fst

  majorantNonnegative :
    {u v : ℕ → ℝᶜ} →
    SeriesMajorizedBy u v →
    (m n : ℕ) →
    0ᶜ ≤ᶜ drop m v n
  majorantNonnegative majorized =
    majorized .snd


seriesMajorizedByTerms :
  {u v : ℕ → ℝᶜ} →
  ((n : ℕ) → absᶜ (u n) ≤ᶜ v n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ v n) →
  SeriesMajorizedBy u v
seriesMajorizedByTerms {u = u} {v = v} term≤ 0≤major =
  termMajorized , majorantNonnegative
  where
  termMajorized :
    (m n : ℕ) →
    absᶜ (drop m u n) ≤ᶜ drop m v n
  termMajorized m n =
    subst2
      (λ x y → absᶜ x ≤ᶜ y)
      (sym (drop-index m u n))
      (sym (drop-index m v n))
      (term≤ (m Nat.+ n))

  majorantNonnegative :
    (m n : ℕ) →
    0ᶜ ≤ᶜ drop m v n
  majorantNonnegative m n =
    subst
      (λ y → 0ᶜ ≤ᶜ y)
      (sym (drop-index m v n))
      (0≤major (m Nat.+ n))


tailSum-comparison :
  {u v : ℕ → ℝᶜ} →
  SeriesMajorizedBy u v →
  (m k : ℕ) →
  absᶜ (tailSum u m k) ≤ᶜ tailSum v m k
tailSum-comparison {u = u} {v = v} majorized m k =
  partialSum-comparison
    (drop m u)
    (drop m v)
    (SeriesMajorizedBy.termMajorized majorized m)
    k


comparisonTest :
  {u v : ℕ → ℝᶜ} →
  SeriesMajorizedBy u v →
  {μ : ℚ⁺ → ℕ} →
  TailBound v μ →
  TailBound u μ
comparisonTest {u = u} {v = v} majorized {μ = μ} v-tail ε m k μ≤m =
  bounded-byᶜ upperBound lowerBound
  where
  tail : ℝᶜ
  tail =
    tailSum u m k

  majorTail : ℝᶜ
  majorTail =
    tailSum v m k

  v-bound : BoundedByᶜ ε majorTail
  v-bound =
    v-tail ε m k μ≤m

  absTail≤majorTail : absᶜ tail ≤ᶜ majorTail
  absTail≤majorTail =
    tailSum-comparison majorized m k

  absTail≤ε : absᶜ tail ≤ᶜ rational (radius ε)
  absTail≤ε =
    ≤ᶜ-trans
      {x = absᶜ tail}
      {y = majorTail}
      {z = rational (radius ε)}
      absTail≤majorTail
      (upperᶜ v-bound)

  upperBound : tail ≤ᶜ rational (radius ε)
  upperBound =
    ≤ᶜ-trans
      {x = tail}
      {y = absᶜ tail}
      {z = rational (radius ε)}
      (≤ᶜabsᶜ-left tail)
      absTail≤ε

  lowerBound : (-ᶜ tail) ≤ᶜ rational (radius ε)
  lowerBound =
    ≤ᶜ-trans
      {x = -ᶜ tail}
      {y = absᶜ tail}
      {z = rational (radius ε)}
      (≤ᶜabsᶜ-right tail)
      absTail≤ε


comparisonSeriesTailBound :
  {u v : ℕ → ℝᶜ} →
  SeriesMajorizedBy u v →
  {μ : ℚ⁺ → ℕ} →
  TailBound v μ →
  AntitoneTailModulus μ →
  SeriesTailBound u (λ ε → μ (half⁺ ε))
comparisonSeriesTailBound majorized v-tail μ-antitone =
  tailBound→SeriesTailBound
    (comparisonTest majorized v-tail)
    μ-antitone


comparisonSeriesSum :
  {u v : ℕ → ℝᶜ} →
  SeriesMajorizedBy u v →
  (μ : ℚ⁺ → ℕ) →
  TailBound v μ →
  AntitoneTailModulus μ →
  ℝᶜ
comparisonSeriesSum {u = u} majorized μ v-tail μ-antitone =
  seriesSumFromFiniteTailBound
    u
    μ
    (comparisonTest majorized v-tail)
    μ-antitone
