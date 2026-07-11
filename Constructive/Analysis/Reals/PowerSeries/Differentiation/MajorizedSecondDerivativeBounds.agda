{-

Explicit rational bounds for second-derivative partial sums

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Differentiation.MajorizedSecondDerivativeBounds where

open import Cubical.Foundations.Prelude

import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sum as Sum using (inl ; inr)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-trans)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (absᶜ ; ≤ᶜabsᶜ-left ; ≤ᶜabsᶜ-right)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using (PowerSeriesMajorizedOnBall)
import Constructive.Analysis.Reals.PowerSeries.Majorant as Majorant
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.SecondDerivativeBounds
  using (PowerSeriesSecondDerivativePartialSumsBoundOnBall)
open import Constructive.Analysis.Reals.Series
  using
    ( SeriesMajorizedBy
    ; TailBound
    ; comparisonTest
    ; partialSum
    ; partialSum-append
    ; partialSum-snoc
    ; tailSum
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  bounded-byᶜ-from-abs≤ :
    {κ : ℚ⁺} →
    {x y : ℝᶜ} →
    absᶜ x ≤ᶜ y →
    BoundedByᶜ κ y →
    BoundedByᶜ κ x
  bounded-byᶜ-from-abs≤ {κ = κ} {x = x} {y = y} abs≤y y-bound =
    bounded-byᶜ upperBound lowerBound
    where
    abs≤κ : absᶜ x ≤ᶜ rational (radius κ)
    abs≤κ =
      ≤ᶜ-trans
        {x = absᶜ x}
        {y = y}
        {z = rational (radius κ)}
        abs≤y
        (upperᶜ y-bound)

    upperBound : x ≤ᶜ rational (radius κ)
    upperBound =
      ≤ᶜ-trans
        {x = x}
        {y = absᶜ x}
        {z = rational (radius κ)}
        (≤ᶜabsᶜ-left x)
        abs≤κ

    lowerBound : (-ᶜ x) ≤ᶜ rational (radius κ)
    lowerBound =
      ≤ᶜ-trans
        {x = -ᶜ x}
        {y = absᶜ x}
        {z = rational (radius κ)}
        (≤ᶜabsᶜ-right x)
        abs≤κ

  positivePrefixBound :
    (ℕ → ℚ⁺) →
    ℕ →
    ℚ⁺
  positivePrefixBound β zero =
    1⁺
  positivePrefixBound β (suc n) =
    positivePrefixBound β n +⁺ β n


powerSeriesSecondDerivativePartialSumsBoundMajorizedRationalΓ :
  (ℕ → ℚ⁺) →
  (ℚ⁺ → ℕ) →
  ℚ⁺
powerSeriesSecondDerivativePartialSumsBoundMajorizedRationalΓ β ν =
  positivePrefixBound β (ν 1⁺) +⁺ 1⁺


private
  abstract
    seriesTermBoundFromMajorizedByRationalBound :
      {u v : ℕ → ℝᶜ} →
      {β : ℕ → ℚ⁺} →
      SeriesMajorizedBy u v →
      ((n : ℕ) → BoundedByᶜ (β n) (v n)) →
      (n : ℕ) →
      BoundedByᶜ (β n) (u n)
    seriesTermBoundFromMajorizedByRationalBound majorized β-bound n =
      bounded-byᶜ-from-abs≤
        (SeriesMajorizedBy.termMajorized majorized zero n)
        (β-bound n)

    partialSumBoundFromMajorizedByRationalBounds :
      {u v : ℕ → ℝᶜ} →
      (β : ℕ → ℚ⁺) →
      SeriesMajorizedBy u v →
      ((n : ℕ) → BoundedByᶜ (β n) (v n)) →
      (n : ℕ) →
      BoundedByᶜ (positivePrefixBound β n) (partialSum u n)
    partialSumBoundFromMajorizedByRationalBounds β majorized β-bound zero =
      bounded-byᶜ-zero 1⁺
    partialSumBoundFromMajorizedByRationalBounds
        {u = u}
        β
        majorized
        β-bound
        (suc n) =
      subst
        (BoundedByᶜ (positivePrefixBound β (suc n)))
        (sym (partialSum-snoc u n))
        (bounded-byᶜ-add
          (positivePrefixBound β n)
          (β n)
          (partialSum u n)
          (u n)
          (partialSumBoundFromMajorizedByRationalBounds
            β
            majorized
            β-bound
            n)
          (seriesTermBoundFromMajorizedByRationalBound
            majorized
            β-bound
            n))

    prefix≤next :
      (β : ℕ → ℚ⁺) →
      (n : ℕ) →
      radius (positivePrefixBound β n) ℚOrder.≤
      radius (positivePrefixBound β (suc n))
    prefix≤next β n =
      Rational.<→≤
        {p = radius (positivePrefixBound β n)}
        {q = radius (positivePrefixBound β (suc n))}
        (summand-left<sum (positivePrefixBound β n) (β n))

    prefix≤prefix+1 :
      (β : ℕ → ℚ⁺) →
      (cutoff : ℕ) →
      radius (positivePrefixBound β cutoff) ℚOrder.≤
      radius (positivePrefixBound β cutoff +⁺ 1⁺)
    prefix≤prefix+1 β cutoff =
      Rational.<→≤
        {p = radius (positivePrefixBound β cutoff)}
        {q = radius (positivePrefixBound β cutoff +⁺ 1⁺)}
        (summand-left<sum (positivePrefixBound β cutoff) 1⁺)

    partialSumBoundBelowPrefix :
      {u v : ℕ → ℝᶜ} →
      (β : ℕ → ℚ⁺) →
      SeriesMajorizedBy u v →
      ((n : ℕ) → BoundedByᶜ (β n) (v n)) →
      (cutoff n : ℕ) →
      NatOrder._≤_ n cutoff →
      BoundedByᶜ (positivePrefixBound β cutoff) (partialSum u n)
    partialSumBoundBelowPrefix
        {u = u}
        β
        majorized
        β-bound
        zero
        n
        n≤0 =
      subst
        (λ k →
          BoundedByᶜ (positivePrefixBound β zero) (partialSum u k))
        (sym (NatOrder.≤0→≡0 n≤0))
        (bounded-byᶜ-zero 1⁺)
    partialSumBoundBelowPrefix
        {u = u}
        β
        majorized
        β-bound
        (suc cutoff)
        n
        n≤suc =
      Sum.rec left right (NatOrder.≤-split n≤suc)
      where
      left :
        NatOrder._<_ n (suc cutoff) →
        BoundedByᶜ (positivePrefixBound β (suc cutoff)) (partialSum u n)
      left n<suc =
        bounded-byᶜ-monotone
          (prefix≤next β cutoff)
          (partialSumBoundBelowPrefix
            β
            majorized
            β-bound
            cutoff
            n
            (NatOrder.pred-≤-pred n<suc))

      right :
        n ≡ suc cutoff →
        BoundedByᶜ (positivePrefixBound β (suc cutoff)) (partialSum u n)
      right n≡suc =
        subst
          (λ k →
            BoundedByᶜ
              (positivePrefixBound β (suc cutoff))
              (partialSum u k))
          (sym n≡suc)
          (partialSumBoundFromMajorizedByRationalBounds
            β
            majorized
            β-bound
            (suc cutoff))

    partialSumBoundFromMajorizedRationalTail :
      {u v : ℕ → ℝᶜ} →
      {ν : ℚ⁺ → ℕ} →
      (β : ℕ → ℚ⁺) →
      SeriesMajorizedBy u v →
      ((n : ℕ) → BoundedByᶜ (β n) (v n)) →
      TailBound v ν →
      (n : ℕ) →
      BoundedByᶜ
        (powerSeriesSecondDerivativePartialSumsBoundMajorizedRationalΓ β ν)
        (partialSum u n)
    partialSumBoundFromMajorizedRationalTail
        {u = u}
        {ν = ν}
        β
        majorized
        β-bound
        v-tail
        n =
      Sum.rec left right (NatOrder.splitℕ-≤ n (ν 1⁺))
      where
      cutoff : ℕ
      cutoff =
        ν 1⁺

      left :
        NatOrder._≤_ n cutoff →
        BoundedByᶜ
          (powerSeriesSecondDerivativePartialSumsBoundMajorizedRationalΓ β ν)
          (partialSum u n)
      left n≤cutoff =
        bounded-byᶜ-monotone
          (prefix≤prefix+1 β cutoff)
          (partialSumBoundBelowPrefix
            β
            majorized
            β-bound
            cutoff
            n
            n≤cutoff)

      right :
        NatOrder._<_ cutoff n →
        BoundedByᶜ
          (powerSeriesSecondDerivativePartialSumsBoundMajorizedRationalΓ β ν)
          (partialSum u n)
      right cutoff<n =
        subst
          (BoundedByᶜ (positivePrefixBound β cutoff +⁺ 1⁺))
          (sym sum-path)
          combined
        where

        cutoff≤n : NatOrder._≤_ cutoff n
        cutoff≤n =
          NatOrder.<-weaken cutoff<n

        k : ℕ
        k =
          cutoff≤n .fst

        cutoff+k≡n : cutoff Nat.+ k ≡ n
        cutoff+k≡n =
          Nat.+-comm cutoff k ∙ cutoff≤n .snd

        sum-path :
          partialSum u n ≡ partialSum u cutoff +ᶜ tailSum u cutoff k
        sum-path =
          sym (cong (partialSum u) cutoff+k≡n) ∙
          partialSum-append u cutoff k

        combined :
          BoundedByᶜ
            (positivePrefixBound β cutoff +⁺ 1⁺)
            (partialSum u cutoff +ᶜ tailSum u cutoff k)
        combined =
          bounded-byᶜ-add
            (positivePrefixBound β cutoff)
            1⁺
            (partialSum u cutoff)
            (tailSum u cutoff k)
            (partialSumBoundFromMajorizedByRationalBounds
              β
              majorized
              β-bound
              cutoff)
            (comparisonTest majorized v-tail 1⁺ cutoff k NatOrder.≤-refl)

    powerSeriesPartialSumsBoundFromMajorizedRationalTail :
      {b : PowerSeries} →
      {ρ : ℚ⁺} →
      {v : ℕ → ℝᶜ} →
      {ν : ℚ⁺ → ℕ} →
      {β : ℕ → ℚ⁺} →
      PowerSeriesMajorizedOnBall b ρ v ν →
      ((n : ℕ) → BoundedByᶜ (β n) (v n)) →
      (y : ℝᶜ) →
      BoundedByᶜ ρ y →
      (n : ℕ) →
      BoundedByᶜ
        (powerSeriesSecondDerivativePartialSumsBoundMajorizedRationalΓ β ν)
        (powerSeriesPartialSum b y n)
    powerSeriesPartialSumsBoundFromMajorizedRationalTail
        {b = b}
        {ρ = ρ}
        {v = v}
        {ν = ν}
        {β = β}
        majorized
        β-bound
        y
        y-bound
        n =
      partialSumBoundFromMajorizedRationalTail
        {u = powerSeriesTerm b y}
        {v = v}
        {ν = ν}
        β
        (Majorant.PowerSeriesMajorizedOnBall.termMajorized
          {a = b}
          {ρ = ρ}
          {v = v}
          {μ = ν}
          majorized
          y
          y-bound)
        β-bound
        (Majorant.PowerSeriesMajorizedOnBall.majorTail
          {a = b}
          {ρ = ρ}
          {v = v}
          {μ = ν}
          majorized)
        n


powerSeriesPartialSumsBoundOnBallFromMajorizedRationalBounds :
  {b : PowerSeries} →
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  {β : ℕ → ℚ⁺} →
  PowerSeriesMajorizedOnBall b ρ v ν →
  ((n : ℕ) → BoundedByᶜ (β n) (v n)) →
  Σ[ Γ ∈ ℚ⁺ ]
    ((y : ℝᶜ) →
    BoundedByᶜ ρ y →
    (n : ℕ) →
    BoundedByᶜ Γ (powerSeriesPartialSum b y n))
powerSeriesPartialSumsBoundOnBallFromMajorizedRationalBounds
    {b = b}
    {ρ = ρ}
    {v = v}
    {ν = ν}
    {β = β}
    majorized
    β-bound =
  powerSeriesSecondDerivativePartialSumsBoundMajorizedRationalΓ β ν ,
  powerSeriesPartialSumsBoundFromMajorizedRationalTail
    {b = b}
    {ρ = ρ}
    {v = v}
    {ν = ν}
    {β = β}
    majorized
    β-bound


powerSeriesSecondDerivativePartialSumsBoundOnBallFromMajorizedRationalBounds :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  {β : ℕ → ℚ⁺} →
  PowerSeriesMajorizedOnBall
    (derivativePowerSeries (derivativePowerSeries a))
    ρ
    v
    ν →
  ((n : ℕ) → BoundedByᶜ (β n) (v n)) →
  PowerSeriesSecondDerivativePartialSumsBoundOnBall a ρ
powerSeriesSecondDerivativePartialSumsBoundOnBallFromMajorizedRationalBounds
    {a = a}
    {ρ = ρ}
    {v = v}
    {ν = ν}
    {β = β}
    majorized
    β-bound =
  powerSeriesPartialSumsBoundOnBallFromMajorizedRationalBounds
    {b = derivativePowerSeries (derivativePowerSeries a)}
    {ρ = ρ}
    {v = v}
    {ν = ν}
    {β = β}
    majorized
    β-bound
