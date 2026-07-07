{-

Majorants for power-series convergence

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Majorant where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-trans)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude using (absᶜ)
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Majorant
  using (bounded-byᶜ-abs)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals


PowerSeriesMajorizedOnBall :
  (a : PowerSeries) →
  ℚ⁺ →
  (ℕ → ℝᶜ) →
  (ℚ⁺ → ℕ) →
  Type₀
PowerSeriesMajorizedOnBall a ρ v μ =
  Σ[ termMajorized ∈
      ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      SeriesMajorizedBy (powerSeriesTerm a h) v) ]
    Σ[ majorTail ∈ TailBound v μ ]
      AntitoneTailModulus μ


module PowerSeriesMajorizedOnBall where
  termMajorized :
    {a : PowerSeries} {ρ : ℚ⁺} {v : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
    PowerSeriesMajorizedOnBall a ρ v μ →
    (h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy (powerSeriesTerm a h) v
  termMajorized majorized =
    majorized .fst

  majorTail :
    {a : PowerSeries} {ρ : ℚ⁺} {v : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
    PowerSeriesMajorizedOnBall a ρ v μ →
    TailBound v μ
  majorTail majorized =
    majorized .snd .fst

  majorAntitone :
    {a : PowerSeries} {ρ : ℚ⁺} {v : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
    PowerSeriesMajorizedOnBall a ρ v μ →
    AntitoneTailModulus μ
  majorAntitone majorized =
    majorized .snd .snd


powerSeriesMajorizedOnBallFromTermBounds :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    absᶜ (powerSeriesTerm a h n) ≤ᶜ v n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ v n) →
  TailBound v μ →
  AntitoneTailModulus μ →
  PowerSeriesMajorizedOnBall a ρ v μ
powerSeriesMajorizedOnBallFromTermBounds
  termBounds
  majorantNonnegative
  majorTail
  majorAntitone =
  (λ h h-bound →
    seriesMajorizedByTerms
      (termBounds h h-bound)
      majorantNonnegative) ,
  majorTail ,
  majorAntitone


powerSeriesMajorizedOnBallFromBoundedTerms :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {κ : ℕ → ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  ((n : ℕ) → rational (radius (κ n)) ≤ᶜ v n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ v n) →
  TailBound v μ →
  AntitoneTailModulus μ →
  PowerSeriesMajorizedOnBall a ρ v μ
powerSeriesMajorizedOnBallFromBoundedTerms
  {a = a}
  {ρ = ρ}
  {κ = κ}
  {v = v}
  {μ = μ}
  termBounds
  bound≤majorant
  majorantNonnegative
  majorTail
  majorAntitone =
  powerSeriesMajorizedOnBallFromTermBounds
    {a = a}
    {ρ = ρ}
    {v = v}
    {μ = μ}
    (λ h h-bound n →
      ≤ᶜ-trans
        {x = absᶜ (powerSeriesTerm a h n)}
        {y = rational (radius (κ n))}
        {z = v n}
        (bounded-byᶜ-abs (termBounds h h-bound n))
        (bound≤majorant n))
    majorantNonnegative
    majorTail
    majorAntitone


majorizedOnBall→hasPowerSeriesOnBallWith :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  PowerSeriesMajorizedOnBall a ρ v μ →
  HasPowerSeriesOnBallWith a ρ μ
majorizedOnBall→hasPowerSeriesOnBallWith {a = a} {ρ = ρ} {v = v} {μ = μ}
    majorized =
  record
    { antitoneModulus =
        PowerSeriesMajorizedOnBall.majorAntitone
          {a = a} {ρ = ρ} {v = v} {μ = μ}
          majorized
    ; tailBound =
        λ h h-bound →
          comparisonTest
            (PowerSeriesMajorizedOnBall.termMajorized
              {a = a} {ρ = ρ} {v = v} {μ = μ}
              majorized h h-bound)
            (PowerSeriesMajorizedOnBall.majorTail
              {a = a} {ρ = ρ} {v = v} {μ = μ}
              majorized)
    }


majorizedOnBall→hasPowerSeriesOnBall :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  PowerSeriesMajorizedOnBall a ρ v μ →
  HasPowerSeriesOnBall a ρ
majorizedOnBall→hasPowerSeriesOnBall {μ = μ} majorized =
  μ , majorizedOnBall→hasPowerSeriesOnBallWith majorized


hasPowerSeriesOnBallWithFromTermBounds :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    absᶜ (powerSeriesTerm a h n) ≤ᶜ v n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ v n) →
  TailBound v μ →
  AntitoneTailModulus μ →
  HasPowerSeriesOnBallWith a ρ μ
hasPowerSeriesOnBallWithFromTermBounds
  {a = a}
  {ρ = ρ}
  {v = v}
  {μ = μ}
  termBounds
  majorantNonnegative
  majorTail
  majorAntitone =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (powerSeriesMajorizedOnBallFromTermBounds
      {a = a}
      {ρ = ρ}
      {v = v}
      {μ = μ}
      termBounds
      majorantNonnegative
      majorTail
      majorAntitone)


hasPowerSeriesOnBallFromTermBounds :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    absᶜ (powerSeriesTerm a h n) ≤ᶜ v n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ v n) →
  TailBound v μ →
  AntitoneTailModulus μ →
  HasPowerSeriesOnBall a ρ
hasPowerSeriesOnBallFromTermBounds
  {a = a}
  {ρ = ρ}
  {v = v}
  {μ = μ}
  termBounds
  majorantNonnegative
  majorTail
  majorAntitone =
  μ ,
  hasPowerSeriesOnBallWithFromTermBounds
    {a = a}
    {ρ = ρ}
    {v = v}
    {μ = μ}
    termBounds
    majorantNonnegative
    majorTail
    majorAntitone


hasPowerSeriesOnBallWithFromBoundedTerms :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {κ : ℕ → ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  ((n : ℕ) → rational (radius (κ n)) ≤ᶜ v n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ v n) →
  TailBound v μ →
  AntitoneTailModulus μ →
  HasPowerSeriesOnBallWith a ρ μ
hasPowerSeriesOnBallWithFromBoundedTerms
  {a = a}
  {ρ = ρ}
  {κ = κ}
  {v = v}
  {μ = μ}
  termBounds
  bound≤majorant
  majorantNonnegative
  majorTail
  majorAntitone =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (powerSeriesMajorizedOnBallFromBoundedTerms
      {a = a}
      {ρ = ρ}
      {κ = κ}
      {v = v}
      {μ = μ}
      termBounds
      bound≤majorant
      majorantNonnegative
      majorTail
      majorAntitone)


hasPowerSeriesOnBallFromBoundedTerms :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {κ : ℕ → ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  ((n : ℕ) → rational (radius (κ n)) ≤ᶜ v n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ v n) →
  TailBound v μ →
  AntitoneTailModulus μ →
  HasPowerSeriesOnBall a ρ
hasPowerSeriesOnBallFromBoundedTerms
  {a = a}
  {ρ = ρ}
  {κ = κ}
  {v = v}
  {μ = μ}
  termBounds
  bound≤majorant
  majorantNonnegative
  majorTail
  majorAntitone =
  μ ,
  hasPowerSeriesOnBallWithFromBoundedTerms
    {a = a}
    {ρ = ρ}
    {κ = κ}
    {v = v}
    {μ = μ}
    termBounds
    bound≤majorant
    majorantNonnegative
    majorTail
    majorAntitone
