{-

Majorants for power-series convergence

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Majorant where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (scalarMulᶜ-nonnegative ; scalarMulᶜ-pres≤ᶜ-scalar)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
  using (scalarMulᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-trans)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude using (absᶜ)
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Quantitative
  using (bounded-byᶜ-abs≤rational)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


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
      AntitoneNatModulus μ


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
    AntitoneNatModulus μ
  majorAntitone majorized =
    majorized .snd .snd

  abstract
    majorantNonnegative :
      {a : PowerSeries} {ρ : ℚ⁺} {v : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
      PowerSeriesMajorizedOnBall a ρ v μ →
      (n : ℕ) →
      0ᶜ ≤ᶜ v n
    majorantNonnegative {a = a} {ρ = ρ} {v = v} {μ = μ} majorized n =
      SeriesMajorizedBy.majorantNonnegative
        {u = powerSeriesTerm a 0ᶜ}
        {v = v}
        (termMajorized
          {a = a}
          {ρ = ρ}
          {v = v}
          {μ = μ}
          majorized
          0ᶜ
          (bounded-byᶜ-zero ρ))
        zero
        n

    shiftedScalarScaleMajorantNonnegative :
      {a : PowerSeries} {ρ : ℚ⁺} {v : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
      (q : ℚ) →
      Rational.0ℚ ℚOrder.≤ q →
      PowerSeriesMajorizedOnBall a ρ v μ →
      (n : ℕ) →
      0ᶜ ≤ᶜ scalarMulᶜ q (v (suc n))
    shiftedScalarScaleMajorantNonnegative
        {a = a}
        {ρ = ρ}
        {v = v}
        {μ = μ}
        q
        0≤q
        majorized
        n =
      scalarMulᶜ-nonnegative
        q
        0≤q
        {x = v (suc n)}
        (majorantNonnegative
          {a = a}
          {ρ = ρ}
          {v = v}
          {μ = μ}
          majorized
          (suc n))

    shiftedPositiveScalarScaleMajorantNonnegative :
      {a : PowerSeries} {ρ : ℚ⁺} {v : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
      (q : ℚ) →
      Rational.0ℚ ℚOrder.< q →
      PowerSeriesMajorizedOnBall a ρ v μ →
      (n : ℕ) →
      0ᶜ ≤ᶜ scalarMulᶜ q (v (suc n))
    shiftedPositiveScalarScaleMajorantNonnegative
        {a = a}
        {ρ = ρ}
        {v = v}
        {μ = μ}
        q
        0<q
        majorized
        n =
      shiftedScalarScaleMajorantNonnegative
        {a = a}
        {ρ = ρ}
        {v = v}
        {μ = μ}
        q
        (Rational.<→≤ {p = Rational.0ℚ} {q = q} 0<q)
        majorized
        n

    shiftedScalarScaleMajorant≤ :
      {a : PowerSeries} {ρ : ℚ⁺} {v : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
      (q r : ℚ) →
      q ℚOrder.≤ r →
      PowerSeriesMajorizedOnBall a ρ v μ →
      (n : ℕ) →
      scalarMulᶜ q (v (suc n)) ≤ᶜ scalarMulᶜ r (v (suc n))
    shiftedScalarScaleMajorant≤
        {a = a}
        {ρ = ρ}
        {v = v}
        {μ = μ}
        q
        r
        q≤r
        majorized
        n =
      scalarMulᶜ-pres≤ᶜ-scalar
        {a = q}
        {b = r}
        q≤r
        {x = v (suc n)}
        (majorantNonnegative
          {a = a}
          {ρ = ρ}
          {v = v}
          {μ = μ}
          majorized
          (suc n))


powerSeriesMajorizedOnBall-cong :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  ((n : ℕ) → a n ≡ b n) →
  PowerSeriesMajorizedOnBall a ρ v μ →
  PowerSeriesMajorizedOnBall b ρ v μ
powerSeriesMajorizedOnBall-cong
  {a = a}
  {b = b}
  {ρ = ρ}
  {v = v}
  {μ = μ}
  coeff
  majorized =
  (λ h h-bound →
    subst
      (λ u → SeriesMajorizedBy u v)
      (powerSeriesTerm-cong-coefficients {a = a} {b = b} coeff h)
      (PowerSeriesMajorizedOnBall.termMajorized
        {a = a}
        {ρ = ρ}
        {v = v}
        {μ = μ}
        majorized
        h
        h-bound)) ,
  PowerSeriesMajorizedOnBall.majorTail
    {a = a}
    {ρ = ρ}
    {v = v}
    {μ = μ}
    majorized ,
  PowerSeriesMajorizedOnBall.majorAntitone
    {a = a}
    {ρ = ρ}
    {v = v}
    {μ = μ}
    majorized


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
  AntitoneNatModulus μ →
  PowerSeriesMajorizedOnBall a ρ v μ
powerSeriesMajorizedOnBallFromTermBounds
  {a = a}
  {v = v}
  termBounds
  majorantNonnegative
  majorTail
  majorAntitone =
  (λ h h-bound →
    seriesMajorizedByTerms
      {u = powerSeriesTerm a h}
      {v = v}
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
  AntitoneNatModulus μ →
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
        (bounded-byᶜ-abs≤rational
          {κ = κ n}
          {x = powerSeriesTerm a h n}
          (termBounds h h-bound n))
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
  hasPowerSeriesOnBallWith
    {a = a}
    {ρ = ρ}
    {μ = μ}
    (PowerSeriesMajorizedOnBall.majorAntitone
      {a = a} {ρ = ρ} {v = v} {μ = μ}
      majorized)
    (λ (h : ℝᶜ) (h-bound : BoundedByᶜ ρ h) →
      comparisonTest
        {u = powerSeriesTerm a h}
        {v = v}
        (PowerSeriesMajorizedOnBall.termMajorized
          {a = a} {ρ = ρ} {v = v} {μ = μ}
          majorized h h-bound)
        {μ = μ}
        (PowerSeriesMajorizedOnBall.majorTail
          {a = a} {ρ = ρ} {v = v} {μ = μ}
          majorized))


majorizedOnBall→hasPowerSeriesOnBall :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  PowerSeriesMajorizedOnBall a ρ v μ →
  HasPowerSeriesOnBall a ρ
majorizedOnBall→hasPowerSeriesOnBall {a = a} {ρ = ρ} {v = v} {μ = μ} majorized =
  μ ,
  majorizedOnBall→hasPowerSeriesOnBallWith
    {a = a}
    {ρ = ρ}
    {v = v}
    {μ = μ}
    majorized
