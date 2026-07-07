{-

Tail bound and public theorem for derivative convergence on strict subballs.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.StrictSubball.OnBall.Tail where

open import Cubical.Foundations.Prelude

import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (_,_)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
  using (0ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-trans)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using
    ( BoundedByᶜ
    ; bounded-byᶜ
    ; upperᶜ
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using
    ( absᶜ
    ; ≤ᶜabsᶜ-left
    ; ≤ᶜabsᶜ-right
    )
open import Constructive.Analysis.Reals.Series
  using
    ( TailBound
    ; drop
    ; partialSum-comparison
    ; tailSum
    )
open import Constructive.Analysis.Reals.Sequences.Base
  using
    ( maxModulus-antitone
    ; maxModulus-left≤
    ; maxModulus-right≤
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.StrictSubball.OnBall.Base
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.StrictSubball.OnBall.Estimate


derivativeStrictSubballTailBoundFromOnBall :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  HasPowerSeriesOnBallWith a σ μ →
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  TailBound
    (powerSeriesTerm (derivativePowerSeries a) h)
    (derivativeStrictSubballFromOnBallModulus ρ<σ μ)
derivativeStrictSubballTailBoundFromOnBall
    {a = a}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    ρ<σ
    convergence
    h
    h-bound
    ε
    m
    k
    modulus≤m =
  bounded-byᶜ upperBound lowerBound
  where
  derivativeTerms : ℕ → ℝᶜ
  derivativeTerms =
    powerSeriesTerm (derivativePowerSeries a) h

  majorant : ℕ → ℝᶜ
  majorant =
    derivativeStrictSubballFromOnBallMajorant ρ<σ

  geometricModulus : ℚ⁺ → ℕ
  geometricModulus =
    derivativeStrictSubballFromOnBallGeometricModulus ρ<σ

  μ1≤m : NatOrder._≤_ (μ 1⁺) m
  μ1≤m =
    NatOrder.≤-trans
      (maxModulus-left≤ (λ _ → μ 1⁺) geometricModulus ε)
      modulus≤m

  geom≤m : NatOrder._≤_ (geometricModulus ε) m
  geom≤m =
    NatOrder.≤-trans
      (maxModulus-right≤ (λ _ → μ 1⁺) geometricModulus ε)
      modulus≤m

  majorantTailBound : BoundedByᶜ ε (tailSum majorant m k)
  majorantTailBound =
    derivativeStrictSubballFromOnBallMajorTail ρ<σ ε m k geom≤m

  n≤sucn : (n : ℕ) → NatOrder._≤_ n (suc n)
  n≤sucn n =
    suc zero , refl

  m≤m+j : (j : ℕ) → NatOrder._≤_ m (m Nat.+ j)
  m≤m+j j =
    j , Nat.+-comm j m

  μ1≤m+j : (j : ℕ) → NatOrder._≤_ (μ 1⁺) (m Nat.+ j)
  μ1≤m+j j =
    NatOrder.≤-trans μ1≤m (m≤m+j j)

  μ1≤sucm+j : (j : ℕ) → NatOrder._≤_ (μ 1⁺) (suc (m Nat.+ j))
  μ1≤sucm+j j =
    NatOrder.≤-trans (μ1≤m+j j) (n≤sucn (m Nat.+ j))

  droppedTerm≤Majorant :
    (j : ℕ) →
    absᶜ (drop m derivativeTerms j) ≤ᶜ drop m majorant j
  droppedTerm≤Majorant j =
    derivativeStrictSubballDroppedTerm≤Majorant
      {a = a}
      {ρ = ρ}
      {σ = σ}
      {μ = μ}
      ρ<σ
      convergence
      h
      h-bound
      m
      j
      (μ1≤sucm+j j)

  absTail≤majorantTail :
    absᶜ (tailSum derivativeTerms m k) ≤ᶜ tailSum majorant m k
  absTail≤majorantTail =
    partialSum-comparison
      (drop m derivativeTerms)
      (drop m majorant)
      droppedTerm≤Majorant
      k

  absTail≤ε : absᶜ (tailSum derivativeTerms m k) ≤ᶜ rational (radius ε)
  absTail≤ε =
    ≤ᶜ-trans
      {x = absᶜ (tailSum derivativeTerms m k)}
      {y = tailSum majorant m k}
      {z = rational (radius ε)}
      absTail≤majorantTail
      (upperᶜ majorantTailBound)

  upperBound : tailSum derivativeTerms m k ≤ᶜ rational (radius ε)
  upperBound =
    ≤ᶜ-trans
      {x = tailSum derivativeTerms m k}
      {y = absᶜ (tailSum derivativeTerms m k)}
      {z = rational (radius ε)}
      (≤ᶜabsᶜ-left (tailSum derivativeTerms m k))
      absTail≤ε

  lowerBound : (-ᶜ tailSum derivativeTerms m k) ≤ᶜ rational (radius ε)
  lowerBound =
    ≤ᶜ-trans
      {x = -ᶜ tailSum derivativeTerms m k}
      {y = absᶜ (tailSum derivativeTerms m k)}
      {z = rational (radius ε)}
      (≤ᶜabsᶜ-right (tailSum derivativeTerms m k))
      absTail≤ε


derivativePowerSeriesOnStrictSubballWith :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  HasPowerSeriesOnBallWith a σ μ →
  HasPowerSeriesOnBallWith
    (derivativePowerSeries a)
    ρ
    (derivativeStrictSubballFromOnBallModulus {ρ = ρ} {σ = σ} ρ<σ μ)
derivativePowerSeriesOnStrictSubballWith
    {a = a}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    ρ<σ
    convergence =
  record
    { antitoneModulus =
        maxModulus-antitone
          constantTailModulusAntitone
          (derivativeStrictSubballFromOnBallMajorAntitone ρ<σ)
    ; tailBound =
        λ h h-bound →
          derivativeStrictSubballTailBoundFromOnBall
            {a = a}
            {ρ = ρ}
            {σ = σ}
            {μ = μ}
            ρ<σ
            convergence
            h
            h-bound
    }


derivativePowerSeriesOnStrictSubball :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  radius ρ ℚOrder.< radius σ →
  HasPowerSeriesOnBall a σ →
  HasPowerSeriesOnBall (derivativePowerSeries a) ρ
derivativePowerSeriesOnStrictSubball
    {a = a}
    {ρ = ρ}
    {σ = σ}
    ρ<σ
    (μ , convergence) =
  derivativeStrictSubballFromOnBallModulus {ρ = ρ} {σ = σ} ρ<σ μ ,
  derivativePowerSeriesOnStrictSubballWith
    {a = a}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    ρ<σ
    convergence
