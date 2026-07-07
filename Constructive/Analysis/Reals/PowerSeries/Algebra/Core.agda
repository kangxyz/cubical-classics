{-

Part of Constructive.Analysis.Reals.PowerSeries.Algebra

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Algebra.Core where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; max ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.HITs.PropositionalTruncation as Prop

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Metric.Instances.CauchyReals
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower)
open import Constructive.Analysis.Reals.Sequences.Base
  using
    ( maxModulus
    ; maxModulus-antitone
    ; maxModulus-left≤
    ; maxModulus-right≤
    ; splitModulus
    ; half-mono-≤
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.Reals.PowerSeries.Algebra.Internal

splitTailModulus-antitone :
  {μ : ℚ⁺ → ℕ} →
  AntitoneTailModulus μ →
  AntitoneTailModulus (splitModulus μ)
splitTailModulus-antitone μ-ant {ε = ε} {δ = δ} ε≤δ =
  μ-ant
    {ε = half⁺ ε}
    {δ = half⁺ δ}
    (half-mono-≤ {ε = ε} {δ = δ} ε≤δ)


maxTailModulus-antitone :
  {μ ν : ℚ⁺ → ℕ} →
  AntitoneTailModulus μ →
  AntitoneTailModulus ν →
  AntitoneTailModulus (maxModulus μ ν)
maxTailModulus-antitone =
  maxModulus-antitone


tailBound-weakenModulus :
  {u : ℕ → ℝᶜ} →
  {μ ν : ℚ⁺ → ℕ} →
  ((ε : ℚ⁺) → NatOrder._≤_ (μ ε) (ν ε)) →
  TailBound u μ →
  TailBound u ν
tailBound-weakenModulus μ≤ν tailBound ε m k ν≤m =
  tailBound ε m k (NatOrder.≤-trans (μ≤ν ε) ν≤m)


tailBound-max-left :
  {u : ℕ → ℝᶜ} →
  {μ ν : ℚ⁺ → ℕ} →
  TailBound u μ →
  TailBound u (maxModulus μ ν)
tailBound-max-left {μ = μ} {ν = ν} =
  tailBound-weakenModulus (maxModulus-left≤ μ ν)


tailBound-max-right :
  {u : ℕ → ℝᶜ} →
  {μ ν : ℚ⁺ → ℕ} →
  TailBound u ν →
  TailBound u (maxModulus μ ν)
tailBound-max-right {μ = μ} {ν = ν} =
  tailBound-weakenModulus (maxModulus-right≤ μ ν)


bounded-byᶜ-zero :
  (ε : ℚ⁺) →
  BoundedByᶜ ε 0ᶜ
bounded-byᶜ-zero ε =
  rational-closed-bound→boundedᶜ
    ε
    Rational.0ℚ
    (rational-closed-boundᶜ
      0≤ε
      (subst
        (λ q → q ℚOrder.≤ radius ε)
        (sym Rational.neg-zero)
        0≤ε))
  where
  0≤ε : Rational.0ℚ ℚOrder.≤ radius ε
  0≤ε =
    ℚOrder.<Weaken≤ Rational.0ℚ (radius ε) (ε .snd)


drop-zero-sequence :
  (m : ℕ) →
  drop m (λ _ → 0ᶜ) ≡ (λ _ → 0ᶜ)
drop-zero-sequence zero =
  refl
drop-zero-sequence (suc m) =
  drop-zero-sequence m


tailSum-zero-sequence :
  (m k : ℕ) →
  tailSum (λ _ → 0ᶜ) m k ≡ 0ᶜ
tailSum-zero-sequence m k =
  cong
    (λ u → partialSum u k)
    (drop-zero-sequence m) ∙
  partialSum-zero-sequence k


zeroPowerSeries :
  PowerSeries
zeroPowerSeries _ =
  0ᶜ


constantPowerSeries :
  ℝᶜ →
  PowerSeries
constantPowerSeries c zero =
  c
constantPowerSeries c (suc _) =
  0ᶜ


addPowerSeries :
  PowerSeries →
  PowerSeries →
  PowerSeries
addPowerSeries a b n =
  a n +ᶜ b n


negPowerSeries :
  PowerSeries →
  PowerSeries
negPowerSeries a n =
  -ᶜ a n


subPowerSeries :
  PowerSeries →
  PowerSeries →
  PowerSeries
subPowerSeries a b =
  addPowerSeries a (negPowerSeries b)


rationalScalePowerSeries :
  ℚ →
  PowerSeries →
  PowerSeries
rationalScalePowerSeries q a n =
  rational q ·ᶜ a n


realScalePowerSeries :
  ℝᶜ →
  PowerSeries →
  PowerSeries
realScalePowerSeries x a n =
  x ·ᶜ a n


shiftPowerSeries :
  PowerSeries →
  PowerSeries
shiftPowerSeries a n =
  a (suc n)
