{-

Part of Constructive.Analysis.Reals.PowerSeries.Algebra

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Algebra.Coefficients where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Modulus
  using
    ( AntitoneNatModulus
    ; maxModulus
    ; maxModulus-antitone
    ; maxModulus-left≤
    ; maxModulus-right≤
    ; splitModulus
    ; splitModulus-antitone
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Data.PositiveRationals


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


shift-zero-sequence :
  (m : ℕ) →
  shift m (λ _ → 0ᶜ) ≡ (λ _ → 0ᶜ)
shift-zero-sequence zero =
  refl
shift-zero-sequence (suc m) =
  shift-zero-sequence m


tailSum-zero-sequence :
  (m k : ℕ) →
  tailSum (λ _ → 0ᶜ) m k ≡ 0ᶜ
tailSum-zero-sequence m k =
  cong
    (λ u → partialSum u k)
    (shift-zero-sequence m) ∙
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
