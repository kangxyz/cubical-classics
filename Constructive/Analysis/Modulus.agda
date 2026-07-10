{-

Natural-number moduli indexed by positive rational precision

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Modulus where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; max)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Data.PositiveRationals
open import Constructive.Data.Rationals using (1/2 ; 0<1/2)


NatModulus : Type₀
NatModulus =
  ℚ⁺ → ℕ


AntitoneNatModulus : NatModulus → Type₀
AntitoneNatModulus μ =
  {ε δ : ℚ⁺} →
  radius ε ℚOrder.≤ radius δ →
  NatOrder._≤_ (μ δ) (μ ε)


maxModulus : NatModulus → NatModulus → NatModulus
maxModulus μ ν ε =
  max (μ ε) (ν ε)


maxModulus-left≤ :
  (μ ν : NatModulus) →
  (ε : ℚ⁺) →
  NatOrder._≤_ (μ ε) (maxModulus μ ν ε)
maxModulus-left≤ μ ν ε =
  NatOrder.left-≤-max {m = μ ε} {n = ν ε}


maxModulus-right≤ :
  (μ ν : NatModulus) →
  (ε : ℚ⁺) →
  NatOrder._≤_ (ν ε) (maxModulus μ ν ε)
maxModulus-right≤ μ ν ε =
  NatOrder.right-≤-max {n = ν ε} {m = μ ε}


splitModulus : NatModulus → NatModulus
splitModulus μ ε =
  μ (half⁺ ε)


quarterModulus : NatModulus → NatModulus
quarterModulus μ ε =
  μ (quarter⁺ ε)


half-mono-≤ :
  {ε δ : ℚ⁺} →
  radius ε ℚOrder.≤ radius δ →
  radius (half⁺ ε) ℚOrder.≤ radius (half⁺ δ)
half-mono-≤ {ε = ε} {δ = δ} ε≤δ =
  ℚOrder.≤-·o
    (radius ε)
    (radius δ)
    1/2
    (ℚOrder.<Weaken≤ 0ℚ 1/2 0<1/2)
    ε≤δ


splitModulus-antitone :
  {μ : NatModulus} →
  AntitoneNatModulus μ →
  AntitoneNatModulus (splitModulus μ)
splitModulus-antitone μ-ant {ε = ε} {δ = δ} ε≤δ =
  μ-ant
    {ε = half⁺ ε}
    {δ = half⁺ δ}
    (half-mono-≤ {ε = ε} {δ = δ} ε≤δ)


quarterModulus-antitone :
  {μ : NatModulus} →
  AntitoneNatModulus μ →
  AntitoneNatModulus (quarterModulus μ)
quarterModulus-antitone μ-ant {ε = ε} {δ = δ} ε≤δ =
  μ-ant
    {ε = quarter⁺ ε}
    {δ = quarter⁺ δ}
    (half-mono-≤
      {ε = half⁺ ε}
      {δ = half⁺ δ}
      (half-mono-≤ {ε = ε} {δ = δ} ε≤δ))


maxModulus-antitone :
  {μ ν : NatModulus} →
  AntitoneNatModulus μ →
  AntitoneNatModulus ν →
  AntitoneNatModulus (maxModulus μ ν)
maxModulus-antitone {μ = μ} {ν = ν} μ-ant ν-ant {ε = ε} {δ = δ} ε≤δ =
  NatOrder.maxLUB
    (NatOrder.≤-trans
      (μ-ant {ε = ε} {δ = δ} ε≤δ)
      (maxModulus-left≤ μ ν ε))
    (NatOrder.≤-trans
      (ν-ant {ε = ε} {δ = δ} ε≤δ)
      (maxModulus-right≤ μ ν ε))
