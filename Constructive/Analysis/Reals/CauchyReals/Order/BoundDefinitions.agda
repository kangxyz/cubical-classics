{-

Bound predicates for rational and Cauchy-real values

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.CauchyReals.Order.BoundDefinitions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (_×_)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Data.PositiveRationals


RationalBoundᶜ : ℚ⁺ → ℚ → Type₀
RationalBoundᶜ κ q =
  (q ℚOrder.< radius κ) × (ℚ.- q ℚOrder.< radius κ)


rational-boundᶜ :
  {κ : ℚ⁺} {q : ℚ} →
  q ℚOrder.< radius κ →
  ℚ.- q ℚOrder.< radius κ →
  RationalBoundᶜ κ q
rational-boundᶜ upper lower =
  upper , lower


module RationalBoundᶜ {κ : ℚ⁺} {q : ℚ} (bound : RationalBoundᶜ κ q) where
  upperℚ : q ℚOrder.< radius κ
  upperℚ =
    bound .fst

  lowerℚ : ℚ.- q ℚOrder.< radius κ
  lowerℚ =
    bound .snd


open RationalBoundᶜ public


RationalClosedBoundᶜ : ℚ⁺ → ℚ → Type₀
RationalClosedBoundᶜ κ q =
  (q ℚOrder.≤ radius κ) × (ℚ.- q ℚOrder.≤ radius κ)


rational-closed-boundᶜ :
  {κ : ℚ⁺} {q : ℚ} →
  q ℚOrder.≤ radius κ →
  ℚ.- q ℚOrder.≤ radius κ →
  RationalClosedBoundᶜ κ q
rational-closed-boundᶜ upper lower =
  upper , lower


module RationalClosedBoundᶜ
    {κ : ℚ⁺} {q : ℚ}
    (bound : RationalClosedBoundᶜ κ q) where
  upper≤ℚ : q ℚOrder.≤ radius κ
  upper≤ℚ =
    bound .fst

  lower≤ℚ : ℚ.- q ℚOrder.≤ radius κ
  lower≤ℚ =
    bound .snd


open RationalClosedBoundᶜ public


isPropRationalBoundᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  isProp (RationalBoundᶜ κ q)
isPropRationalBoundᶜ κ q =
  isProp×
    (ℚOrder.isProp< q (radius κ))
    (ℚOrder.isProp< (ℚ.- q) (radius κ))


isPropRationalClosedBoundᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  isProp (RationalClosedBoundᶜ κ q)
isPropRationalClosedBoundᶜ κ q =
  isProp×
    (ℚOrder.isProp≤ q (radius κ))
    (ℚOrder.isProp≤ (ℚ.- q) (radius κ))


BoundedByᶜ : ℚ⁺ → ℝᶜ → Type₀
BoundedByᶜ κ x =
  (x ≤ᶜ rational (radius κ)) × ((-ᶜ x) ≤ᶜ rational (radius κ))


bounded-byᶜ :
  {κ : ℚ⁺} {x : ℝᶜ} →
  x ≤ᶜ rational (radius κ) →
  (-ᶜ x) ≤ᶜ rational (radius κ) →
  BoundedByᶜ κ x
bounded-byᶜ upper lower =
  upper , lower


module BoundedByᶜ {κ : ℚ⁺} {x : ℝᶜ} (bound : BoundedByᶜ κ x) where
  upperᶜ : x ≤ᶜ rational (radius κ)
  upperᶜ =
    bound .fst

  lowerᶜ : (-ᶜ x) ≤ᶜ rational (radius κ)
  lowerᶜ =
    bound .snd


open BoundedByᶜ public


isPropBoundedByᶜ :
  (κ : ℚ⁺) (x : ℝᶜ) →
  isProp (BoundedByᶜ κ x)
isPropBoundedByᶜ κ x =
  isProp×
    (isProp≤ᶜ x (rational (radius κ)))
    (isProp≤ᶜ (-ᶜ x) (rational (radius κ)))
