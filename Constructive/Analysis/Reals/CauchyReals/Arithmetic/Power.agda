{-

Natural powers of HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Constructive.Analysis.GeometricDecay.Rate using (positivePower)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ProductBounds
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Data.PositiveRationals


realPower :
  ℝᶜ →
  ℕ →
  ℝᶜ
realPower x zero =
  1ᶜ
realPower x (suc n) =
  x ·ᶜ realPower x n


realPower-zero :
  (x : ℝᶜ) →
  realPower x zero ≡ 1ᶜ
realPower-zero x =
  refl


realPower-suc :
  (x : ℝᶜ) →
  (n : ℕ) →
  realPower x (suc n) ≡ x ·ᶜ realPower x n
realPower-suc x n =
  refl


private
  realPower-one-bounded :
    (x : ℝᶜ) →
    BoundedByᶜ 1⁺ (realPower x zero)
  realPower-one-bounded x =
    oneBoundedᶜ


realPowerBoundsFromBound :
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  BoundedByᶜ ρ x →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower x n)
realPowerBoundsFromBound ρ x x-bound zero =
  realPower-one-bounded x
realPowerBoundsFromBound ρ x x-bound (suc n) =
  bounded-byᶜ-mul
    ρ
    (positivePower ρ n)
    x
    (realPower x n)
    x-bound
    (realPowerBoundsFromBound ρ x x-bound n)
