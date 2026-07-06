{-

Finite interval grids for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Interval.Grid where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (Σ≡Prop)

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.Interval
open import Constructive.Data.PositiveRationals


record Grid (a b : ℝᶜ) (a≤b : a ≤ᶜ b) (n : ℕ) : Type₀ where
  constructor make-grid
  no-eta-equality

  field
    point : Fin (suc n) → [ a , b ]ᶜ
    left-point : pointᶜ {a = a} {b = b} (point Fin.zero) ≡ a
    right-point : pointᶜ {a = a} {b = b} (point (Fin.fromℕ n)) ≡ b


AdjacentClose :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {n : ℕ} →
  Grid a b a≤b n →
  ℚ⁺ →
  Type₀
AdjacentClose {a = a} {b = b} {n = n} G δ =
  (i : Fin n) →
  MetricSpace.Close
    (IntervalMetric a b)
    (Grid.point G (Fin.weakenFin i))
    δ
    (Grid.point G (Fin.suc i))


gridLeftEndpointPath :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {n : ℕ} →
  (G : Grid a b a≤b n) →
  Grid.point G Fin.zero ≡ leftEndpoint {a = a} {b = b} a≤b
gridLeftEndpointPath {a = a} {b = b} {a≤b = a≤b} G =
  Σ≡Prop
    (isPropIntervalBounds a b)
    (Grid.left-point G)


gridRightEndpointPath :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {n : ℕ} →
  (G : Grid a b a≤b n) →
  Grid.point G (Fin.fromℕ n) ≡ rightEndpoint {a = a} {b = b} a≤b
gridRightEndpointPath {a = a} {b = b} {a≤b = a≤b} G =
  Σ≡Prop
    (isPropIntervalBounds a b)
    (Grid.right-point G)


endpointGrid :
  (a b : ℝᶜ) →
  (a≤b : a ≤ᶜ b) →
  Grid a b a≤b (suc zero)
endpointGrid a b a≤b =
  make-grid endpoint refl refl
  where
  endpoint : Fin (suc (suc zero)) → [ a , b ]ᶜ
  endpoint Fin.zero =
    leftEndpoint {a = a} {b = b} a≤b
  endpoint (Fin.suc Fin.zero) =
    rightEndpoint {a = a} {b = b} a≤b
