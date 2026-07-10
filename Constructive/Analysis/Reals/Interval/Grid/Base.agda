{-

Finite interval grids for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Interval.Grid.Base where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; Σ≡Prop)

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.Interval.Base
open import Constructive.Data.PositiveRationals


Grid :
  (a b : ℝᶜ) →
  a ≤ᶜ b →
  ℕ →
  Type₀
Grid a b a≤b n =
  Σ[ order ∈ a ≤ᶜ b ]
    Σ[ order-path ∈ order ≡ a≤b ]
      Σ[ point ∈ (Fin (suc n) → [ a , b ]ᶜ) ]
        Σ[ left-point ∈ pointᶜ {a = a} {b = b} (point Fin.zero) ≡ a ]
          pointᶜ {a = a} {b = b} (point (Fin.fromℕ n)) ≡ b


make-grid :
  {a b : ℝᶜ} →
  {a≤b : a ≤ᶜ b} →
  {n : ℕ} →
  (point : Fin (suc n) → [ a , b ]ᶜ) →
  pointᶜ {a = a} {b = b} (point Fin.zero) ≡ a →
  pointᶜ {a = a} {b = b} (point (Fin.fromℕ n)) ≡ b →
  Grid a b a≤b n
make-grid {a≤b = a≤b} point left-point right-point =
  a≤b , refl , point , left-point , right-point


module Grid where
  point :
    {a b : ℝᶜ} →
    {a≤b : a ≤ᶜ b} →
    {n : ℕ} →
    Grid a b a≤b n →
    Fin (suc n) →
    [ a , b ]ᶜ
  point G =
    G .snd .snd .fst

  left-point :
    {a b : ℝᶜ} →
    {a≤b : a ≤ᶜ b} →
    {n : ℕ} →
    (G : Grid a b a≤b n) →
    pointᶜ {a = a} {b = b}
      (point {a = a} {b = b} {a≤b = a≤b} {n = n} G Fin.zero)
    ≡ a
  left-point G =
    G .snd .snd .snd .fst

  right-point :
    {a b : ℝᶜ} →
    {a≤b : a ≤ᶜ b} →
    {n : ℕ} →
    (G : Grid a b a≤b n) →
    pointᶜ {a = a} {b = b}
      (point {a = a} {b = b} {a≤b = a≤b} {n = n} G (Fin.fromℕ n))
    ≡ b
  right-point G =
    G .snd .snd .snd .snd


AdjacentClose :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {n : ℕ} →
  Grid a b a≤b n →
  ℚ⁺ →
  Type₀
AdjacentClose {a = a} {b = b} {a≤b = a≤b} {n = n} G δ =
  (i : Fin n) →
  MetricSpace.Close
    (IntervalMetric a b)
    (Grid.point {a = a} {b = b} {a≤b = a≤b} {n = n} G (Fin.weakenFin i))
    δ
    (Grid.point {a = a} {b = b} {a≤b = a≤b} {n = n} G (Fin.suc i))


gridLeftEndpointPath :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {n : ℕ} →
  (G : Grid a b a≤b n) →
  Grid.point {a = a} {b = b} {a≤b = a≤b} {n = n} G Fin.zero ≡
  leftEndpoint {a = a} {b = b} a≤b
gridLeftEndpointPath {a = a} {b = b} {a≤b = a≤b} {n = n} G =
  Σ≡Prop
    (isPropIntervalBounds a b)
    (Grid.left-point {a = a} {b = b} {a≤b = a≤b} {n = n} G)


gridRightEndpointPath :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {n : ℕ} →
  (G : Grid a b a≤b n) →
  Grid.point {a = a} {b = b} {a≤b = a≤b} {n = n} G (Fin.fromℕ n) ≡
  rightEndpoint {a = a} {b = b} a≤b
gridRightEndpointPath {a = a} {b = b} {a≤b = a≤b} {n = n} G =
  Σ≡Prop
    (isPropIntervalBounds a b)
    (Grid.right-point {a = a} {b = b} {a≤b = a≤b} {n = n} G)


endpointGrid :
  (a b : ℝᶜ) →
  (a≤b : a ≤ᶜ b) →
  Grid a b a≤b (suc zero)
endpointGrid a b a≤b =
  make-grid {a = a} {b = b} {a≤b = a≤b} {n = suc zero} endpoint refl refl
  where
  endpoint : Fin (suc (suc zero)) → [ a , b ]ᶜ
  endpoint Fin.zero =
    leftEndpoint {a = a} {b = b} a≤b
  endpoint (Fin.suc Fin.zero) =
    rightEndpoint {a = a} {b = b} a≤b
