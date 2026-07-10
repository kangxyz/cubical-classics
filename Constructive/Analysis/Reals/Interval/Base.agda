{-

Closed intervals of HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Interval.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; _×_ ; Σ≡Prop)

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Map using (IsNonexpanding)
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base


infix 4 [_,_]ᶜ


[_,_]ᶜ : ℝᶜ → ℝᶜ → Type₀
[ a , b ]ᶜ =
  Σ[ x ∈ ℝᶜ ] (a ≤ᶜ x) × (x ≤ᶜ b)


pointᶜ : {a b : ℝᶜ} → [ a , b ]ᶜ → ℝᶜ
pointᶜ (x , _) =
  x


lowerBoundᶜ :
  {a b : ℝᶜ} →
  (u : [ a , b ]ᶜ) →
  a ≤ᶜ pointᶜ {a = a} {b = b} u
lowerBoundᶜ (x , a≤x , _) =
  a≤x


upperBoundᶜ :
  {a b : ℝᶜ} →
  (u : [ a , b ]ᶜ) →
  pointᶜ {a = a} {b = b} u ≤ᶜ b
upperBoundᶜ (x , _ , x≤b) =
  x≤b


leftEndpoint :
  {a b : ℝᶜ} →
  a ≤ᶜ b →
  [ a , b ]ᶜ
leftEndpoint {a = a} a≤b =
  a , ≤ᶜ-refl a , a≤b


rightEndpoint :
  {a b : ℝᶜ} →
  a ≤ᶜ b →
  [ a , b ]ᶜ
rightEndpoint {b = b} a≤b =
  b , a≤b , ≤ᶜ-refl b


isPropIntervalBounds :
  (a b x : ℝᶜ) →
  isProp ((a ≤ᶜ x) × (x ≤ᶜ b))
isPropIntervalBounds a b x =
  isProp× (isProp≤ᶜ a x) (isProp≤ᶜ x b)


isSetInterval :
  (a b : ℝᶜ) →
  isSet [ a , b ]ᶜ
isSetInterval a b =
  isOfHLevelΣ 2 (MetricSpace.isSetCarrier CauchyRealsMetricSpace) λ x →
  isProp→isSet (isPropIntervalBounds a b x)


IntervalMetricSpace : (a b : ℝᶜ) → MetricSpace _ _
IntervalMetricSpace a b .MetricSpace.Carrier =
  [ a , b ]ᶜ
IntervalMetricSpace a b .MetricSpace.isSetCarrier =
  isSetInterval a b
IntervalMetricSpace a b .MetricSpace.Close x ε y =
  MetricSpace.Close
    CauchyRealsMetricSpace
    (pointᶜ {a = a} {b = b} x)
    ε
    (pointᶜ {a = a} {b = b} y)
IntervalMetricSpace a b .MetricSpace.isPropClose x y ε =
  MetricSpace.isPropClose
    CauchyRealsMetricSpace
    (pointᶜ {a = a} {b = b} x)
    (pointᶜ {a = a} {b = b} y)
    ε
IntervalMetricSpace a b .MetricSpace.close-refl x ε =
  MetricSpace.close-refl
    CauchyRealsMetricSpace
    (pointᶜ {a = a} {b = b} x)
    ε
IntervalMetricSpace a b .MetricSpace.close-sym =
  MetricSpace.close-sym CauchyRealsMetricSpace
IntervalMetricSpace a b .MetricSpace.close-mono =
  MetricSpace.close-mono CauchyRealsMetricSpace
IntervalMetricSpace a b .MetricSpace.close-triangle =
  MetricSpace.close-triangle CauchyRealsMetricSpace
IntervalMetricSpace a b .MetricSpace.close-rounded =
  MetricSpace.close-rounded CauchyRealsMetricSpace
IntervalMetricSpace a b .MetricSpace.close-separated x y closeAt =
  Σ≡Prop
    (isPropIntervalBounds a b)
    (MetricSpace.close-separated
      CauchyRealsMetricSpace
      (pointᶜ {a = a} {b = b} x)
      (pointᶜ {a = a} {b = b} y)
      closeAt)


IntervalMetric : (a b : ℝᶜ) → MetricSpace _ _
IntervalMetric =
  IntervalMetricSpace


pointNonexpanding :
  {a b : ℝᶜ} →
  IsNonexpanding
    (IntervalMetric a b)
    CauchyRealsMetricSpace
    (pointᶜ {a = a} {b = b})
pointNonexpanding x∼y =
  x∼y
