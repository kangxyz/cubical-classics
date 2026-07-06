{-

Fixed-point interfaces

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.FixedPoint.Base where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax)

open import Constructive.Analysis.Metric.Base
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

private
  variable
    ℓ ℓ' : Level


CloseBound :
  (𝓜 : MetricSpace ℓ ℓ') →
  MetricSpace.Carrier 𝓜 →
  MetricSpace.Carrier 𝓜 →
  Type (ℓ-max ℓ-zero ℓ')
CloseBound 𝓜 x y =
  Σ[ ε ∈ ℚ⁺ ] MetricSpace.Close 𝓜 x ε y


HasCloseBounds :
  (𝓜 : MetricSpace ℓ ℓ') →
  Type (ℓ-max ℓ ℓ')
HasCloseBounds 𝓜 =
  (x y : MetricSpace.Carrier 𝓜) →
  CloseBound 𝓜 x y


IsContractionWith :
  (𝓜 : MetricSpace ℓ ℓ') →
  ℚ⁺ →
  (MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜) →
  Type (ℓ-max ℓ ℓ')
IsContractionWith 𝓜 ρ f =
  {x y : MetricSpace.Carrier 𝓜} {ε : ℚ⁺} →
  MetricSpace.Close 𝓜 x ε y →
  MetricSpace.Close 𝓜 (f x) (ρ *⁺ ε) (f y)


FixedPoint :
  {𝓜 : MetricSpace ℓ ℓ'} →
  (MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜) →
  Type ℓ
FixedPoint {𝓜 = 𝓜} f =
  Σ[ x ∈ MetricSpace.Carrier 𝓜 ] f x ≡ x


record Contraction (𝓜 : MetricSpace ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    map :
      MetricSpace.Carrier 𝓜 →
      MetricSpace.Carrier 𝓜

    ratio :
      ℚ⁺

    ratio<1 :
      radius ratio ℚOrder.< Rational.1ℚ

    contracts :
      IsContractionWith 𝓜 ratio map


record
  PicardSeed
    (𝓜 : MetricSpace ℓ ℓ')
    (f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜)
    : Type (ℓ-max ℓ ℓ')
  where
  field
    start :
      MetricSpace.Carrier 𝓜

    stepBound :
      ℚ⁺

    stepClose :
      MetricSpace.Close 𝓜 start stepBound (f start)
