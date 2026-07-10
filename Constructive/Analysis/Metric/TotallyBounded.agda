{-

Total boundedness by finite rational-precision nets

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Metric.TotallyBounded where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁)

open import Constructive.Data.PositiveRationals
open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Map

private
  variable
    ℓ ℓ' ℓᵃ ℓᵃ' ℓᵇ ℓᵇ' : Level


record FiniteNet (𝓜 : MetricSpace ℓ ℓ') (ε : ℚ⁺) :
    Type (ℓ-max ℓ ℓ') where
  constructor finite-net
  no-eta-equality

  field
    size : ℕ
    center : Fin size → MetricSpace.Carrier 𝓜
    covers :
      (x : MetricSpace.Carrier 𝓜) →
      ∥ Σ[ i ∈ Fin size ] MetricSpace.Close 𝓜 (center i) ε x ∥₁


open FiniteNet public


IsTotallyBounded : MetricSpace ℓ ℓ' → Type (ℓ-max ℓ ℓ')
IsTotallyBounded 𝓜 =
  (ε : ℚ⁺) → FiniteNet 𝓜 ε


record ImageFiniteNet
    (𝓧 : MetricSpace ℓᵃ ℓᵃ')
    (𝓨 : MetricSpace ℓᵇ ℓᵇ')
    (f : MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨)
    (ε : ℚ⁺) :
    Type (ℓ-max ℓᵃ (ℓ-max ℓᵇ ℓᵇ')) where
  constructor image-finite-net
  no-eta-equality

  field
    size : ℕ
    center : Fin size → MetricSpace.Carrier 𝓨
    covers :
      (x : MetricSpace.Carrier 𝓧) →
      ∥ Σ[ i ∈ Fin size ] MetricSpace.Close 𝓨 (center i) ε (f x) ∥₁


open ImageFiniteNet public


ImageIsTotallyBounded :
  (𝓧 : MetricSpace ℓᵃ ℓᵃ') →
  (𝓨 : MetricSpace ℓᵇ ℓᵇ') →
  (MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨) →
  Type (ℓ-max ℓᵃ (ℓ-max ℓᵇ ℓᵇ'))
ImageIsTotallyBounded 𝓧 𝓨 f =
  (ε : ℚ⁺) → ImageFiniteNet 𝓧 𝓨 f ε


uniformlyContinuousImageTotallyBounded :
  {𝓧 : MetricSpace ℓᵃ ℓᵃ'} →
  {𝓨 : MetricSpace ℓᵇ ℓᵇ'} →
  {f : MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨} →
  IsTotallyBounded 𝓧 →
  IsUniformlyContinuous 𝓧 𝓨 f →
  ImageIsTotallyBounded 𝓧 𝓨 f
uniformlyContinuousImageTotallyBounded {𝓧 = 𝓧} {𝓨 = 𝓨} {f = f} tb (μ , f-cont) ε =
  image-finite-net
    (FiniteNet.size net)
    (λ i → f (FiniteNet.center net i))
    cover-image
  where
  net : FiniteNet 𝓧 (μ ε)
  net = tb (μ ε)

  cover-image :
    (x : MetricSpace.Carrier 𝓧) →
    ∥ Σ[ i ∈ Fin (FiniteNet.size net) ]
      MetricSpace.Close 𝓨 (f (FiniteNet.center net i)) ε (f x) ∥₁
  cover-image x =
    Prop.map
      (λ (i , ci∼x) → i , f-cont ε ci∼x)
      (FiniteNet.covers net x)


nonexpandingImageTotallyBounded :
  {𝓧 : MetricSpace ℓᵃ ℓᵃ'} →
  {𝓨 : MetricSpace ℓᵇ ℓᵇ'} →
  {f : MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨} →
  IsTotallyBounded 𝓧 →
  IsNonexpanding 𝓧 𝓨 f →
  ImageIsTotallyBounded 𝓧 𝓨 f
nonexpandingImageTotallyBounded {𝓧 = 𝓧} {𝓨 = 𝓨} {f = f} tb f-ne =
  uniformlyContinuousImageTotallyBounded
    {𝓧 = 𝓧}
    {𝓨 = 𝓨}
    {f = f}
    tb
    (nonexpanding→uniformlyContinuous {𝓧 = 𝓧} {𝓨 = 𝓨} {f = f} f-ne)
