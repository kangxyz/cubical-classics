{-

Picard iteration in precision-indexed metric spaces

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.FixedPoint.Iteration where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; max)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Data.Sum as Sum using (inl ; inr)

open import Constructive.Analysis.GeometricDecay.Rate
open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Cauchy
open import Constructive.Analysis.Modulus
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational
open import Constructive.Analysis.FixedPoint.Base

private
  variable
    ℓ ℓ' : Level

contraction-precision< :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  (ε : ℚ⁺) →
  ρ *⁺ ε <⁺ ε
contraction-precision< ρ ρ<1 ε =
  subst
    (λ q → radius (ρ *⁺ ε) ℚOrder.< q)
    (ℚ.·IdL (radius ε))
    (Rational.mul-right-positive-<
      {a = radius ε}
      {b = radius ρ}
      {c = Rational.1ℚ}
      (ε .snd)
      ρ<1)


contraction-precision≤ :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  (ε : ℚ⁺) →
  radius (ρ *⁺ ε) ℚOrder.≤ radius ε
contraction-precision≤ ρ ρ<1 ε =
  Rational.<→≤
    {p = radius (ρ *⁺ ε)}
    {q = radius ε}
    (contraction-precision< ρ ρ<1 ε)


iterate :
  {A : Type ℓ} →
  (A → A) →
  A →
  ℕ →
  A
iterate f x zero =
  x
iterate f x (suc n) =
  f (iterate f x n)


picardAdjacent :
  (𝓜 : MetricSpace ℓ ℓ') →
  (ρ : ℚ⁺) →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  IsContractionWith 𝓜 ρ f →
  (x₀ : MetricSpace.Carrier 𝓜) →
  (η : ℚ⁺) →
  MetricSpace.Close 𝓜 x₀ η (f x₀) →
  (n : ℕ) →
  MetricSpace.Close
    𝓜
    (iterate f x₀ n)
    (positivePower ρ n *⁺ η)
    (iterate f x₀ (suc n))
picardAdjacent 𝓜 ρ {f = f} f-contr x₀ η x₀∼fx₀ zero =
  subst
    (λ ε → MetricSpace.Close 𝓜 x₀ ε (f x₀))
    (sym (*⁺-identity-left η))
    x₀∼fx₀
picardAdjacent 𝓜 ρ {f = f} f-contr x₀ η x₀∼fx₀ (suc n) =
  subst
    (λ ε →
      MetricSpace.Close
        𝓜
        (iterate f x₀ (suc n))
        ε
        (iterate f x₀ (suc (suc n))))
    (sym (*⁺-assoc ρ (positivePower ρ n) η))
    (f-contr
      {x = iterate f x₀ n}
      {y = iterate f x₀ (suc n)}
      {ε = positivePower ρ n *⁺ η}
      (picardAdjacent 𝓜 ρ f-contr x₀ η x₀∼fx₀ n))


picardChain+ :
  (𝓜 : MetricSpace ℓ ℓ') →
  (ρ : ℚ⁺) →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  IsContractionWith 𝓜 ρ f →
  (x₀ : MetricSpace.Carrier 𝓜) →
  (η : ℚ⁺) →
  MetricSpace.Close 𝓜 x₀ η (f x₀) →
  (m k n : ℕ) →
  suc k Nat.+ m ≡ n →
  MetricSpace.Close
    𝓜
    (iterate f x₀ m)
    (scaledGeometricSegment ρ η m k)
    (iterate f x₀ n)
picardChain+ 𝓜 ρ {f = f} f-contr x₀ η x₀∼fx₀ m zero n sm≡n =
  subst
    (λ t →
      MetricSpace.Close
        𝓜
        (iterate f x₀ m)
        (scaledGeometricSegment ρ η m zero)
        (iterate f x₀ t))
    sm≡n
    (picardAdjacent 𝓜 ρ f-contr x₀ η x₀∼fx₀ m)
picardChain+ 𝓜 ρ {f = f} f-contr x₀ η x₀∼fx₀ m (suc k) n ssk+m≡n =
  MetricSpace.close-triangle
    𝓜
    {x = iterate f x₀ m}
    {y = iterate f x₀ (suc m)}
    {z = iterate f x₀ n}
    {ε = positivePower ρ m *⁺ η}
    {δ = scaledGeometricSegment ρ η (suc m) k}
    (picardAdjacent 𝓜 ρ f-contr x₀ η x₀∼fx₀ m)
    (picardChain+
      𝓜
      ρ
      f-contr
      x₀
      η
      x₀∼fx₀
      (suc m)
      k
      n
      (Nat.+-suc (suc k) m ∙ ssk+m≡n))


picardForwardClose :
  (𝓜 : MetricSpace ℓ ℓ') →
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  IsContractionWith 𝓜 ρ f →
  (x₀ : MetricSpace.Carrier 𝓜) →
  (η ε : ℚ⁺) →
  MetricSpace.Close 𝓜 x₀ η (f x₀) →
  (m k n : ℕ) →
  suc k Nat.+ m ≡ n →
  NatOrder._≤_ (scaledGeometricSegmentModulus ρ ρ<1 η ε) m →
  MetricSpace.Close 𝓜 (iterate f x₀ m) ε (iterate f x₀ n)
picardForwardClose 𝓜 ρ ρ<1 {f = f} f-contr x₀ η ε x₀∼fx₀ m k n sk+m≡n μ≤m =
  close-mono-≤
    𝓜
    (scaledGeometricSegmentUpperBound⁺ ρ ρ<1 η ε m k μ≤m)
    (picardChain+ 𝓜 ρ f-contr x₀ η x₀∼fx₀ m k n sk+m≡n)


picardForwardClose≤ :
  (𝓜 : MetricSpace ℓ ℓ') →
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  IsContractionWith 𝓜 ρ f →
  (x₀ : MetricSpace.Carrier 𝓜) →
  (η : ℚ⁺) →
  MetricSpace.Close 𝓜 x₀ η (f x₀) →
  let μ = scaledGeometricSegmentModulus ρ ρ<1 η in
  (ε : ℚ⁺) →
  (m n : ℕ) →
  NatOrder._≤_ m n →
  NatOrder._≤_ (μ ε) m →
  MetricSpace.Close 𝓜 (iterate f x₀ m) ε (iterate f x₀ n)
picardForwardClose≤ 𝓜 ρ ρ<1 {f = f} f-contr x₀ η x₀∼fx₀ ε m n (zero , m≡n) μ≤m =
  subst
    (λ t → MetricSpace.Close 𝓜 (iterate f x₀ m) ε (iterate f x₀ t))
    m≡n
    (MetricSpace.close-refl 𝓜 (iterate f x₀ m) ε)
picardForwardClose≤ 𝓜 ρ ρ<1 {f = f} f-contr x₀ η x₀∼fx₀ ε m n (suc k , sk+m≡n) μ≤m =
  picardForwardClose
    𝓜
    ρ
    ρ<1
    f-contr
    x₀
    η
    ε
    x₀∼fx₀
    m
    k
    n
    sk+m≡n
    μ≤m


picardCloseToCommonUpper :
  (𝓜 : MetricSpace ℓ ℓ') →
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  IsContractionWith 𝓜 ρ f →
  (x₀ : MetricSpace.Carrier 𝓜) →
  (η ε : ℚ⁺) →
  MetricSpace.Close 𝓜 x₀ η (f x₀) →
  let μ = scaledGeometricSegmentModulus ρ ρ<1 η in
  (m n upper : ℕ) →
  NatOrder._≤_ m upper →
  NatOrder._≤_ n upper →
  NatOrder._≤_ (μ (half⁺ ε)) m →
  NatOrder._≤_ (μ (half⁺ ε)) n →
  MetricSpace.Close 𝓜 (iterate f x₀ m) ε (iterate f x₀ n)
picardCloseToCommonUpper 𝓜 ρ ρ<1 {f = f} f-contr x₀ η ε x₀∼fx₀
  m n upper m≤upper n≤upper μ≤m μ≤n =
  subst
    (λ ρ → MetricSpace.Close 𝓜 (iterate f x₀ m) ρ (iterate f x₀ n))
    (half⁺+half⁺≡ ε)
    (MetricSpace.close-triangle
      𝓜
      {x = iterate f x₀ m}
      {y = iterate f x₀ upper}
      {z = iterate f x₀ n}
      {ε = half⁺ ε}
      {δ = half⁺ ε}
      m∼upper
      upper∼n)
  where
  μ : NatModulus
  μ =
    scaledGeometricSegmentModulus ρ ρ<1 η

  m∼upper :
    MetricSpace.Close 𝓜 (iterate f x₀ m) (half⁺ ε) (iterate f x₀ upper)
  m∼upper =
    picardForwardClose≤ 𝓜 ρ ρ<1 f-contr x₀ η x₀∼fx₀ (half⁺ ε)
      m upper m≤upper μ≤m

  n∼upper :
    MetricSpace.Close 𝓜 (iterate f x₀ n) (half⁺ ε) (iterate f x₀ upper)
  n∼upper =
    picardForwardClose≤ 𝓜 ρ ρ<1 f-contr x₀ η x₀∼fx₀ (half⁺ ε)
      n upper n≤upper μ≤n

  upper∼n :
    MetricSpace.Close 𝓜 (iterate f x₀ upper) (half⁺ ε) (iterate f x₀ n)
  upper∼n =
    MetricSpace.close-sym 𝓜 n∼upper


picardRegularCauchyWithModulus :
  (𝓜 : MetricSpace ℓ ℓ') →
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  IsContractionWith 𝓜 ρ f →
  (x₀ : MetricSpace.Carrier 𝓜) →
  (η : ℚ⁺) →
  MetricSpace.Close 𝓜 x₀ η (f x₀) →
  let μ = scaledGeometricSegmentModulus ρ ρ<1 η in
  (ε δ : ℚ⁺) →
  MetricSpace.Close
    𝓜
    (iterate f x₀ (μ (half⁺ ε)))
    (ε +⁺ δ)
    (iterate f x₀ (μ (half⁺ δ)))
picardRegularCauchyWithModulus 𝓜 ρ ρ<1 {f = f} f-contr x₀ η x₀∼fx₀ ε δ =
  picardCloseToCommonUpper
    𝓜
    ρ
    ρ<1
    f-contr
    x₀
    η
    (ε +⁺ δ)
    x₀∼fx₀
    (ν ε)
    (ν δ)
    upper
    νe≤upper
    νd≤upper
    μκ≤νe
    μκ≤νd
  where
  μ : NatModulus
  μ =
    scaledGeometricSegmentModulus ρ ρ<1 η

  ν : NatModulus
  ν ε =
    μ (half⁺ ε)

  μ-antitone : AntitoneNatModulus μ
  μ-antitone =
    scaledGeometricSegmentModulus-antitone ρ ρ<1 η

  κ : ℚ⁺
  κ =
    half⁺ (ε +⁺ δ)

  upper : ℕ
  upper =
    max (ν ε) (ν δ)

  νe≤upper : NatOrder._≤_ (ν ε) upper
  νe≤upper =
    NatOrder.left-≤-max {m = ν ε} {n = ν δ}

  νd≤upper : NatOrder._≤_ (ν δ) upper
  νd≤upper =
    NatOrder.right-≤-max {n = ν δ} {m = ν ε}

  ε≤sum : radius ε ℚOrder.≤ radius (ε +⁺ δ)
  ε≤sum =
    Rational.<→≤
      {p = radius ε}
      {q = radius (ε +⁺ δ)}
      (summand-left<sum ε δ)

  δ≤sum : radius δ ℚOrder.≤ radius (ε +⁺ δ)
  δ≤sum =
    Rational.<→≤
      {p = radius δ}
      {q = radius (ε +⁺ δ)}
      (summand-right<sum ε δ)

  halfε≤κ : radius (half⁺ ε) ℚOrder.≤ radius κ
  halfε≤κ =
    half-mono-≤ {ε = ε} {δ = ε +⁺ δ} ε≤sum

  halfδ≤κ : radius (half⁺ δ) ℚOrder.≤ radius κ
  halfδ≤κ =
    half-mono-≤ {ε = δ} {δ = ε +⁺ δ} δ≤sum

  μκ≤νe : NatOrder._≤_ (μ κ) (ν ε)
  μκ≤νe =
    μ-antitone {ε = half⁺ ε} {δ = κ} halfε≤κ

  μκ≤νd : NatOrder._≤_ (μ κ) (ν δ)
  μκ≤νd =
    μ-antitone {ε = half⁺ δ} {δ = κ} halfδ≤κ


picardCauchyApproximation :
  (𝓜 : MetricSpace ℓ ℓ') →
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  IsContractionWith 𝓜 ρ f →
  (x₀ : MetricSpace.Carrier 𝓜) →
  (η : ℚ⁺) →
  MetricSpace.Close 𝓜 x₀ η (f x₀) →
  CauchyApproximation 𝓜
picardCauchyApproximation 𝓜 ρ ρ<1 {f = f} f-contr x₀ η x₀∼fx₀ =
  cauchy-approximation
    (λ ε → iterate f x₀ (μ (half⁺ ε)))
    (picardRegularCauchyWithModulus 𝓜 ρ ρ<1 f-contr x₀ η x₀∼fx₀)
  where
  μ : NatModulus
  μ =
    scaledGeometricSegmentModulus ρ ρ<1 η
