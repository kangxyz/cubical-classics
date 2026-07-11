{-

Strict-subball constants for derivative convergence from ball convergence.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Differentiation.SubballParameters where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder

open import Cubical.Data.Nat using (ℕ)
open import Constructive.Analysis.Modulus
  using (maxModulus)
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using (rationalScaleModulus)
open import Constructive.Analysis.GeometricDecay
  using (positiveGeometricPowerModulus)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

derivativeStrictSubballOuterRatio :
  {ρ σ : ℚ⁺} →
  radius ρ ℚOrder.< radius σ →
  ℚ⁺
derivativeStrictSubballOuterRatio {ρ = ρ} {σ = σ} ρ<σ =
  Rational.middle (radius ratio) Rational.1ℚ ,
  outer-positive
  where
  ratio : ℚ⁺
  ratio =
    ratio⁺ ρ σ

  ratio<1 : radius ratio ℚOrder.< Rational.1ℚ
  ratio<1 =
    ratio⁺<1 {ρ = ρ} {σ = σ} ρ<σ

  ratio<outer :
    radius ratio ℚOrder.< Rational.middle (radius ratio) Rational.1ℚ
  ratio<outer =
    Rational.middle>l {p = radius ratio} {q = Rational.1ℚ} ratio<1

  outer-positive :
    Rational.0ℚ ℚOrder.< Rational.middle (radius ratio) Rational.1ℚ
  outer-positive =
    Rational.≤<-trans
      {p = Rational.0ℚ}
      {q = radius ratio}
      {r = Rational.middle (radius ratio) Rational.1ℚ}
      (Rational.<→≤ {p = Rational.0ℚ} {q = radius ratio} (ratio .snd))
      ratio<outer


derivativeStrictSubballOuterRatio<1 :
  {ρ σ : ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  radius (derivativeStrictSubballOuterRatio {ρ = ρ} {σ = σ} ρ<σ)
    ℚOrder.<
  Rational.1ℚ
derivativeStrictSubballOuterRatio<1 {ρ = ρ} {σ = σ} ρ<σ =
  Rational.middle<r
    {p = radius (ratio⁺ ρ σ)}
    {q = Rational.1ℚ}
    (ratio⁺<1 {ρ = ρ} {σ = σ} ρ<σ)


innerRatio<outerRatio :
  {ρ σ : ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  radius (ratio⁺ ρ σ)
    ℚOrder.<
  radius (derivativeStrictSubballOuterRatio {ρ = ρ} {σ = σ} ρ<σ)
innerRatio<outerRatio {ρ = ρ} {σ = σ} ρ<σ =
  Rational.middle>l
    {p = radius (ratio⁺ ρ σ)}
    {q = Rational.1ℚ}
    (ratio⁺<1 {ρ = ρ} {σ = σ} ρ<σ)


derivativeStrictSubballInnerRatio :
  {ρ σ : ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ℚ⁺
derivativeStrictSubballInnerRatio {ρ = ρ} {σ = σ} ρ<σ =
  ratio⁺ ρ σ *⁺
  posInv⁺ (derivativeStrictSubballOuterRatio {ρ = ρ} {σ = σ} ρ<σ)


derivativeStrictSubballInnerRatio<1 :
  {ρ σ : ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  radius (derivativeStrictSubballInnerRatio {ρ = ρ} {σ = σ} ρ<σ)
    ℚOrder.<
  Rational.1ℚ
derivativeStrictSubballInnerRatio<1 {ρ = ρ} {σ = σ} ρ<σ =
  Rational.div-positive-denom-<1
    {q = radius (ratio⁺ ρ σ)}
    {a = radius outer}
    (innerRatio<outerRatio ρ<σ)
    (outer .snd)
  where
  outer : ℚ⁺
  outer =
    derivativeStrictSubballOuterRatio {ρ = ρ} {σ = σ} ρ<σ


derivativeStrictSubballInnerGap :
  {ρ σ : ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ℚ⁺
derivativeStrictSubballInnerGap {ρ = ρ} {σ = σ} ρ<σ =
  1⁺ ⊖ derivativeStrictSubballInnerRatio {ρ = ρ} {σ = σ} ρ<σ
    [ derivativeStrictSubballInnerRatio<1 {ρ = ρ} {σ = σ} ρ<σ ]


derivativeStrictSubballFromOnBallScale :
  {ρ σ : ℚ⁺} →
  radius ρ ℚOrder.< radius σ →
  ℚ⁺
derivativeStrictSubballFromOnBallScale {ρ = ρ} {σ = σ} ρ<σ =
  posInv⁺ σ *⁺
  (1⁺ +⁺ posInv⁺ (derivativeStrictSubballInnerGap {ρ = ρ} {σ = σ} ρ<σ))


derivativeStrictSubballFromOnBallGeometricModulus :
  {ρ σ : ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ℚ⁺ →
  ℕ
derivativeStrictSubballFromOnBallGeometricModulus {ρ = ρ} {σ = σ} ρ<σ =
  rationalScaleModulus
    (radius (derivativeStrictSubballFromOnBallScale {ρ = ρ} {σ = σ} ρ<σ))
    (positiveGeometricPowerModulus outer outer<1)
  where
  outer : ℚ⁺
  outer =
    derivativeStrictSubballOuterRatio {ρ = ρ} {σ = σ} ρ<σ

  outer<1 : radius outer ℚOrder.< Rational.1ℚ
  outer<1 =
    derivativeStrictSubballOuterRatio<1 {ρ = ρ} {σ = σ} ρ<σ


derivativeStrictSubballFromOnBallModulus :
  {ρ σ : ℚ⁺} →
  radius ρ ℚOrder.< radius σ →
  (ℚ⁺ → ℕ) →
  ℚ⁺ →
  ℕ
derivativeStrictSubballFromOnBallModulus {ρ = ρ} {σ = σ} ρ<σ μ =
  maxModulus
    (λ _ → μ 1⁺)
    (derivativeStrictSubballFromOnBallGeometricModulus {ρ = ρ} {σ = σ} ρ<σ)
