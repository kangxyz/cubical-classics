{-

Rational Lipschitz extension for Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Lipschitz.RationalExtension where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals using (ℚ)

import Constructive.Analysis.CauchyCompletion.Complete as CauchyCompletion
import Constructive.Analysis.Metric.Complete as MetricComplete
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Continuity
open import Constructive.CauchyReals.Lipschitz.Base
open import Constructive.Data.PositiveRationals
open import Constructive.Data.Rationals.Closeness


IsRationalLipschitzWithᶜ :
  ℚ⁺ →
  (ℚ → ℝᶜ) →
  Type₀
IsRationalLipschitzWithᶜ κ f =
  (q r : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  f q ∼[ κ *⁺ ε ] f r


module RationalLipschitzExtension
  (κ : ℚ⁺) (f : ℚ → ℝᶜ)
  (f-lip : IsRationalLipschitzWithᶜ κ f)
  where
  open CauchyCompletion.CompleteOf.ScaledLipschitzCompletionExtension
    RationalsMetricSpace
    κ
    CauchyRealsMetricSpace
    MetricComplete.CauchyRealsIsComplete
    f
    f-lip
    public
    renaming
      ( extend to extendRationalLipschitzWithᶜ
      ; extend-point to extendRationalLipschitzWithᶜ-rational
      ; extend-close to extendRationalLipschitzWithᶜ-close
      ; extend-lipschitz to extendRationalLipschitzWithᶜ-lipschitzWith
      )


extendRationalLipschitzWithᶜ :
  (κ : ℚ⁺) (f : ℚ → ℝᶜ) →
  IsRationalLipschitzWithᶜ κ f →
  ℝᶜ → ℝᶜ
extendRationalLipschitzWithᶜ κ f f-lip =
  RationalLipschitzExtension.extendRationalLipschitzWithᶜ κ f f-lip


extendRationalLipschitzWithᶜ-rational :
  (κ : ℚ⁺) (f : ℚ → ℝᶜ)
  (f-lip : IsRationalLipschitzWithᶜ κ f)
  (q : ℚ) →
  extendRationalLipschitzWithᶜ κ f f-lip (rational q) ≡ f q
extendRationalLipschitzWithᶜ-rational κ f f-lip =
  RationalLipschitzExtension.extendRationalLipschitzWithᶜ-rational κ f f-lip


extendRationalLipschitzWithᶜ-close :
  (κ : ℚ⁺) (f : ℚ → ℝᶜ)
  (f-lip : IsRationalLipschitzWithᶜ κ f) →
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  extendRationalLipschitzWithᶜ κ f f-lip x
    ∼[ κ *⁺ ε ]
  extendRationalLipschitzWithᶜ κ f f-lip y
extendRationalLipschitzWithᶜ-close κ f f-lip =
  RationalLipschitzExtension.extendRationalLipschitzWithᶜ-close κ f f-lip


extendRationalLipschitzWithᶜ-unique :
  (κ : ℚ⁺) (f : ℚ → ℝᶜ)
  (f-lip : IsRationalLipschitzWithᶜ κ f)
  (g : ℝᶜ → ℝᶜ) →
  ({x y : ℝᶜ} {ε : ℚ⁺} → x ∼[ ε ] y → g x ∼[ κ *⁺ ε ] g y) →
  ((q : ℚ) → g (rational q) ≡ f q) →
  (x : ℝᶜ) →
  g x ≡ extendRationalLipschitzWithᶜ κ f f-lip x
extendRationalLipschitzWithᶜ-unique κ f f-lip =
  RationalLipschitzExtension.extend-unique κ f f-lip


extendRationalLipschitzWithᶜ-lipschitz :
  (κ : ℚ⁺) (f : ℚ → ℝᶜ)
  (f-lip : IsRationalLipschitzWithᶜ κ f) →
  IsLipschitz (extendRationalLipschitzWithᶜ κ f f-lip)
extendRationalLipschitzWithᶜ-lipschitz κ f f-lip =
  (λ ε → posInv⁺ κ *⁺ ε) ,
  RationalLipschitzExtension.extendRationalLipschitzWithᶜ-lipschitzWith κ f f-lip


extendRationalLipschitzWithᶜ-continuous :
  (κ : ℚ⁺) (f : ℚ → ℝᶜ)
  (f-lip : IsRationalLipschitzWithᶜ κ f) →
  IsContinuous (extendRationalLipschitzWithᶜ κ f f-lip)
extendRationalLipschitzWithᶜ-continuous κ f f-lip =
  lipschitz→continuous
    (extendRationalLipschitzWithᶜ-lipschitz κ f f-lip)
