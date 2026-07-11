{-

Extension helpers for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.CauchyReals.Extension where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals using (ℚ)

import Constructive.Analysis.Completions.CauchyCompletion.Extension as GenericExtension
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Base
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace


private
  module CompletionUniqueness =
    GenericExtension.UniquenessOf RationalsMetricSpace


IsRationalNonexpanding : (ℚ → ℝᶜ) → Type₀
IsRationalNonexpanding f =
  (q r : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  f q ∼[ ε ] f r


module _ (f : ℚ → ℝᶜ) (f-ne : IsRationalNonexpanding f) where
  private
    module GenericExtensionOf =
      GenericExtension.NonexpandingExtensionOf RationalsMetricSpace

    module Extension =
      GenericExtensionOf.NonexpandingExtension
        CauchyRealsMetricSpace
        CauchyRealsIsCauchyComplete
        f
        (λ {x} {y} {ε} → f-ne x y ε)

  extendNonexpanding : ℝᶜ → ℝᶜ
  extendNonexpanding =
    Extension.extend

  extendNonexpanding-rational :
    (q : ℚ) →
    extendNonexpanding (rational q) ≡ f q
  extendNonexpanding-rational =
    Extension.extend-point

  extendNonexpanding-close :
    {x y : ℝᶜ} {ε : ℚ⁺} →
    x ∼[ ε ] y →
    extendNonexpanding x ∼[ ε ] extendNonexpanding y
  extendNonexpanding-close =
    Extension.extend-close


nonexpanding-equal :
  (f g : ℝᶜ → ℝᶜ) →
  IsNonexpanding CauchyRealsMetricSpace CauchyRealsMetricSpace f →
  IsNonexpanding CauchyRealsMetricSpace CauchyRealsMetricSpace g →
  ((q : ℚ) → f (rational q) ≡ g (rational q)) →
  (x : ℝᶜ) →
  f x ≡ g x
nonexpanding-equal =
  CompletionUniqueness.nonexpanding-equal CauchyRealsMetricSpace


continuous-equal :
  (f g : ℝᶜ → ℝᶜ) →
  IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace f →
  IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace g →
  ((q : ℚ) → f (rational q) ≡ g (rational q)) →
  (x : ℝᶜ) →
  f x ≡ g x
continuous-equal =
  CompletionUniqueness.uniformlyContinuous-equal CauchyRealsMetricSpace


continuous-constant-equal :
  (f : ℝᶜ → ℝᶜ) →
  (c : ℝᶜ) →
  IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace f →
  ((q : ℚ) → f (rational q) ≡ c) →
  (x : ℝᶜ) →
  f x ≡ c
continuous-constant-equal f c f-cont =
  continuous-equal f (λ _ → c) f-cont
    (constant-uniformlyContinuous
      CauchyRealsMetricSpace CauchyRealsMetricSpace c)


IsBinaryNonexpandingLeft : (ℝᶜ → ℝᶜ → ℝᶜ) → Type₀
IsBinaryNonexpandingLeft f =
  (y : ℝᶜ) →
  IsNonexpanding CauchyRealsMetricSpace CauchyRealsMetricSpace
    (λ x → f x y)


IsBinaryNonexpandingRight : (ℝᶜ → ℝᶜ → ℝᶜ) → Type₀
IsBinaryNonexpandingRight f =
  (x : ℝᶜ) →
  IsNonexpanding CauchyRealsMetricSpace CauchyRealsMetricSpace
    (f x)


binary-nonexpanding-equal :
  (f g : ℝᶜ → ℝᶜ → ℝᶜ) →
  IsBinaryNonexpandingLeft f →
  IsBinaryNonexpandingRight f →
  IsBinaryNonexpandingLeft g →
  IsBinaryNonexpandingRight g →
  ((q r : ℚ) → f (rational q) (rational r) ≡
                 g (rational q) (rational r)) →
  (x y : ℝᶜ) →
  f x y ≡ g x y
binary-nonexpanding-equal f g f-left f-right g-left g-right point-path x y =
  nonexpanding-equal
    (λ z → f z y)
    (λ z → g z y)
    (f-left y)
    (g-left y)
    (λ q →
      nonexpanding-equal
        (f (rational q))
        (g (rational q))
        (f-right (rational q))
        (g-right (rational q))
        (point-path q)
        y)
    x


IsRationalLipschitzWithᶜ :
  ℚ⁺ →
  (ℚ → ℝᶜ) →
  Type₀
IsRationalLipschitzWithᶜ κ f =
  (q r : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  f q ∼[ κ *⁺ ε ] f r


private
  module RationalLipschitzExtension
    (κ : ℚ⁺) (f : ℚ → ℝᶜ)
    (f-lip : IsRationalLipschitzWithᶜ κ f)
    where
    open GenericExtension.LipschitzExtensionOf.LipschitzExtension
      RationalsMetricSpace
      κ
      CauchyRealsMetricSpace
      CauchyRealsIsCauchyComplete
      f
      f-lip
      public
      renaming
        ( extend to extendRationalLipschitzWithᶜ
        ; extend-point to extendRationalLipschitzWithᶜ-rational
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
  RationalLipschitzExtension.extendRationalLipschitzWithᶜ-lipschitzWith
    κ f f-lip _ _ _


extendRationalLipschitzWithᶜ-lipschitz :
  (κ : ℚ⁺) (f : ℚ → ℝᶜ)
  (f-lip : IsRationalLipschitzWithᶜ κ f) →
  IsLipschitz CauchyRealsMetricSpace CauchyRealsMetricSpace (extendRationalLipschitzWithᶜ κ f f-lip)
extendRationalLipschitzWithᶜ-lipschitz κ f f-lip =
  κ ,
  RationalLipschitzExtension.extendRationalLipschitzWithᶜ-lipschitzWith κ f f-lip


extendRationalLipschitzWithᶜ-continuous :
  (κ : ℚ⁺) (f : ℚ → ℝᶜ)
  (f-lip : IsRationalLipschitzWithᶜ κ f) →
  IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (extendRationalLipschitzWithᶜ κ f f-lip)
extendRationalLipschitzWithᶜ-continuous κ f f-lip =
  lipschitz→uniformlyContinuous
    {𝓧 = CauchyRealsMetricSpace}
    {𝓨 = CauchyRealsMetricSpace}
    {f = extendRationalLipschitzWithᶜ κ f f-lip}
    (extendRationalLipschitzWithᶜ-lipschitz κ f f-lip)


private
  module BinaryExtension =
    GenericExtension.BinaryExtensionOf RationalsMetricSpace


IsBinaryRationalNonexpandingLeft : (ℚ → ℚ → ℝᶜ) → Type₀
IsBinaryRationalNonexpandingLeft f =
  (q r s : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  f q s ∼[ ε ] f r s


IsBinaryRationalNonexpandingRight : (ℚ → ℚ → ℝᶜ) → Type₀
IsBinaryRationalNonexpandingRight f =
  (q : ℚ) → IsRationalNonexpanding (f q)


module _
  (f : ℚ → ℚ → ℝᶜ)
  (left-ne : IsBinaryRationalNonexpandingLeft f)
  (right-ne : IsBinaryRationalNonexpandingRight f)
  where

  private
    right-ne' : BinaryExtension.IsBinaryPointNonexpandingRight f
    right-ne' q {b = r} {c = s} {ε = ε} =
      right-ne q r s ε

    module Extension =
      BinaryExtension.BinaryNonexpandingExtension f left-ne right-ne'

  extendBinaryNonexpanding : ℝᶜ → ℝᶜ → ℝᶜ
  extendBinaryNonexpanding =
    Extension.extendBinaryNonexpanding

  extendBinaryNonexpanding-rational-right :
    (x : ℝᶜ) (r : ℚ) →
    extendBinaryNonexpanding x (rational r) ≡
    extendNonexpanding
      (λ q → f q r)
      (λ q s ε q∼s → left-ne q s r ε q∼s)
      x
  extendBinaryNonexpanding-rational-right =
    Extension.extendBinaryNonexpanding-point-right

  extendBinaryNonexpanding-close-left :
    {x y : ℝᶜ} {ε : ℚ⁺} →
    x ∼[ ε ] y →
    (z : ℝᶜ) →
    extendBinaryNonexpanding x z ∼[ ε ] extendBinaryNonexpanding y z
  extendBinaryNonexpanding-close-left =
    Extension.extendBinaryNonexpanding-close-left

  extendBinaryNonexpanding-close-right :
    (x : ℝᶜ) →
    {y z : ℝᶜ} {ε : ℚ⁺} →
    y ∼[ ε ] z →
    extendBinaryNonexpanding x y ∼[ ε ] extendBinaryNonexpanding x z
  extendBinaryNonexpanding-close-right =
    Extension.extendBinaryNonexpanding-close-right

  extendBinaryNonexpanding-close :
    {x y z w : ℝᶜ} {η ε : ℚ⁺} →
    x ∼[ η ] y →
    z ∼[ ε ] w →
    extendBinaryNonexpanding x z ∼[ η +⁺ ε ] extendBinaryNonexpanding y w
  extendBinaryNonexpanding-close =
    Extension.extendBinaryNonexpanding-close
