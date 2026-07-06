{-

Extension helpers for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Extension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Rationals using (ℚ)

import Constructive.Analysis.CauchyCompletion.Extension as GenericExtension
import Constructive.Analysis.Metric.Complete as MetricComplete
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness
open import Constructive.CauchyReals.Continuity
open import Constructive.CauchyReals.Induction
open import Constructive.CauchyReals.Recursion public


open GenericExtension.ExtensionOf RationalsMetricSpace public
  using
    ( close-limit-intro
    ; limit-close-intro
    ; limit-limit-intro
    ; limit-approx-close
    )


IsRationalNonexpanding : (ℚ → ℝᶜ) → Type₀
IsRationalNonexpanding f =
  (q r : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  f q ∼[ ε ] f r


module _ (f : ℚ → ℝᶜ) (f-ne : IsRationalNonexpanding f) where
  private
    module GenericExtensionOf =
      GenericExtension.ExtensionOf RationalsMetricSpace

    module Extension =
      GenericExtensionOf.NonexpandingExtension
        CauchyRealsMetricSpace
        MetricComplete.CauchyRealsIsComplete
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

  extendNonexpanding-isNonexpanding :
    IsNonexpanding extendNonexpanding
  extendNonexpanding-isNonexpanding =
    extendNonexpanding-close

  extendNonexpanding-continuous :
    IsContinuous extendNonexpanding
  extendNonexpanding-continuous =
    nonexpanding→continuous extendNonexpanding-isNonexpanding


extensions-close :
  {f g : ℚ → ℝᶜ} →
  (f-ne : IsRationalNonexpanding f) →
  (g-ne : IsRationalNonexpanding g) →
  ((q : ℚ) (ε : ℚ⁺) → f q ∼[ ε ] g q) →
  (x : ℝᶜ) (ε : ℚ⁺) →
  extendNonexpanding f f-ne x ∼[ ε ] extendNonexpanding g g-ne x
extensions-close {f = f} {g = g} f-ne g-ne f∼g =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
  kit .PropInductionKit.A x =
    (ε : ℚ⁺) →
    extendNonexpanding f f-ne x ∼[ ε ] extendNonexpanding g g-ne x
  kit .PropInductionKit.isPropA x =
    isPropΠ λ ε →
      squash
  kit .PropInductionKit.point* q =
    f∼g q
  kit .PropInductionKit.limit* x closeAt ε =
    limit-limit-intro
      (cauchy-approximation
        (λ δ → extendNonexpanding f f-ne (approximate x δ))
        (λ δ η → extendNonexpanding-close f f-ne (isRegular x δ η)))
      (cauchy-approximation
        (λ δ → extendNonexpanding g g-ne (approximate x δ))
        (λ δ η → extendNonexpanding-close g g-ne (isRegular x δ η)))
      ε δ δ δ+δ<ε
      (closeAt δ (ε ⊖ (δ +⁺ δ) [ δ+δ<ε ]))
    where
    δ : ℚ⁺
    δ = quarter⁺ ε

    δ+δ<ε : δ +⁺ δ <⁺ ε
    δ+δ<ε = quarter-sum< ε


extensions-equal :
  {f g : ℚ → ℝᶜ} →
  (f-ne : IsRationalNonexpanding f) →
  (g-ne : IsRationalNonexpanding g) →
  ((q : ℚ) → f q ≡ g q) →
  (x : ℝᶜ) →
  extendNonexpanding f f-ne x ≡ extendNonexpanding g g-ne x
extensions-equal {f = f} {g = g} f-ne g-ne f≡g x =
  path
    (extendNonexpanding f f-ne x)
    (extendNonexpanding g g-ne x)
    λ ε →
      extensions-close f-ne g-ne pointwise x ε
  where
  pointwise :
    (q : ℚ) (ε : ℚ⁺) →
    f q ∼[ ε ] g q
  pointwise q ε =
    subst
      (λ y → f q ∼[ ε ] y)
      (f≡g q)
      (close-refl (f q) ε)


nonexpanding-equal :
  (f g : ℝᶜ → ℝᶜ) →
  IsNonexpanding f →
  IsNonexpanding g →
  ((q : ℚ) → f (rational q) ≡ g (rational q)) →
  (x : ℝᶜ) →
  f x ≡ g x
nonexpanding-equal f g f-ne g-ne rational-path =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
  kit .PropInductionKit.A x =
    f x ≡ g x
  kit .PropInductionKit.isPropA x =
    isSetℝᶜ (f x) (g x)
  kit .PropInductionKit.point* =
    rational-path
  kit .PropInductionKit.limit* x pointwise =
    path (f (limit x)) (g (limit x)) closeAt
    where
    closeAt : (ε : ℚ⁺) → f (limit x) ∼[ ε ] g (limit x)
    closeAt ε =
      close-mono {ε = (α +⁺ α) +⁺ α} {δ = ε}
        (three-quarter< ε)
        (close-triangle
          (close-triangle f-lim∼approx f-approx∼g-approx)
          g-approx∼lim)
      where
      α : ℚ⁺
      α = quarter⁺ ε

      δ : ℚ⁺
      δ = quarter⁺ α

      lim∼approx : limit x ∼[ α ] approximate x δ
      lim∼approx =
        limit-approx-close x α

      f-lim∼approx : f (limit x) ∼[ α ] f (approximate x δ)
      f-lim∼approx =
        f-ne lim∼approx

      f-approx∼g-approx : f (approximate x δ) ∼[ α ] g (approximate x δ)
      f-approx∼g-approx =
        subst
          (λ y → f (approximate x δ) ∼[ α ] y)
          (pointwise δ)
          (close-refl (f (approximate x δ)) α)

      g-approx∼lim : g (approximate x δ) ∼[ α ] g (limit x)
      g-approx∼lim =
        g-ne (close-sym lim∼approx)


continuous-equal :
  (f g : ℝᶜ → ℝᶜ) →
  IsContinuous f →
  IsContinuous g →
  ((q : ℚ) → f (rational q) ≡ g (rational q)) →
  (x : ℝᶜ) →
  f x ≡ g x
continuous-equal f g f-cont g-cont rational-path =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
  kit .PropInductionKit.A x =
    f x ≡ g x
  kit .PropInductionKit.isPropA x =
    isSetℝᶜ (f x) (g x)
  kit .PropInductionKit.point* =
    rational-path
  kit .PropInductionKit.limit* x pointwise =
    path (f (limit x)) (g (limit x)) closeAt
    where
    closeAt : (ε : ℚ⁺) → f (limit x) ∼[ ε ] g (limit x)
    closeAt ε =
      close-mono {ε = (α +⁺ α) +⁺ α} {δ = ε}
        (three-quarter< ε)
        (close-triangle
          (close-triangle f-lim∼approx f-approx∼g-approx)
          g-approx∼lim)
      where
      α : ℚ⁺
      α = quarter⁺ ε

      μf μg : ℚ⁺
      μf = fst (f-cont α)
      μg = fst (g-cont α)

      μ : ℚ⁺
      μ = min⁺ μf μg

      β : ℚ⁺
      β = half⁺ μ

      δ : ℚ⁺
      δ = quarter⁺ β

      lim∼approx : limit x ∼[ β ] approximate x δ
      lim∼approx =
        limit-approx-close x β

      lim∼approx-f : limit x ∼[ μf ] approximate x δ
      lim∼approx-f =
        close-mono (half-min⁺<left μf μg) lim∼approx

      lim∼approx-g : limit x ∼[ μg ] approximate x δ
      lim∼approx-g =
        close-mono (half-min⁺<right μf μg) lim∼approx

      f-lim∼approx : f (limit x) ∼[ α ] f (approximate x δ)
      f-lim∼approx =
        snd (f-cont α) lim∼approx-f

      f-approx∼g-approx : f (approximate x δ) ∼[ α ] g (approximate x δ)
      f-approx∼g-approx =
        subst
          (λ y → f (approximate x δ) ∼[ α ] y)
          (pointwise δ)
          (close-refl (f (approximate x δ)) α)

      g-approx∼lim : g (approximate x δ) ∼[ α ] g (limit x)
      g-approx∼lim =
        snd (g-cont α) (close-sym lim∼approx-g)


continuous-constant-equal :
  (f : ℝᶜ → ℝᶜ) →
  (c : ℝᶜ) →
  IsContinuous f →
  ((q : ℚ) → f (rational q) ≡ c) →
  (x : ℝᶜ) →
  f x ≡ c
continuous-constant-equal f c f-cont rational-path =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
  kit .PropInductionKit.A x =
    f x ≡ c
  kit .PropInductionKit.isPropA x =
    isSetℝᶜ (f x) c
  kit .PropInductionKit.point* =
    rational-path
  kit .PropInductionKit.limit* x pointwise =
    path (f (limit x)) c closeAt
    where
    closeAt : (ε : ℚ⁺) → f (limit x) ∼[ ε ] c
    closeAt ε =
      close-mono {ε = α +⁺ α} {δ = ε}
        (quarter-sum< ε)
        (close-triangle f-lim∼approx f-approx∼c)
      where
      α : ℚ⁺
      α = quarter⁺ ε

      μ : ℚ⁺
      μ = fst (f-cont α)

      f-close : {x y : ℝᶜ} → x ∼[ μ ] y → f x ∼[ α ] f y
      f-close = snd (f-cont α)

      δ : ℚ⁺
      δ = quarter⁺ μ

      lim∼approx : limit x ∼[ μ ] approximate x δ
      lim∼approx =
        limit-approx-close x μ

      f-lim∼approx : f (limit x) ∼[ α ] f (approximate x δ)
      f-lim∼approx =
        f-close lim∼approx

      f-approx∼c : f (approximate x δ) ∼[ α ] c
      f-approx∼c =
        subst
          (λ y → f (approximate x δ) ∼[ α ] y)
          (pointwise δ)
          (close-refl (f (approximate x δ)) α)


private
  module BinaryExtension =
    GenericExtension.BinaryNonexpandingExtensionOf RationalsMetricSpace


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

  extendBinaryNonexpanding-rational-left :
    (q : ℚ) (y : ℝᶜ) →
    extendBinaryNonexpanding (rational q) y ≡
    extendNonexpanding (f q) (right-ne q) y
  extendBinaryNonexpanding-rational-left =
    Extension.extendBinaryNonexpanding-point-left

  extendBinaryNonexpanding-rational-rational :
    (q r : ℚ) →
    extendBinaryNonexpanding (rational q) (rational r) ≡ f q r
  extendBinaryNonexpanding-rational-rational =
    Extension.extendBinaryNonexpanding-point-point

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
