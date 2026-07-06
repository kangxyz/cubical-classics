{-

Rational Lipschitz extension for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Lipschitz.RationalExtension where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness
open import Constructive.CauchyReals.Continuity
open import Constructive.CauchyReals.Extension
open import Constructive.CauchyReals.Lipschitz.Base
open import Constructive.CauchyReals.Recursion
open import Constructive.Data.PositiveRationals
open import Constructive.Data.Rationals.Closeness
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    scale-diff-positive :
      (a p q : 𝓡 .fst) →
      (a · p) - (a · q) ≡ a · (p - q)
    scale-diff-positive _ _ _ = solve! 𝓡

    scale-diff-sum :
      (κ ε δ η : 𝓡 .fst) →
      (κ · ε) - ((κ · δ) + (κ · η)) ≡ κ · (ε - (δ + η))
    scale-diff-sum _ _ _ _ = solve! 𝓡


IsRationalLipschitzWithᶜ :
  ℚ⁺ →
  (ℚ → ℝᶜ) →
  Type₀
IsRationalLipschitzWithᶜ κ f =
  (q r : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  f q ∼[ κ *⁺ ε ] f r



scale-precision-cancel :
  (κ ε : ℚ⁺) →
  κ *⁺ (posInv⁺ κ *⁺ ε) ≡ ε
scale-precision-cancel κ ε =
  sym (*⁺-assoc κ (posInv⁺ κ) ε) ∙
  cong (λ ρ → ρ *⁺ ε) (*⁺-posInv-right κ) ∙
  *⁺-identity-left ε

scale-precision-cancel-left :
  (κ ε : ℚ⁺) →
  posInv⁺ κ *⁺ (κ *⁺ ε) ≡ ε
scale-precision-cancel-left κ ε =
  sym (*⁺-assoc (posInv⁺ κ) κ ε) ∙
  cong (λ ρ → ρ *⁺ ε) (*⁺-posInv-left κ) ∙
  *⁺-identity-left ε

scale-precision-sum-cancel :
  (κ ε δ : ℚ⁺) →
  κ *⁺ ((posInv⁺ κ *⁺ ε) +⁺ (posInv⁺ κ *⁺ δ)) ≡ ε +⁺ δ
scale-precision-sum-cancel κ ε δ =
  *⁺-distrib-left κ (posInv⁺ κ *⁺ ε) (posInv⁺ κ *⁺ δ) ∙
  cong₂ _+⁺_
    (scale-precision-cancel κ ε)
    (scale-precision-cancel κ δ)

scale-precision-mono :
  (κ ε δ : ℚ⁺) →
  ε <⁺ δ →
  κ *⁺ ε <⁺ κ *⁺ δ
scale-precision-mono κ ε δ ε<δ =
  Rational.mul-left-positive-<
    {a = radius κ}
    {b = radius ε}
    {c = radius δ}
    (κ .snd)
    ε<δ

scale-precision-difference :
  (κ ε δ : ℚ⁺) →
  (δ<ε : δ <⁺ ε) →
  (κδ<κε : κ *⁺ δ <⁺ κ *⁺ ε) →
  (κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ] ≡
  κ *⁺ (ε ⊖ δ [ δ<ε ])
scale-precision-difference κ ε δ δ<ε κδ<κε =
  ℚ⁺Path
    (SolverHelpers.scale-diff-positive ℚCommRing
      (radius κ) (radius ε) (radius δ))

scale-precision-sum< :
  (κ ε δ η : ℚ⁺) →
  δ +⁺ η <⁺ ε →
  (κ *⁺ δ) +⁺ (κ *⁺ η) <⁺ κ *⁺ ε
scale-precision-sum< κ ε δ η δ+η<ε =
  subst
    (λ ρ → ρ <⁺ κ *⁺ ε)
    (*⁺-distrib-left κ δ η)
    (scale-precision-mono κ (δ +⁺ η) ε δ+η<ε)

scale-precision-sum-difference :
  (κ ε δ η : ℚ⁺) →
  (δ+η<ε : δ +⁺ η <⁺ ε) →
  (κδη<κε : (κ *⁺ δ) +⁺ (κ *⁺ η) <⁺ κ *⁺ ε) →
  (κ *⁺ ε) ⊖ ((κ *⁺ δ) +⁺ (κ *⁺ η)) [ κδη<κε ] ≡
  κ *⁺ (ε ⊖ (δ +⁺ η) [ δ+η<ε ])
scale-precision-sum-difference κ ε δ η δ+η<ε κδη<κε =
  ℚ⁺Path
    (SolverHelpers.scale-diff-sum ℚCommRing
      (radius κ) (radius ε) (radius δ) (radius η))

ScaledCauchy :
  (κ : ℚ⁺) →
  (ℚ⁺ → ℝᶜ) →
  Type₀
ScaledCauchy κ g =
  (ε δ : ℚ⁺) → g ε ∼[ κ *⁺ (ε +⁺ δ) ] g δ

scaledCauchyApproximation :
  (κ : ℚ⁺) →
  (g : ℚ⁺ → ℝᶜ) →
  ScaledCauchy κ g →
  CauchyApproximation
scaledCauchyApproximation κ g gCauchy =
  cauchy-approximation h hCauchy
  where
  h : ℚ⁺ → ℝᶜ
  h ε = g (posInv⁺ κ *⁺ ε)

  hCauchy : (ε δ : ℚ⁺) → h ε ∼[ ε +⁺ δ ] h δ
  hCauchy ε δ =
    subst
      (λ ρ → h ε ∼[ ρ ] h δ)
      (scale-precision-sum-cancel κ ε δ)
      (gCauchy (posInv⁺ κ *⁺ ε) (posInv⁺ κ *⁺ δ))

private
  rationalLipschitzKit :
    (κ : ℚ⁺) (f : ℚ → ℝᶜ) →
    IsRationalLipschitzWithᶜ κ f →
    RecursionKit ℓ-zero ℓ-zero
  rationalLipschitzKit κ f f-lip .RecursionKit.A =
    ℝᶜ
  rationalLipschitzKit κ f f-lip .RecursionKit.B ε x y =
    x ∼[ κ *⁺ ε ] y
  rationalLipschitzKit κ f f-lip .RecursionKit.isPropB ε x y =
    squash
  rationalLipschitzKit κ f f-lip .RecursionKit.separated x y closeAt =
    path x y λ ε →
      subst
        (λ ρ → x ∼[ ρ ] y)
        (scale-precision-cancel κ ε)
        (closeAt (posInv⁺ κ *⁺ ε))
  rationalLipschitzKit κ f f-lip .RecursionKit.rational* =
    f
  rationalLipschitzKit κ f f-lip .RecursionKit.limit* x g gCauchy =
    limit (scaledCauchyApproximation κ g gCauchy)
  rationalLipschitzKit κ f f-lip .RecursionKit.rational-rational* q r ε q∼r =
    f-lip q r ε q∼r
  rationalLipschitzKit κ f f-lip .RecursionKit.rational-limit* q ε δ δ<ε y g gCauchy q∼gδ =
    close-limit-intro
      (f q)
      (scaledCauchyApproximation κ g gCauchy)
      (κ *⁺ ε)
      (κ *⁺ δ)
      κδ<κε
      q∼hκδ
    where
    κδ<κε : κ *⁺ δ <⁺ κ *⁺ ε
    κδ<κε =
      scale-precision-mono κ δ ε δ<ε

    precisionPath :
      (κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ] ≡
      κ *⁺ (ε ⊖ δ [ δ<ε ])
    precisionPath =
      scale-precision-difference κ ε δ δ<ε κδ<κε

    indexPath : posInv⁺ κ *⁺ (κ *⁺ δ) ≡ δ
    indexPath =
      scale-precision-cancel-left κ δ

    q∼hκδ :
      f q
        ∼[ (κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ] ]
      approximate (scaledCauchyApproximation κ g gCauchy) (κ *⁺ δ)
    q∼hκδ =
      subst2
        (λ ρ θ → f q ∼[ ρ ] g θ)
        (sym precisionPath)
        (sym indexPath)
        q∼gδ
  rationalLipschitzKit κ f f-lip .RecursionKit.limit-rational* x g gCauchy r ε δ δ<ε gδ∼r =
    limit-close-intro
      (scaledCauchyApproximation κ g gCauchy)
      (f r)
      (κ *⁺ ε)
      (κ *⁺ δ)
      κδ<κε
      hκδ∼r
    where
    κδ<κε : κ *⁺ δ <⁺ κ *⁺ ε
    κδ<κε =
      scale-precision-mono κ δ ε δ<ε

    precisionPath :
      (κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ] ≡
      κ *⁺ (ε ⊖ δ [ δ<ε ])
    precisionPath =
      scale-precision-difference κ ε δ δ<ε κδ<κε

    indexPath : posInv⁺ κ *⁺ (κ *⁺ δ) ≡ δ
    indexPath =
      scale-precision-cancel-left κ δ

    hκδ∼r :
      approximate (scaledCauchyApproximation κ g gCauchy) (κ *⁺ δ)
        ∼[ (κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ] ]
      f r
    hκδ∼r =
      subst2
        (λ θ ρ → g θ ∼[ ρ ] f r)
        (sym indexPath)
        (sym precisionPath)
        gδ∼r
  rationalLipschitzKit κ f f-lip .RecursionKit.limit-limit* x y g h gCauchy hCauchy ε δ η δ+η<ε gδ∼hη =
    limit-limit-intro
      (scaledCauchyApproximation κ g gCauchy)
      (scaledCauchyApproximation κ h hCauchy)
      (κ *⁺ ε)
      (κ *⁺ δ)
      (κ *⁺ η)
      κδη<κε
      hκδ∼hκη
    where
    κδη<κε : (κ *⁺ δ) +⁺ (κ *⁺ η) <⁺ κ *⁺ ε
    κδη<κε =
      scale-precision-sum< κ ε δ η δ+η<ε

    precisionPath :
      (κ *⁺ ε) ⊖ ((κ *⁺ δ) +⁺ (κ *⁺ η)) [ κδη<κε ] ≡
      κ *⁺ (ε ⊖ (δ +⁺ η) [ δ+η<ε ])
    precisionPath =
      scale-precision-sum-difference κ ε δ η δ+η<ε κδη<κε

    δIndexPath : posInv⁺ κ *⁺ (κ *⁺ δ) ≡ δ
    δIndexPath =
      scale-precision-cancel-left κ δ

    ηIndexPath : posInv⁺ κ *⁺ (κ *⁺ η) ≡ η
    ηIndexPath =
      scale-precision-cancel-left κ η

    neededPrecision : ℚ⁺
    neededPrecision =
      (κ *⁺ ε) ⊖ ((κ *⁺ δ) +⁺ (κ *⁺ η)) [ κδη<κε ]

    gδ∼hη-neededPrecision :
      g δ ∼[ neededPrecision ] h η
    gδ∼hη-neededPrecision =
      subst
        (λ ρ → g δ ∼[ ρ ] h η)
        (sym precisionPath)
        gδ∼hη

    gδ∼hκη :
      g δ ∼[ neededPrecision ]
      approximate (scaledCauchyApproximation κ h hCauchy) (κ *⁺ η)
    gδ∼hκη =
      subst
        (λ θ → g δ ∼[ neededPrecision ] h θ)
        (sym ηIndexPath)
        gδ∼hη-neededPrecision

    hκδ∼hκη :
      approximate (scaledCauchyApproximation κ g gCauchy) (κ *⁺ δ)
        ∼[ neededPrecision ]
      approximate (scaledCauchyApproximation κ h hCauchy) (κ *⁺ η)
    hκδ∼hκη =
      subst
        (λ θ →
          g θ ∼[ neededPrecision ]
          approximate (scaledCauchyApproximation κ h hCauchy) (κ *⁺ η))
        (sym δIndexPath)
        gδ∼hκη

  module RationalLipschitzRecursion
    (κ : ℚ⁺) (f : ℚ → ℝᶜ)
    (f-lip : IsRationalLipschitzWithᶜ κ f) =
    Recursion (rationalLipschitzKit κ f f-lip)


extendRationalLipschitzWithᶜ :
  (κ : ℚ⁺) (f : ℚ → ℝᶜ) →
  IsRationalLipschitzWithᶜ κ f →
  ℝᶜ → ℝᶜ
extendRationalLipschitzWithᶜ κ f f-lip =
  RationalLipschitzRecursion.rec κ f f-lip


extendRationalLipschitzWithᶜ-rational :
  (κ : ℚ⁺) (f : ℚ → ℝᶜ)
  (f-lip : IsRationalLipschitzWithᶜ κ f)
  (q : ℚ) →
  extendRationalLipschitzWithᶜ κ f f-lip (rational q) ≡ f q
extendRationalLipschitzWithᶜ-rational κ f f-lip q =
  refl


extendRationalLipschitzWithᶜ-close :
  (κ : ℚ⁺) (f : ℚ → ℝᶜ)
  (f-lip : IsRationalLipschitzWithᶜ κ f) →
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  extendRationalLipschitzWithᶜ κ f f-lip x
    ∼[ κ *⁺ ε ]
  extendRationalLipschitzWithᶜ κ f f-lip y
extendRationalLipschitzWithᶜ-close κ f f-lip =
  RationalLipschitzRecursion.rec-close κ f f-lip


extendRationalLipschitzWithᶜ-lipschitz :
  (κ : ℚ⁺) (f : ℚ → ℝᶜ)
  (f-lip : IsRationalLipschitzWithᶜ κ f) →
  IsLipschitz (extendRationalLipschitzWithᶜ κ f f-lip)
extendRationalLipschitzWithᶜ-lipschitz κ f f-lip =
  (λ ε → posInv⁺ κ *⁺ ε) ,
  λ ε {x = x} {y = y} x∼y →
    subst
      (λ ρ → extendRationalLipschitzWithᶜ κ f f-lip x
        ∼[ ρ ]
        extendRationalLipschitzWithᶜ κ f f-lip y)
      (scale-precision-cancel κ ε)
      (extendRationalLipschitzWithᶜ-close κ f f-lip x∼y)


extendRationalLipschitzWithᶜ-continuous :
  (κ : ℚ⁺) (f : ℚ → ℝᶜ)
  (f-lip : IsRationalLipschitzWithᶜ κ f) →
  IsContinuous (extendRationalLipschitzWithᶜ κ f f-lip)
extendRationalLipschitzWithᶜ-continuous κ f f-lip =
  lipschitz→continuous
    (extendRationalLipschitzWithᶜ-lipschitz κ f f-lip)
