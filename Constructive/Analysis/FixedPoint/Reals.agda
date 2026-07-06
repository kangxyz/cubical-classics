{-

Cauchy-real fixed-point corollaries

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.FixedPoint.Reals where

open import Cubical.Foundations.Prelude
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational
open import Constructive.Analysis.FixedPoint.Base
open import Constructive.Analysis.FixedPoint.Banach


CauchyRealsFixedPoint :
  (ℝᶜ → ℝᶜ) →
  Type₀
CauchyRealsFixedPoint =
  FixedPoint {𝓜 = CauchyRealsMetricSpace}


CauchyRealsContraction :
  Type₀
CauchyRealsContraction =
  Contraction CauchyRealsMetricSpace


CauchyRealsPicardSeed :
  (ℝᶜ → ℝᶜ) →
  Type₀
CauchyRealsPicardSeed =
  PicardSeed CauchyRealsMetricSpace


cauchyRealsBanachFixedPoint :
  (c : CauchyRealsContraction) →
  CauchyRealsPicardSeed (Contraction.map c) →
  CauchyRealsFixedPoint (Contraction.map c)
cauchyRealsBanachFixedPoint c seed =
  banachFixedPoint
    CauchyRealsMetricSpace
    CauchyRealsIsCauchyComplete
    c
    seed


cauchyRealsBanachFrom :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  (f : ℝᶜ → ℝᶜ) →
  IsContractionWith CauchyRealsMetricSpace ρ f →
  (x₀ : ℝᶜ) →
  (η : ℚ⁺) →
  MetricSpace.Close CauchyRealsMetricSpace x₀ η (f x₀) →
  CauchyRealsFixedPoint f
cauchyRealsBanachFrom ρ ρ<1 f f-contr x₀ η x₀∼fx₀ =
  banachFrom
    CauchyRealsMetricSpace
    CauchyRealsIsCauchyComplete
    ρ
    ρ<1
    f
    f-contr
    x₀
    η
    x₀∼fx₀


cauchyRealsBanachUniqueWithBound :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  {f : ℝᶜ → ℝᶜ} →
  IsContractionWith CauchyRealsMetricSpace ρ f →
  (p q : ℝᶜ) →
  f p ≡ p →
  f q ≡ q →
  CloseBound CauchyRealsMetricSpace p q →
  p ≡ q
cauchyRealsBanachUniqueWithBound ρ ρ<1 f-contr p q fp≡p fq≡q p∼q =
  banachUniqueWithBound
    CauchyRealsMetricSpace
    ρ
    ρ<1
    f-contr
    p
    q
    fp≡p
    fq≡q
    p∼q
