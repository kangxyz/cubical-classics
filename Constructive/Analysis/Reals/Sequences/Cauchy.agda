{-

Cauchy-real Cauchy sequences with explicit moduli

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Sequences.Cauchy where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Modulus
import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.Sequences.Base
open import Constructive.Analysis.Reals.Sequences.Convergence
open import Constructive.Data.PositiveRationals

open ClosenessOf RationalsMetricSpace


CauchyWithModulus :
  Sequence →
  NatModulus →
  Type₀
CauchyWithModulus u μ =
  (ε : ℚ⁺) →
  (m n : ℕ) →
  NatOrder._≤_ (μ ε) m →
  NatOrder._≤_ (μ ε) n →
  u m ∼[ ε ] u n


RegularCauchyWithModulus :
  Sequence →
  NatModulus →
  Type₀
RegularCauchyWithModulus u μ =
  (ε δ : ℚ⁺) →
  u (μ ε) ∼[ ε +⁺ δ ] u (μ δ)


convergesWithModulus→cauchyWithModulus :
  {u : Sequence} →
  {x : ℝᶜ} →
  {μ : NatModulus} →
  ConvergesWithModulus u x μ →
  CauchyWithModulus u (splitModulus μ)
convergesWithModulus→cauchyWithModulus {u = u} u→x ε m n μ≤m μ≤n =
  subst
    (λ ρ → u m ∼[ ρ ] u n)
    (half⁺+half⁺≡ ε)
    (MetricSpace.close-triangle CauchyRealsMetricSpace
      (u→x (half⁺ ε) m μ≤m)
      (close-sym (u→x (half⁺ ε) n μ≤n)))


convergesTo→cauchyWithModulus :
  {u : Sequence} →
  {x : ℝᶜ} →
  ConvergesTo u x →
  Σ[ μ ∈ NatModulus ] CauchyWithModulus u μ
convergesTo→cauchyWithModulus (μ , u→x) =
  splitModulus μ , convergesWithModulus→cauchyWithModulus u→x


cauchyWithAntitone→regular :
  {u : Sequence} →
  {μ : NatModulus} →
  CauchyWithModulus u μ →
  AntitoneNatModulus μ →
  RegularCauchyWithModulus u μ
cauchyWithAntitone→regular {μ = μ} u-cauchy μ-ant ε δ =
  u-cauchy
    (ε +⁺ δ)
    (μ ε)
    (μ δ)
    μsum≤με
    μsum≤μδ
  where
  ε≤sum : radius ε ℚOrder.≤ radius (ε +⁺ δ)
  ε≤sum =
    ℚOrder.<Weaken≤
      (radius ε)
      (radius (ε +⁺ δ))
      (summand-left<sum ε δ)

  δ≤sum : radius δ ℚOrder.≤ radius (ε +⁺ δ)
  δ≤sum =
    ℚOrder.<Weaken≤
      (radius δ)
      (radius (ε +⁺ δ))
      (summand-right<sum ε δ)

  μsum≤με : NatOrder._≤_ (μ (ε +⁺ δ)) (μ ε)
  μsum≤με =
    μ-ant {ε = ε} {δ = ε +⁺ δ} ε≤sum

  μsum≤μδ : NatOrder._≤_ (μ (ε +⁺ δ)) (μ δ)
  μsum≤μδ =
    μ-ant {ε = δ} {δ = ε +⁺ δ} δ≤sum


sequenceCauchyApproximation :
  (u : Sequence) →
  (μ : NatModulus) →
  RegularCauchyWithModulus u μ →
  MetricCauchy.CauchyApproximation CauchyRealsMetricSpace
sequenceCauchyApproximation u μ u-regular =
  MetricCauchy.cauchy-approximation
    (λ ε → u (μ ε))
    u-regular


regularCauchyLimit :
  (u : Sequence) →
  (μ : NatModulus) →
  (u-regular : RegularCauchyWithModulus u μ) →
  MetricCauchy.CauchyLimit
    (sequenceCauchyApproximation u μ u-regular)
regularCauchyLimit u μ u-regular =
  CauchyRealsIsCauchyComplete
    (sequenceCauchyApproximation u μ u-regular)


cauchyLimit :
  (u : Sequence) →
  (μ : NatModulus) →
  RegularCauchyWithModulus u μ →
  ℝᶜ
cauchyLimit u μ u-regular =
  MetricCauchy.limitPoint
    (regularCauchyLimit u μ u-regular)


regularCauchyLimitConverges :
  (u : Sequence) →
  (μ : NatModulus) →
  (u-regular : RegularCauchyWithModulus u μ) →
  MetricCauchy.ConvergesTo
    (sequenceCauchyApproximation u μ u-regular)
    (cauchyLimit u μ u-regular)
regularCauchyLimitConverges u μ u-regular =
  MetricCauchy.converges
    (regularCauchyLimit u μ u-regular)


cauchyWithAntitoneLimit :
  (u : Sequence) →
  (μ : NatModulus) →
  CauchyWithModulus u μ →
  AntitoneNatModulus μ →
  ℝᶜ
cauchyWithAntitoneLimit u μ u-cauchy μ-ant =
  cauchyLimit u μ
    (cauchyWithAntitone→regular u-cauchy μ-ant)


cauchyWithAntitoneLimitConverges :
  (u : Sequence) →
  (μ : NatModulus) →
  (u-cauchy : CauchyWithModulus u μ) →
  (μ-ant : AntitoneNatModulus μ) →
  ConvergesWithModulus
    u
    (cauchyWithAntitoneLimit u μ u-cauchy μ-ant)
    (splitModulus μ)
cauchyWithAntitoneLimitConverges u μ u-cauchy μ-ant ε n μhalf≤n =
  subst
    (λ ρ → u n ∼[ ρ ] cauchyWithAntitoneLimit u μ u-cauchy μ-ant)
    (half⁺+half⁺≡ ε)
    (MetricSpace.close-triangle CauchyRealsMetricSpace u∼approx approx∼lim)
  where
  α : ℚ⁺
  α =
    half⁺ ε

  β : ℚ⁺
  β =
    quarter⁺ ε

  β<α : β <⁺ α
  β<α =
    half< (half⁺ ε)

  α≤? : radius β ℚOrder.≤ radius α
  α≤? =
    ℚOrder.<Weaken≤ (radius β) (radius α) β<α

  μα≤μβ : NatOrder._≤_ (μ α) (μ β)
  μα≤μβ =
    μ-ant {ε = β} {δ = α} α≤?

  u-regular : RegularCauchyWithModulus u μ
  u-regular =
    cauchyWithAntitone→regular u-cauchy μ-ant

  lim :
    MetricCauchy.CauchyLimit
      (sequenceCauchyApproximation u μ u-regular)
  lim =
    regularCauchyLimit u μ u-regular

  u∼approx : u n ∼[ α ] u (μ β)
  u∼approx =
    u-cauchy α n (μ β) μhalf≤n μα≤μβ

  lim∼approx :
    cauchyWithAntitoneLimit u μ u-cauchy μ-ant ∼[ α ] u (μ β)
  lim∼approx =
    MetricCauchy.converges lim α β β<α

  approx∼lim :
    u (μ β) ∼[ α ] cauchyWithAntitoneLimit u μ u-cauchy μ-ant
  approx∼lim =
    close-sym lim∼approx


cauchyWithAntitoneConvergesTo :
  (u : Sequence) →
  (μ : NatModulus) →
  (u-cauchy : CauchyWithModulus u μ) →
  (μ-ant : AntitoneNatModulus μ) →
  ConvergesTo
    u
    (cauchyWithAntitoneLimit u μ u-cauchy μ-ant)
cauchyWithAntitoneConvergesTo u μ u-cauchy μ-ant =
  splitModulus μ ,
  cauchyWithAntitoneLimitConverges u μ u-cauchy μ-ant


cauchyWithAntitoneLimitUnique :
  (u : Sequence) →
  (μ : NatModulus) →
  (u-cauchy : CauchyWithModulus u μ) →
  (μ-ant : AntitoneNatModulus μ) →
  {x : ℝᶜ} →
  ConvergesTo u x →
  cauchyWithAntitoneLimit u μ u-cauchy μ-ant ≡ x
cauchyWithAntitoneLimitUnique u μ u-cauchy μ-ant (ν , u→x) =
  limitUniqueWithModuli
    {μ = splitModulus μ}
    {ν = ν}
    (cauchyWithAntitoneLimitConverges u μ u-cauchy μ-ant)
    u→x
