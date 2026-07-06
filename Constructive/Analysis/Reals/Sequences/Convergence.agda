{-

Convergence of Cauchy-real sequences with explicit moduli

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Sequences.Convergence where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Base
import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.Sequences.Base
open import Constructive.Data.PositiveRationals

open ClosenessOf RationalsMetricSpace


ConvergesWithModulus :
  Sequence →
  ℝᶜ →
  NatModulus →
  Type₀
ConvergesWithModulus u x μ =
  (ε : ℚ⁺) →
  (n : ℕ) →
  NatOrder._≤_ (μ ε) n →
  u n ∼[ ε ] x


ConvergesTo :
  Sequence →
  ℝᶜ →
  Type₀
ConvergesTo u x =
  Σ[ μ ∈ NatModulus ] ConvergesWithModulus u x μ


Limit :
  Sequence →
  Type₀
Limit u =
  Σ[ x ∈ ℝᶜ ] ConvergesTo u x


constantConvergesWithModulus :
  (x : ℝᶜ) →
  (μ : NatModulus) →
  ConvergesWithModulus (constantSequence x) x μ
constantConvergesWithModulus x μ ε n μ≤n =
  close-refl x ε


constantConvergesTo :
  (x : ℝᶜ) →
  ConvergesTo (constantSequence x) x
constantConvergesTo x =
  (λ _ → zero) , constantConvergesWithModulus x (λ _ → zero)


convergesWithModulus-mono :
  {u : Sequence} →
  {x : ℝᶜ} →
  {μ : NatModulus} →
  ConvergesWithModulus u x μ →
  {ε δ : ℚ⁺} →
  radius ε ℚOrder.≤ radius δ →
  (n : ℕ) →
  NatOrder._≤_ (μ ε) n →
  u n ∼[ δ ] x
convergesWithModulus-mono u→x ε≤δ n μ≤n =
  MetricCauchy.close-mono-≤
    CauchyRealsMetricSpace
    ε≤δ
    (u→x _ n μ≤n)


convergesWithModulus-weakenIndex :
  {u : Sequence} →
  {x : ℝᶜ} →
  {μ : NatModulus} →
  ConvergesWithModulus u x μ →
  (ε : ℚ⁺) →
  {m n : ℕ} →
  NatOrder._≤_ (μ ε) m →
  NatOrder._≤_ m n →
  u n ∼[ ε ] x
convergesWithModulus-weakenIndex u→x ε μ≤m m≤n =
  u→x ε _ (NatOrder.≤-trans μ≤m m≤n)


limitUniqueWithModuli :
  {u : Sequence} →
  {x y : ℝᶜ} →
  {μ ν : NatModulus} →
  ConvergesWithModulus u x μ →
  ConvergesWithModulus u y ν →
  x ≡ y
limitUniqueWithModuli {u = u} {x = x} {y = y} {μ = μ} {ν = ν} u→x u→y =
  MetricSpace.close-separated CauchyRealsMetricSpace x y closeAt
  where
  closeAt : (ε : ℚ⁺) → x ∼[ ε ] y
  closeAt ε =
    subst
      (λ ρ → x ∼[ ρ ] y)
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle CauchyRealsMetricSpace x∼u u∼y)
    where
    α : ℚ⁺
    α =
      half⁺ ε

    n : ℕ
    n =
      maxModulus μ ν α

    μ≤n : NatOrder._≤_ (μ α) n
    μ≤n =
      maxModulus-left≤ μ ν α

    ν≤n : NatOrder._≤_ (ν α) n
    ν≤n =
      maxModulus-right≤ μ ν α

    x∼u : x ∼[ α ] u n
    x∼u =
      close-sym (u→x α n μ≤n)

    u∼y : u n ∼[ α ] y
    u∼y =
      u→y α n ν≤n


limitUnique :
  {u : Sequence} →
  (a b : Limit u) →
  a .fst ≡ b .fst
limitUnique (x , μ , u→x) (y , ν , u→y) =
  limitUniqueWithModuli
    {x = x}
    {y = y}
    {μ = μ}
    {ν = ν}
    u→x
    u→y


convergesToPath :
  {u : Sequence} →
  {x y : ℝᶜ} →
  ConvergesTo u x →
  ConvergesTo u y →
  x ≡ y
convergesToPath (μ , u→x) (ν , u→y) =
  limitUniqueWithModuli
    {μ = μ}
    {ν = ν}
    u→x
    u→y
