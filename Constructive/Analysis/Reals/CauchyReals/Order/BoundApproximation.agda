{-

Cauchy-real boundedness and rational bounds

-}
{-# OPTIONS --safe #-}

module Constructive.Analysis.Reals.CauchyReals.Order.BoundApproximation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ; Σ-syntax; _,_; _×_)
open import Cubical.Data.Sum as Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarOrder
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace
open import Constructive.Analysis.Reals.CauchyReals.Extension
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Approximation
open import Constructive.Analysis.Reals.CauchyReals.Order.BoundDefinitions
open import Constructive.Analysis.Reals.CauchyReals.Order.BoundOperations
open import Constructive.Analysis.Reals.CauchyReals.Order.Density
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive using (≤ᶜ-add)
open import Constructive.Data.PositiveRationals
open import Constructive.Data.Rationals.Closeness
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    diff-plus-cancel :
      (q φ : 𝓡 .fst) →
      (q + (- φ)) + φ ≡ q
    diff-plus-cancel _ _ = solve! 𝓡

    diff-zero-right :
      (q : 𝓡 .fst) →
      q + (- 0r) ≡ q
    diff-zero-right _ = solve! 𝓡

    zero-diff :
      (q : 𝓡 .fst) →
      0r + (- q) ≡ - q
    zero-diff _ = solve! 𝓡

    bounded-close-precision :
      (θ δ η : 𝓡 .fst) →
      θ + (δ + η) ≡ δ + (θ + η)
    bounded-close-precision _ _ _ = solve! 𝓡

  diff≤→≤+ :
    (q δ φ : ℚ) →
    q ℚ.- φ ℚOrder.≤ δ →
    q ℚOrder.≤ δ ℚ.+ φ
  diff≤→≤+ q δ φ q-φ≤δ =
    subst
      (λ s → s ℚOrder.≤ δ ℚ.+ φ)
      (SolverHelpers.diff-plus-cancel ℚCommRing q φ)
      (ℚOrder.≤-+o (q ℚ.- φ) δ φ q-φ≤δ)

  diff-zero-right :
    (q : ℚ) →
    q ℚ.- 0ℚ ≡ q
  diff-zero-right =
    SolverHelpers.diff-zero-right ℚCommRing

  zero-diff :
    (q : ℚ) →
    0ℚ ℚ.- q ≡ ℚ.- q
  zero-diff =
    SolverHelpers.zero-diff ℚCommRing

  product-bound< :
    (δ ε κ : ℚ⁺) →
    δ <⁺ ε →
    δ *⁺ κ <⁺ κ *⁺ ε
  product-bound< δ ε κ δ<ε =
    subst
      (λ ρ → ρ ℚOrder.< radius (κ *⁺ ε))
      (sym (ℚ.·Comm (radius δ) (radius κ)))
      (Rational.mul-left-positive-<
        {a = radius κ}
        {b = radius δ}
        {c = radius ε}
        (κ .snd)
        δ<ε)

bounded-approximation-rational-boundᶜ :
  (κ φ η θ : ℚ⁺) (x : ℝᶜ) (q : ℚ) →
  θ <⁺ φ →
  φ <⁺ η →
  BoundedByᶜ κ x →
  x ∼[ θ ] rational q →
  RationalBoundᶜ (κ +⁺ η) q
bounded-approximation-rational-boundᶜ κ φ η θ x q θ<φ φ<η bound x∼q =
  rational-boundᶜ {κ = κ +⁺ η} {q = q} q<κ+η -q<κ+η
  where
  κ+φ<κ+η : radius (κ +⁺ φ) ℚOrder.< radius (κ +⁺ η)
  κ+φ<κ+η =
    ℚOrder.<-o+ (radius φ) (radius η) (radius κ) φ<η

  q-φ≤x : rational (q ℚ.- radius φ) ≤ᶜ x
  q-φ≤x =
    close-rational-lower-bound x q θ φ θ<φ x∼q

  q-φ≤κᶜ : rational (q ℚ.- radius φ) ≤ᶜ rational (radius κ)
  q-φ≤κᶜ =
    ≤ᶜ-trans
      {x = rational (q ℚ.- radius φ)}
      {y = x}
      {z = rational (radius κ)}
      q-φ≤x
      (upperᶜ {κ = κ} {x = x} bound)

  q≤κ+φ : q ℚOrder.≤ radius (κ +⁺ φ)
  q≤κ+φ =
    diff≤→≤+
      q
      (radius κ)
      (radius φ)
      (rational≤ᶜ→≤ℚ q-φ≤κᶜ)

  q<κ+η : q ℚOrder.< radius (κ +⁺ η)
  q<κ+η =
    Rational.≤<-trans
      {p = q}
      {q = radius (κ +⁺ φ)}
      {r = radius (κ +⁺ η)}
      q≤κ+φ
      κ+φ<κ+η

  -q-φ≤-x : rational ((ℚ.- q) ℚ.- radius φ) ≤ᶜ (-ᶜ x)
  -q-φ≤-x =
    close-rational-lower-bound
      (-ᶜ x)
      (ℚ.- q)
      θ
      φ
      θ<φ
      (neg-close x∼q)

  -q-φ≤κᶜ : rational ((ℚ.- q) ℚ.- radius φ) ≤ᶜ rational (radius κ)
  -q-φ≤κᶜ =
    ≤ᶜ-trans
      {x = rational ((ℚ.- q) ℚ.- radius φ)}
      {y = -ᶜ x}
      {z = rational (radius κ)}
      -q-φ≤-x
      (lowerᶜ {κ = κ} {x = x} bound)

  -q≤κ+φ : ℚ.- q ℚOrder.≤ radius (κ +⁺ φ)
  -q≤κ+φ =
    diff≤→≤+
      (ℚ.- q)
      (radius κ)
      (radius φ)
      (rational≤ᶜ→≤ℚ -q-φ≤κᶜ)

  -q<κ+η : ℚ.- q ℚOrder.< radius (κ +⁺ η)
  -q<κ+η =
    Rational.≤<-trans
      {p = ℚ.- q}
      {q = radius (κ +⁺ φ)}
      {r = radius (κ +⁺ η)}
      -q≤κ+φ
      κ+φ<κ+η


bounded-byᶜ-close-zero :
  (κ μ : ℚ⁺) (x : ℝᶜ) →
  BoundedByᶜ κ x →
  κ <⁺ μ →
  x ∼[ μ ] 0ᶜ
bounded-byᶜ-close-zero κ μ x bound κ<μ =
  Prop.rec squash step (rational-approximation x θ)
  where
  gap : ℚ⁺
  gap = μ ⊖ κ [ κ<μ ]

  φ θ η zeta : ℚ⁺
  φ = quarter⁺ gap
  θ = half⁺ φ
  η = φ +⁺ φ
  zeta = κ +⁺ η

  θ<φ : θ <⁺ φ
  θ<φ =
    half< φ

  φ<η : φ <⁺ η
  φ<η =
    summand-left<sum φ φ

  κ+φ<zeta : radius (κ +⁺ φ) ℚOrder.< radius zeta
  κ+φ<zeta =
    ℚOrder.<-o+ (radius φ) (radius η) (radius κ) φ<η

  θ+η<gap : radius (θ +⁺ η) ℚOrder.< radius gap
  θ+η<gap =
    ℚOrder.isTrans<
      (radius (θ +⁺ η))
      (radius (η +⁺ φ))
      (radius gap)
      θ+η<η+φ
      η+φ<gap
    where
    θ+η<η+φ : radius (θ +⁺ η) ℚOrder.< radius (η +⁺ φ)
    θ+η<η+φ =
      subst
        (λ ρ → ρ ℚOrder.< radius (η +⁺ φ))
        (ℚ.+Comm (radius η) (radius θ))
        (ℚOrder.<-o+ (radius θ) (radius φ) (radius η) θ<φ)

    η+φ<gap : radius (η +⁺ φ) ℚOrder.< radius gap
    η+φ<gap =
      three-quarter< gap

  θ+zeta<μ : θ +⁺ zeta <⁺ μ
  θ+zeta<μ =
    subst
      (λ ρ → ρ ℚOrder.< radius μ)
      (sym
        (SolverHelpers.bounded-close-precision
          ℚCommRing
          (radius θ)
          (radius κ)
          (radius η)))
      (sum<from-difference μ κ (θ +⁺ η) κ<μ θ+η<gap)

  step :
    Σ[ q ∈ ℚ ] x ∼[ θ ] rational q →
    x ∼[ μ ] 0ᶜ
  step (q , x∼q) =
    close-mono
      {ε = θ +⁺ zeta}
      {δ = μ}
      θ+zeta<μ
      (close-triangle
        x∼q
        (point-point-close q 0ℚ zeta q∼0))
    where
    q-φ≤x : rational (q ℚ.- radius φ) ≤ᶜ x
    q-φ≤x =
      close-rational-lower-bound x q θ φ θ<φ x∼q

    q-φ≤κᶜ : rational (q ℚ.- radius φ) ≤ᶜ rational (radius κ)
    q-φ≤κᶜ =
      ≤ᶜ-trans
        {x = rational (q ℚ.- radius φ)}
        {y = x}
        {z = rational (radius κ)}
        q-φ≤x
        (upperᶜ {κ = κ} {x = x} bound)

    q≤κ+φ : q ℚOrder.≤ radius (κ +⁺ φ)
    q≤κ+φ =
      diff≤→≤+
        q
        (radius κ)
        (radius φ)
        (rational≤ᶜ→≤ℚ q-φ≤κᶜ)

    -q-φ≤-x : rational ((ℚ.- q) ℚ.- radius φ) ≤ᶜ (-ᶜ x)
    -q-φ≤-x =
      close-rational-lower-bound
        (-ᶜ x)
        (ℚ.- q)
        θ
        φ
        θ<φ
        (neg-close x∼q)

    -q-φ≤κᶜ : rational ((ℚ.- q) ℚ.- radius φ) ≤ᶜ rational (radius κ)
    -q-φ≤κᶜ =
      ≤ᶜ-trans
        {x = rational ((ℚ.- q) ℚ.- radius φ)}
        {y = -ᶜ x}
        {z = rational (radius κ)}
        -q-φ≤-x
        (lowerᶜ {κ = κ} {x = x} bound)

    -q≤κ+φ : ℚ.- q ℚOrder.≤ radius (κ +⁺ φ)
    -q≤κ+φ =
      diff≤→≤+
        (ℚ.- q)
        (radius κ)
        (radius φ)
        (rational≤ᶜ→≤ℚ -q-φ≤κᶜ)

    q<zeta : q ℚOrder.< radius zeta
    q<zeta =
      Rational.≤<-trans
        {p = q}
        {q = radius (κ +⁺ φ)}
        {r = radius zeta}
        q≤κ+φ
        κ+φ<zeta

    -q<zeta : ℚ.- q ℚOrder.< radius zeta
    -q<zeta =
      Rational.≤<-trans
        {p = ℚ.- q}
        {q = radius (κ +⁺ φ)}
        {r = radius zeta}
        -q≤κ+φ
        κ+φ<zeta

    q∼0 : Closeℚ q zeta 0ℚ
    q∼0 =
      subst
        (λ ρ → ρ ℚOrder.< radius zeta)
        (sym (diff-zero-right q))
        q<zeta ,
      subst
        (λ ρ → ρ ℚOrder.< radius zeta)
        (sym (zero-diff q))
        -q<zeta


bounded-small-scalar-close-zeroᶜ :
  (κ : ℚ⁺) (x : ℝᶜ) →
  BoundedByᶜ κ x →
  (a : ℚ) (ε : ℚ⁺) →
  RationalBoundᶜ ε a →
  scalarMulᶜ a x ∼[ κ *⁺ ε ] 0ᶜ
bounded-small-scalar-close-zeroᶜ κ x x-bound a ε a-bound =
  Prop.rec squash step rounded-bound
  where
  close-zero→bound :
    (δ : ℚ⁺) →
    Closeℚ a δ 0ℚ →
    RationalBoundᶜ δ a
  close-zero→bound δ a∼0 =
    rational-boundᶜ {κ = δ} {q = a}
      (subst
        (λ ρ → ρ ℚOrder.< radius δ)
        (diff-zero-right a)
        (a∼0 .fst))
      (subst
        (λ ρ → ρ ℚOrder.< radius δ)
        (zero-diff a)
        (a∼0 .snd))

  a∼0 : Closeℚ a ε 0ℚ
  a∼0 =
    subst
      (λ ρ → ρ ℚOrder.< radius ε)
      (sym (diff-zero-right a))
      (upperℚ {κ = ε} {q = a} a-bound) ,
    subst
      (λ ρ → ρ ℚOrder.< radius ε)
      (sym (zero-diff a))
      (lowerℚ {κ = ε} {q = a} a-bound)

  rounded-bound :
    ∥ Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × RationalBoundᶜ δ a ∥₁
  rounded-bound =
    Prop.rec squash₁
      (λ (δ , δ<ε , a∼δ0) →
        ∣ δ , δ<ε , close-zero→bound δ a∼δ0 ∣₁)
      (rational-close-rounded a 0ℚ ε a∼0)

  step :
    Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × RationalBoundᶜ δ a →
    scalarMulᶜ a x ∼[ κ *⁺ ε ] 0ᶜ
  step (δ , δ<ε , aδ-bound) =
    bounded-byᶜ-close-zero
      (δ *⁺ κ)
      (κ *⁺ ε)
      (scalarMulᶜ a x)
      (bounded-byᶜ-scale-rational-bound a κ δ x aδ-bound x-bound)
      (product-bound< δ ε κ δ<ε)


rational-approximation-boundᶜ :
  (x : ℝᶜ) (q : ℚ) →
  x ∼[ half⁺ 1⁺ ] rational q →
  BoundedByᶜ (scalar-bound q) x
rational-approximation-boundᶜ x q x∼q =
  bounded-byᶜ {κ = scalar-bound q} {x = x}
    (≤ᶜ-trans
      {x = x}
      {y = rational (q ℚ.+ 1ℚ)}
      {z = rational (radius (scalar-bound q))}
      x≤q+1
      q+1≤bound)
    (≤ᶜ-trans
      {x = -ᶜ x}
      {y = rational ((ℚ.- q) ℚ.+ 1ℚ)}
      {z = rational (radius (scalar-bound q))}
      -x≤-q+1
      -q+1≤bound)
  where
  δ : ℚ⁺
  δ = half⁺ 1⁺

  δ<1 : δ <⁺ 1⁺
  δ<1 =
    half< 1⁺

  x≤q+1 : x ≤ᶜ rational (q ℚ.+ 1ℚ)
  x≤q+1 =
    close-rational-upper-bound x q δ 1⁺ δ<1 x∼q

  -x≤-q+1 : (-ᶜ x) ≤ᶜ rational ((ℚ.- q) ℚ.+ 1ℚ)
  -x≤-q+1 =
    close-rational-upper-bound (-ᶜ x) (ℚ.- q) δ 1⁺ δ<1 (neg-close x∼q)

  q+1≤boundℚ : q ℚ.+ 1ℚ ℚOrder.≤ radius (scalar-bound q)
  q+1≤boundℚ =
    ℚOrder.≤-+o
      q
      (ℚ.max q (ℚ.- q))
      1ℚ
      (ℚOrder.≤max q (ℚ.- q))

  -q+1≤boundℚ : (ℚ.- q) ℚ.+ 1ℚ ℚOrder.≤ radius (scalar-bound q)
  -q+1≤boundℚ =
    ℚOrder.≤-+o
      (ℚ.- q)
      (ℚ.max q (ℚ.- q))
      1ℚ
      (Rational.≤max-r q (ℚ.- q))

  q+1≤bound : rational (q ℚ.+ 1ℚ) ≤ᶜ rational (radius (scalar-bound q))
  q+1≤bound =
    ≤ℚ→rational≤ᶜ q+1≤boundℚ

  -q+1≤bound : rational ((ℚ.- q) ℚ.+ 1ℚ) ≤ᶜ rational (radius (scalar-bound q))
  -q+1≤bound =
    ≤ℚ→rational≤ᶜ -q+1≤boundℚ


merely-boundedᶜ :
  (x : ℝᶜ) →
  ∥ Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ x ∥₁
merely-boundedᶜ x =
  Prop.rec squash₁ step (rational-approximation x (half⁺ 1⁺))
  where
  step :
    Σ[ q ∈ ℚ ] x ∼[ half⁺ 1⁺ ] rational q →
    ∥ Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ x ∥₁
  step (q , x∼q) =
    ∣ scalar-bound q , rational-approximation-boundᶜ x q x∼q ∣₁
