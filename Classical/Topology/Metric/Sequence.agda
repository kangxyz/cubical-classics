{-

Sequence in Metric Space

This file contains:
- Basics of sequence (of points) in metric space;
- The notion of convergence and limit of sequences;
- The notion of cluster points;
- The notion of Cauchy sequence;
- The notion of Cauchy completeness.

-}
{-# OPTIONS --safe #-}
module Classical.Topology.Metric.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using ()
  renaming (_>_ to _>ℕ_ ; _<_ to _<ℕ_
          ; _≥_ to _≥ℕ_ ; _≤_ to _≤ℕ_
          ; isProp≤  to isProp≤ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad

open import Classical.Axioms
open import Classical.Foundations.Powerset
open import Classical.Preliminary.Nat
open import Constructive.Algebra.StrictlyOrderedField
open import Classical.Topology.Metric
open import Classical.Analysis.Real.Base

private
  variable
    ℓ : Level


module _ ⦃ 🤖 : Oracle ⦄
  {X : Type ℓ} ⦃ 𝓂 : Metric X ⦄ where

  open Oracle 🤖

  open StrictlyOrderedFieldStr (ℝMacNeilleCompleteOrderedField .fst)
  open Metric 𝓂


  {-

    Convergence and Limit of Sequence in Metric Spaces

  -}

  -- A sequence seq converges to a point x
  -- if for any ε > 0 there merely exists n₀ : ℕ
  -- such that whenever n > n₀,
  -- the distance between x and seq n is smaller than ε.

  isConvergentTo : (ℕ → X) → X → Type
  isConvergentTo seq x = (ε : ℝ) → ε > 0 → ∥ Σ[ n₀ ∈ ℕ ] ((n : ℕ) → n >ℕ n₀ → dist x (seq n) < ε) ∥₁

  isPropIsConvergentTo : {seq : ℕ → X}{x : X} → isProp (isConvergentTo seq x)
  isPropIsConvergentTo = isPropΠ2 (λ _ _ → squash₁)

  record Limit (seq : ℕ → X) : Type ℓ where
    field
      lim : X
      conv : isConvergentTo seq lim

  open Limit


  -- A stronger version with explicit existence,
  -- but they turn out to be (logically) equivalent.

  isConvergentToΣ : (ℕ → X) → X → Type
  isConvergentToΣ seq x = (ε : ℝ) → ε > 0 → Σ[ n₀ ∈ ℕ ] ((n : ℕ) → n >ℕ n₀ → dist x (seq n) < ε)

  isConvergentTo→isConvergentToΣ : {seq : ℕ → X}{x : X} → isConvergentTo seq x → isConvergentToΣ seq x
  isConvergentTo→isConvergentToΣ converge ε ε>0 = findByOracle (λ _ → isPropΠ2 (λ _ _ → isProp<)) (converge ε ε>0)


  -- The uniqueness of limit

  isPropLimit : {seq : ℕ → X} → isProp (Limit seq)
  isPropLimit {seq = seq} p q i .conv =
    isProp→PathP (λ i → isPropIsConvergentTo {x = isPropLimit p q i .lim}) (p .conv) (q .conv) i
  isPropLimit {seq = seq} p q i .lim = infinitelyClose→≡ ∣x-y∣<ε i
    where

    module _ (ε : ℝ)(ε>0 : ε > 0) where

      ε/2 = middle 0 ε
      ε/2>0 = middle>l ε>0

      ∣x-y∣<ε : dist (p .lim) (q .lim) < ε
      ∣x-y∣<ε = proof (_ , isProp<) by do
        (n₀ , abs<₀) ← p .conv ε/2 ε/2>0
        (n₁ , abs<₁) ← q .conv ε/2 ε/2>0
        let n = sucmax n₀ n₁
        return (dist-triangle<ε ε>0
          (abs<₀ _ (sucmax>left {m = n₀} {n = n₁}))
          (subst (_< ε/2) (dist-symm (q .lim) (seq n)) (abs<₁ _ (sucmax>right {m = n₀} {n = n₁}))))


  {-

    Cluster Points

  -}

  -- A point x is a cluster point of a sequence seq
  -- if for any n : ℕ and ε > 0 there merely exists n₀ : ℕ
  -- such that the distance between x and seq n₀ is smaller than ε.

  isClusteringAt : (ℕ → X) → X → Type
  isClusteringAt seq x = (n₀ : ℕ)(ε : ℝ) → ε > 0 → ∥ Σ[ n ∈ ℕ ] (n₀ <ℕ n) × (dist x (seq n) < ε) ∥₁

  isPropIsClusteringAt :  {seq : ℕ → X}{x : X} → isProp (isClusteringAt seq x)
  isPropIsClusteringAt = isPropΠ3 (λ _ _ _ → squash₁)

  record ClusterPoint (seq : ℕ → X) : Type ℓ where
    field
      point : X
      accum : isClusteringAt seq point

  open ClusterPoint


  -- A stronger version with explicit existence,
  -- but they turn out to be (logically) equivalent.

  isClusteringAtΣ : (ℕ → X) → X → Type
  isClusteringAtΣ seq x = (n₀ : ℕ)(ε : ℝ) → ε > 0 → Σ[ n ∈ ℕ ] (n₀ <ℕ n) × (dist x (seq n) < ε)

  isClusteringAt→isClusteringAtΣ : {seq : ℕ → X}{x : X} → isClusteringAt seq x → isClusteringAtΣ seq x
  isClusteringAt→isClusteringAtΣ cluster n₀ ε ε>0 = findByOracle (λ _ → isProp× isProp≤ℕ isProp<) (cluster n₀ ε ε>0)


  {-

    Cauchy Sequence

  -}

  -- A sequence seq is a Cauchy sequence
  -- if for any ε > 0 there merely exists N : ℕ
  -- such that whenever m n > N,
  -- the distance between seq m and seq n is smaller than ε.
  -- In other words, the terms crowd together as n approaches infinity.

  isCauchy : (ℕ → X) → Type
  isCauchy seq = (ε : ℝ) → ε > 0 → ∥ Σ[ N ∈ ℕ ] ((m n : ℕ) → m >ℕ N → n >ℕ N → dist (seq m) (seq n) < ε) ∥₁


  -- A stronger version with explicit existence,
  -- but they turn out to be (logically) equivalent.

  isCauchyΣ : (ℕ → X) → Type
  isCauchyΣ seq = (ε : ℝ) → ε > 0 → Σ[ N ∈ ℕ ] ((m n : ℕ) → m >ℕ N → n >ℕ N → dist (seq m) (seq n) < ε)

  isCauchy→isCauchyΣ : {seq : ℕ → X}{x : X} → isCauchy seq → isCauchyΣ seq
  isCauchy→isCauchyΣ cauchy ε ε>0 = findByOracle (λ _ → isPropΠ4 (λ _ _ _ _ → isProp<)) (cauchy ε ε>0)


  -- A metric space is Cauchy complete if every Cauchy sequence has a limit.

  isCauchyComplete : Type ℓ
  isCauchyComplete = {seq : ℕ → X} → isCauchy seq → Limit seq
