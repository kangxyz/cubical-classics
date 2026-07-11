{- Convergence of Cauchy products from explicit remainder control. -}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.CauchyProduct.Convergence where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using
    ( BoundedByᶜ
    ; bounded-byᶜ
    ; bounded-byᶜ-close-zero
    ; diff-close-zero→close
    )
open import Constructive.Analysis.Reals.Series.Finite using (partialSum)
open import Constructive.Analysis.Reals.Series.Tail using (TailBound)
open import Constructive.Analysis.Reals.Series.Cauchy
  using
    ( partialSumSequence
    ; seriesSumFromFiniteTailBound
    ; seriesSumFromFiniteTailBoundConvergesTo
    )
open import Constructive.Data.PositiveRationals

open ClosenessOf RationalsMetricSpace

import Constructive.Analysis.Reals.Sequences.Algebra as SeqAlg
import Constructive.Analysis.Reals.Sequences.Convergence as SeqConv
import Constructive.Analysis.Reals.Sequences.Order as SeqOrder
open import Constructive.Analysis.Modulus
  using
    ( AntitoneNatModulus
    ; maxModulus
    ; maxModulus-left≤
    ; maxModulus-right≤
    )

open import Constructive.Analysis.Reals.Series.CauchyProduct.Finite

seriesSumFromFiniteTailBound-cong :
  {u v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  (u≡v : u ≡ v) →
  (uTail : TailBound u μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  seriesSumFromFiniteTailBound u μ uTail μ-antitone ≡
  seriesSumFromFiniteTailBound
    v
    μ
    (subst (λ w → TailBound w μ) u≡v uTail)
    μ-antitone
seriesSumFromFiniteTailBound-cong {u = u} {v = v} {μ = μ}
    u≡v uTail μ-antitone =
  SeqConv.convergesToPath u-as-v-converges v-converges
  where
  sumU : ℝᶜ
  sumU =
    seriesSumFromFiniteTailBound u μ uTail μ-antitone

  vTail : TailBound v μ
  vTail =
    subst (λ w → TailBound w μ) u≡v uTail

  u-converges :
    SeqConv.ConvergesTo (partialSumSequence u) sumU
  u-converges =
    seriesSumFromFiniteTailBoundConvergesTo u μ uTail μ-antitone

  u-as-v-converges :
    SeqConv.ConvergesTo (partialSumSequence v) sumU
  u-as-v-converges =
    SeqOrder.eventuallyEqualPreservesConvergesTo
      u-converges
      (λ _ n _ → cong (λ w → partialSum w n) u≡v)

  v-converges :
    SeqConv.ConvergesTo
      (partialSumSequence v)
      (seriesSumFromFiniteTailBound v μ vTail μ-antitone)
  v-converges =
    seriesSumFromFiniteTailBoundConvergesTo v μ vTail μ-antitone


rectangularTriangularRemainderConvergesFromBound :
  (u v : ℕ → ℝᶜ) →
  (χ : ℚ⁺ → ℕ) →
  ((ε : ℚ⁺) →
    (n : ℕ) →
    NatOrder._≤_ (χ ε) n →
    BoundedByᶜ ε (rectangularTriangularRemainder u v n n)) →
  SeqConv.ConvergesWithModulus
    (λ n → rectangularTriangularRemainder u v n n)
    0ᶜ
    (λ ε → χ (half⁺ ε))
rectangularTriangularRemainderConvergesFromBound u v χ remainderBound ε n χ≤n =
  bounded-byᶜ-close-zero
    (half⁺ ε)
    ε
    (rectangularTriangularRemainder u v n n)
    (remainderBound (half⁺ ε) n χ≤n)
    (half< ε)




sequenceCauchyProductSumProductFromRemainderConvergence :
  (u v : ℕ → ℝᶜ) →
  (ν τ μ χ β : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneNatModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneNatModulus τ) →
  (productTail : TailBound (sequenceCauchyProduct u v) μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  BoundedByᶜ ι (seriesSumFromFiniteTailBound u ν uTail ν-antitone) →
  SeqAlg.EventuallyBoundedByWith β κ (partialSumSequence v) →
  SeqConv.ConvergesWithModulus
    (λ n → rectangularTriangularRemainder u v n n)
    0ᶜ
    χ →
  seriesSumFromFiniteTailBound
    (sequenceCauchyProduct u v)
    μ
    productTail
    μ-antitone
  ≡
  seriesSumFromFiniteTailBound u ν uTail ν-antitone ·ᶜ
  seriesSumFromFiniteTailBound v τ vTail τ-antitone
sequenceCauchyProductSumProductFromRemainderConvergence
  u
  v
  ν
  τ
  μ
  χ
  β
  κ
  ι
  uTail
  ν-antitone
  vTail
  τ-antitone
  productTail
  μ-antitone
  sumU-bound
  partialV-bound
  remainder→0 =
  SeqConv.convergesToPath
    product-series-converges
    product-algebra-converges-aligned
  where
  sumU : ℝᶜ
  sumU =
    seriesSumFromFiniteTailBound u ν uTail ν-antitone

  sumV : ℝᶜ
  sumV =
    seriesSumFromFiniteTailBound v τ vTail τ-antitone

  productLimit : ℝᶜ
  productLimit =
    sumU ·ᶜ sumV

  productSequence : ℕ → ℝᶜ
  productSequence n =
    partialSum u n ·ᶜ partialSum v n

  product-algebra-converges :
    SeqConv.ConvergesTo productSequence productLimit
  product-algebra-converges =
    SeqAlg.mulConvergesToWithBounds
      κ
      ι
      sumU-bound
      partialV-bound
      (seriesSumFromFiniteTailBoundConvergesTo
        u
        ν
        uTail
        ν-antitone)
      (seriesSumFromFiniteTailBoundConvergesTo
        v
        τ
        vTail
        τ-antitone)

  alignedModulus : ℚ⁺ → ℕ
  alignedModulus ε =
    maxModulus (product-algebra-converges .fst) χ (half⁺ ε)

  product-algebra-converges-aligned :
    SeqConv.ConvergesTo
      (partialSumSequence (sequenceCauchyProduct u v))
      productLimit
  product-algebra-converges-aligned =
    alignedModulus , aligned-converges
    where
    aligned-converges :
      SeqConv.ConvergesWithModulus
        (partialSumSequence (sequenceCauchyProduct u v))
        productLimit
        alignedModulus
    aligned-converges ε n aligned≤n =
      subst
        (λ ρ →
          partialSum (sequenceCauchyProduct u v) n
          ∼[ ρ ]
          productLimit)
        (half⁺+half⁺≡ ε)
        (MetricSpace.close-triangle
          CauchyRealsMetricSpace
          cp∼productPartial
          productPartial∼limit)
      where
      α : ℚ⁺
      α =
        half⁺ ε

      product≤n :
        (NatOrder._≤_) ((product-algebra-converges .fst) α) n
      product≤n =
        NatOrder.≤-trans
          (maxModulus-left≤
            (product-algebra-converges .fst)
            χ
            α)
          aligned≤n

      remainder≤n :
        (NatOrder._≤_) (χ α) n
      remainder≤n =
        NatOrder.≤-trans
          (maxModulus-right≤
            (product-algebra-converges .fst)
            χ
            α)
          aligned≤n

      productPartial∼limit :
        productSequence n ∼[ α ] productLimit
      productPartial∼limit =
        product-algebra-converges .snd α n product≤n

      remainder∼0 :
        rectangularTriangularRemainder u v n n ∼[ α ] 0ᶜ
      remainder∼0 =
        remainder→0 α n remainder≤n

      productDiff∼0 :
        (productSequence n +ᶜ
          (-ᶜ partialSum (sequenceCauchyProduct u v) n))
        ∼[ α ]
        0ᶜ
      productDiff∼0 =
        subst
          (λ z → z ∼[ α ] 0ᶜ)
          (sym (partialProduct-sequenceCauchyProductRemainder u v n))
          remainder∼0

      productPartial∼cp :
        productSequence n ∼[ α ]
        partialSum (sequenceCauchyProduct u v) n
      productPartial∼cp =
        diff-close-zero→close productDiff∼0

      cp∼productPartial :
        partialSum (sequenceCauchyProduct u v) n
        ∼[ α ]
        productSequence n
      cp∼productPartial =
        MetricSpace.close-sym CauchyRealsMetricSpace productPartial∼cp

  product-series-converges :
    SeqConv.ConvergesTo
      (partialSumSequence (sequenceCauchyProduct u v))
      (seriesSumFromFiniteTailBound
        (sequenceCauchyProduct u v)
        μ
        productTail
        μ-antitone)
  product-series-converges =
    seriesSumFromFiniteTailBoundConvergesTo
      (sequenceCauchyProduct u v)
      μ
      productTail
      μ-antitone


sequenceCauchyProductSumProductFromRemainderBound :
  (u v : ℕ → ℝᶜ) →
  (ν τ μ χ β : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneNatModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneNatModulus τ) →
  (productTail : TailBound (sequenceCauchyProduct u v) μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  BoundedByᶜ ι (seriesSumFromFiniteTailBound u ν uTail ν-antitone) →
  SeqAlg.EventuallyBoundedByWith β κ (partialSumSequence v) →
  ((ε : ℚ⁺) →
    (n : ℕ) →
    NatOrder._≤_ (χ ε) n →
    BoundedByᶜ ε (rectangularTriangularRemainder u v n n)) →
  seriesSumFromFiniteTailBound
    (sequenceCauchyProduct u v)
    μ
    productTail
    μ-antitone
  ≡
  seriesSumFromFiniteTailBound u ν uTail ν-antitone ·ᶜ
  seriesSumFromFiniteTailBound v τ vTail τ-antitone
sequenceCauchyProductSumProductFromRemainderBound
  u
  v
  ν
  τ
  μ
  χ
  β
  κ
  ι
  uTail
  ν-antitone
  vTail
  τ-antitone
  productTail
  μ-antitone
  sumU-bound
  partialV-bound
  remainderBound =
  sequenceCauchyProductSumProductFromRemainderConvergence
    u
    v
    ν
    τ
    μ
    (λ ε → χ (half⁺ ε))
    β
    κ
    ι
    uTail
    ν-antitone
    vTail
    τ-antitone
    productTail
    μ-antitone
    sumU-bound
    partialV-bound
    (rectangularTriangularRemainderConvergesFromBound
      u
      v
      χ
      remainderBound)
