{-

Part of Constructive.Analysis.Reals.PowerSeries.CauchyProduct

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.CauchyProduct.MajorantProduct where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.HITs.PropositionalTruncation as Prop

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (mulᶜ≤abs-product)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using
    ( BoundedByᶜ
    ; bounded-byᶜ
    ; bounded-byᶜ-add
    ; merely-boundedᶜ
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (absᶜ)
open import Constructive.Analysis.Reals.Series
  using
    ( SeriesMajorizedBy
    ; TailBound
    ; partialSum
    ; partialSumSequence
    ; seriesSumFromFiniteTailBound
    ; seriesSumFromFiniteTailBoundConvergesTo
    )
open import Constructive.Data.PositiveRationals

open ClosenessOf RationalsMetricSpace

import Constructive.Analysis.Reals.Sequences.Algebra as SeqAlg
open import Constructive.Analysis.Modulus
  using (AntitoneNatModulus)

open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Core
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Remainder
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Bounds
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.MajorantRemainder

seriesPartialSumsEventuallyBoundedBySum :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (uTail : TailBound u μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (seriesSumFromFiniteTailBound u μ uTail μ-antitone) →
  SeqAlg.EventuallyBoundedByWith
    (λ _ → μ (quarter⁺ (half⁺ (half⁺ 1⁺))))
    (1⁺ +⁺ κ)
    (partialSumSequence u)
seriesPartialSumsEventuallyBoundedBySum
    u μ uTail μ-antitone κ sum-bound _ n μ≤n =
  subst
    (BoundedByᶜ (1⁺ +⁺ κ))
    (minus-plus-cancel-right partial sum)
    (bounded-byᶜ-add
      1⁺
      κ
      diff
      sum
      diff-bound
      sum-bound)
  where
  partial : ℝᶜ
  partial =
    partialSum u n

  sum : ℝᶜ
  sum =
    seriesSumFromFiniteTailBound u μ uTail μ-antitone

  diff : ℝᶜ
  diff =
    partial +ᶜ (-ᶜ sum)

  partial∼sum :
    partial ∼[ half⁺ 1⁺ ] sum
  partial∼sum =
    seriesSumFromFiniteTailBoundConvergesTo
      u
      μ
      uTail
      μ-antitone
      .snd
      (half⁺ 1⁺)
      n
      μ≤n

  diff-bound :
    BoundedByᶜ 1⁺ diff
  diff-bound =
    close→difference-bounded-byᶜ
      partial
      sum
      (half< 1⁺)
      partial∼sum




sequenceCauchyProductSumProductFromMajorantRemainderBound :
  {u v U V : ℕ → ℝᶜ} →
  (ν τ μ χ β : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneNatModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneNatModulus τ) →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (productMajorTail : TailBound (sequenceCauchyProduct U V) μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  BoundedByᶜ ι (seriesSumFromFiniteTailBound u ν uTail ν-antitone) →
  SeqAlg.EventuallyBoundedByWith β κ (partialSumSequence v) →
  ((ε : ℚ⁺) →
    (n : ℕ) →
    NatOrder._≤_ (χ ε) n →
    BoundedByᶜ
      ε
      (rectangularTriangularRemainder U V n n)) →
  seriesSumFromFiniteTailBound
    (sequenceCauchyProduct u v)
    μ
    (sequenceCauchyProductTailBoundFromMajorant
      uMajorized
      vMajorized
      productMajorTail)
    μ-antitone
  ≡
  seriesSumFromFiniteTailBound u ν uTail ν-antitone ·ᶜ
  seriesSumFromFiniteTailBound v τ vTail τ-antitone
sequenceCauchyProductSumProductFromMajorantRemainderBound
  {u = u}
  {v = v}
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
  uMajorized
  vMajorized
  productMajorTail
  μ-antitone
  sumU-bound
  partialV-bound
  majorantRemainderBound =
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
    (sequenceCauchyProductTailBoundFromMajorant
      uMajorized
      vMajorized
      productMajorTail)
    μ-antitone
    sumU-bound
    partialV-bound
    (λ ε n χ≤n →
      rectangularTriangularRemainderBoundFromMajorant
        uMajorized
        vMajorized
        ε
        n
        (majorantRemainderBound ε n χ≤n))


sequenceCauchyProductSumProductFromMajorantProductTailWithPartialBound :
  {u v U V : ℕ → ℝᶜ} →
  (ν τ μ β : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneNatModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneNatModulus τ) →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (productMajorTail : TailBound (sequenceCauchyProduct U V) μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  BoundedByᶜ ι (seriesSumFromFiniteTailBound u ν uTail ν-antitone) →
  SeqAlg.EventuallyBoundedByWith β κ (partialSumSequence v) →
  seriesSumFromFiniteTailBound
    (sequenceCauchyProduct u v)
    μ
    (sequenceCauchyProductTailBoundFromMajorant
      uMajorized
      vMajorized
      productMajorTail)
    μ-antitone
  ≡
  seriesSumFromFiniteTailBound u ν uTail ν-antitone ·ᶜ
  seriesSumFromFiniteTailBound v τ vTail τ-antitone
sequenceCauchyProductSumProductFromMajorantProductTailWithPartialBound
  {U = U}
  {V = V}
  ν
  τ
  μ
  β
  κ
  ι
  uTail
  ν-antitone
  vTail
  τ-antitone
  uMajorized
  vMajorized
  productMajorTail
  μ-antitone
  sumU-bound
  partialV-bound =
  sequenceCauchyProductSumProductFromMajorantRemainderBound
    ν
    τ
    μ
    μ
    β
    κ
    ι
    uTail
    ν-antitone
    vTail
    τ-antitone
    uMajorized
    vMajorized
    productMajorTail
    μ-antitone
    sumU-bound
    partialV-bound
    (rectangularTriangularRemainderBoundFromProductTail
      U
      V
      U-nonnegative
      V-nonnegative
      (λ n →
        rectangularTriangularRemainder≤cauchyProductTail
          U
          V
          U-nonnegative
          V-nonnegative
          n
          n
          NatOrder.≤-refl)
      productMajorTail)
  where
  U-nonnegative :
    (n : ℕ) → 0ᶜ ≤ᶜ U n
  U-nonnegative n =
    SeriesMajorizedBy.majorantNonnegative uMajorized zero n

  V-nonnegative :
    (n : ℕ) → 0ᶜ ≤ᶜ V n
  V-nonnegative n =
    SeriesMajorizedBy.majorantNonnegative vMajorized zero n


sequenceCauchyProductSumProductFromMajorantProductTailAndSumBounds :
  {u v U V : ℕ → ℝᶜ} →
  (ν τ μ : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneNatModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneNatModulus τ) →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (productMajorTail : TailBound (sequenceCauchyProduct U V) μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  BoundedByᶜ ι (seriesSumFromFiniteTailBound u ν uTail ν-antitone) →
  BoundedByᶜ κ (seriesSumFromFiniteTailBound v τ vTail τ-antitone) →
  seriesSumFromFiniteTailBound
    (sequenceCauchyProduct u v)
    μ
    (sequenceCauchyProductTailBoundFromMajorant
      uMajorized
      vMajorized
      productMajorTail)
    μ-antitone
  ≡
  seriesSumFromFiniteTailBound u ν uTail ν-antitone ·ᶜ
  seriesSumFromFiniteTailBound v τ vTail τ-antitone
sequenceCauchyProductSumProductFromMajorantProductTailAndSumBounds
  ν
  τ
  μ
  κ
  ι
  uTail
  ν-antitone
  vTail
  τ-antitone
  uMajorized
  vMajorized
  productMajorTail
  μ-antitone
  sumU-bound
  sumV-bound =
  sequenceCauchyProductSumProductFromMajorantProductTailWithPartialBound
    ν
    τ
    μ
    (λ _ → τ (quarter⁺ (half⁺ (half⁺ 1⁺))))
    (1⁺ +⁺ κ)
    ι
    uTail
    ν-antitone
    vTail
    τ-antitone
    uMajorized
    vMajorized
    productMajorTail
    μ-antitone
    sumU-bound
    (seriesPartialSumsEventuallyBoundedBySum
      _
      τ
      vTail
      τ-antitone
      κ
      sumV-bound)


sequenceCauchyProductSumProductFromMajorantProductTail :
  {u v U V : ℕ → ℝᶜ} →
  (ν τ μ : ℚ⁺ → ℕ) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneNatModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneNatModulus τ) →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (productMajorTail : TailBound (sequenceCauchyProduct U V) μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  seriesSumFromFiniteTailBound
    (sequenceCauchyProduct u v)
    μ
    (sequenceCauchyProductTailBoundFromMajorant
      uMajorized
      vMajorized
      productMajorTail)
    μ-antitone
  ≡
  seriesSumFromFiniteTailBound u ν uTail ν-antitone ·ᶜ
  seriesSumFromFiniteTailBound v τ vTail τ-antitone
sequenceCauchyProductSumProductFromMajorantProductTail
  {u = u}
  {v = v}
  ν
  τ
  μ
  uTail
  ν-antitone
  vTail
  τ-antitone
  uMajorized
  vMajorized
  productMajorTail
  μ-antitone =
  Prop.rec
    (isSetCompletion productSum productOfSums)
    step-left
    (merely-boundedᶜ sumU)
  where
  productSum : ℝᶜ
  productSum =
    seriesSumFromFiniteTailBound
      (sequenceCauchyProduct u v)
      μ
      (sequenceCauchyProductTailBoundFromMajorant
        uMajorized
        vMajorized
        productMajorTail)
      μ-antitone

  sumU : ℝᶜ
  sumU =
    seriesSumFromFiniteTailBound u ν uTail ν-antitone

  sumV : ℝᶜ
  sumV =
    seriesSumFromFiniteTailBound v τ vTail τ-antitone

  productOfSums : ℝᶜ
  productOfSums =
    sumU ·ᶜ sumV

  step-left :
    Σ[ ι ∈ ℚ⁺ ] BoundedByᶜ ι sumU →
    productSum ≡ productOfSums
  step-left (ι , sumU-bound) =
    Prop.rec
      (isSetCompletion productSum productOfSums)
      step-right
      (merely-boundedᶜ sumV)
    where
    step-right :
      Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ sumV →
      productSum ≡ productOfSums
    step-right (κ , sumV-bound) =
      sequenceCauchyProductSumProductFromMajorantProductTailAndSumBounds
        ν
        τ
        μ
        κ
        ι
        uTail
        ν-antitone
        vTail
        τ-antitone
        uMajorized
        vMajorized
        productMajorTail
        μ-antitone
        sumU-bound
        sumV-bound
