{-

Cauchy-product coefficients for power series

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.CauchyProduct where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Metric.Instances.CauchyReals
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using
    ( mulᶜ≤abs-product
    ; mulᶜ-pres≤ᶜ-right
    ; neg-mulᶜ≤abs-product
    )
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-refl ; ≤ᶜ-trans)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using
    ( BoundedByᶜ
    ; bounded-byᶜ
    ; bounded-byᶜ-add
    ; bounded-byᶜ-close-zero
    ; merely-boundedᶜ
    ; upperᶜ
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using (close-rational-upper-bound)
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using
    ( absᶜ
    ; absᶜ-least
    ; absᶜ-nonnegative
    ; absᶜ-triangle
    ; absᶜ-zero
    ; nonnegativeᶜ-add
    ; ≤ᶜabsᶜ-left
    ; ≤ᶜabsᶜ-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
  using (diffᶜ-nonnegative→≤ᶜ ; ≤ᶜ-add)
open import Constructive.Analysis.Reals.Series
  using
    ( AntitoneTailModulus
    ; SeriesMajorizedBy
    ; TailBound
    ; comparisonTest
    ; diff-close-zero→close
    ; drop
    ; drop-index
    ; partialSum
    ; partialSum-add
    ; partialSum-diff-right-tail≤
    ; partialSum-suc
    ; partialSumSequence
    ; seriesSumFromFiniteTailBound
    ; seriesSumFromFiniteTailBoundConvergesTo
    ; seriesMajorizedByTerms
    ; nonnegative-upper→bounded-byᶜ
    ; tailSum
    ; tailSum-comparison
    ; tailSum-nonnegative
    ; tailSum-suc-start
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower ; realPower-suc ; realPower-zero)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using
    ( HasPowerSeriesOnBall
    ; HasPowerSeriesOnBallWith
    ; powerSeriesSumOnBall
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using
    ( PowerSeriesMajorizedOnBall
    ; majorizedOnBall→hasPowerSeriesOnBall
    ; majorizedOnBall→hasPowerSeriesOnBallWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( addPowerSeries
    ; constantPowerSeries
    ; negPowerSeries
    ; partialSum-mulLeft
    ; rationalScalePowerSeries
    ; shiftPowerSeries
    ; subPowerSeries
    ; zeroPowerSeries
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace

import Constructive.Analysis.Reals.Sequences.Algebra as SeqAlg
import Constructive.Analysis.Reals.Sequences.Convergence as SeqConv
import Constructive.Analysis.Reals.Sequences.Order as SeqOrder
open import Constructive.Analysis.Reals.Sequences.Base
  using (maxModulus ; maxModulus-left≤ ; maxModulus-right≤)


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    rectangular-triangular-remainder-step :
      (u Qq Qm R T : 𝓡 .fst) →
      ((u · Qq + R) + (- (u · Qm + T))) ≡
      (u · (Qq + (- Qm)) + (R + (- T)))
    rectangular-triangular-remainder-step _ _ _ _ _ =
      solve! 𝓡

    tail-cauchy-product-decomposition-step :
      (u v tv cp tcp : 𝓡 .fst) →
      ((u · v + cp) + (u · tv + tcp)) ≡
      (u · (v + tv) + (cp + tcp))
    tail-cauchy-product-decomposition-step _ _ _ _ _ =
      solve! 𝓡


cauchyProductPowerSeries :
  PowerSeries →
  PowerSeries →
  PowerSeries
cauchyProductPowerSeries a b zero =
  a zero ·ᶜ b zero
cauchyProductPowerSeries a b (suc n) =
  a zero ·ᶜ b (suc n) +ᶜ
  cauchyProductPowerSeries (shiftPowerSeries a) b n


sequenceCauchyProduct :
  (ℕ → ℝᶜ) →
  (ℕ → ℝᶜ) →
  ℕ →
  ℝᶜ
sequenceCauchyProduct u v zero =
  u zero ·ᶜ v zero
sequenceCauchyProduct u v (suc n) =
  u zero ·ᶜ v (suc n) +ᶜ
  sequenceCauchyProduct (λ k → u (suc k)) v n


sequenceCauchyProduct-zero :
  (u v : ℕ → ℝᶜ) →
  sequenceCauchyProduct u v zero ≡ u zero ·ᶜ v zero
sequenceCauchyProduct-zero u v =
  refl


sequenceCauchyProduct-suc :
  (u v : ℕ → ℝᶜ) →
  (n : ℕ) →
  sequenceCauchyProduct u v (suc n) ≡
  u zero ·ᶜ v (suc n) +ᶜ
  sequenceCauchyProduct (λ k → u (suc k)) v n
sequenceCauchyProduct-suc u v n =
  refl


sequenceCauchyProduct-cong :
  {u v U V : ℕ → ℝᶜ} →
  ((n : ℕ) → u n ≡ U n) →
  ((n : ℕ) → v n ≡ V n) →
  (n : ℕ) →
  sequenceCauchyProduct u v n ≡
  sequenceCauchyProduct U V n
sequenceCauchyProduct-cong u≡U v≡V zero =
  cong₂ _·ᶜ_ (u≡U zero) (v≡V zero)
sequenceCauchyProduct-cong {u = u} {v = v} {U = U} {V = V}
    u≡U v≡V (suc n) =
  cong₂
    _+ᶜ_
    (cong₂ _·ᶜ_ (u≡U zero) (v≡V (suc n)))
    (sequenceCauchyProduct-cong
      (λ k → u≡U (suc k))
      v≡V
      n)


sequenceCauchyProduct-cong-left :
  {u v U : ℕ → ℝᶜ} →
  ((n : ℕ) → u n ≡ U n) →
  (n : ℕ) →
  sequenceCauchyProduct u v n ≡
  sequenceCauchyProduct U v n
sequenceCauchyProduct-cong-left u≡U =
  sequenceCauchyProduct-cong u≡U (λ _ → refl)


sequenceCauchyProduct-scale-left :
  (c : ℝᶜ) →
  (u v : ℕ → ℝᶜ) →
  (n : ℕ) →
  sequenceCauchyProduct (λ k → c ·ᶜ u k) v n ≡
  c ·ᶜ sequenceCauchyProduct u v n
sequenceCauchyProduct-scale-left c u v zero =
  sym (mulᶜ-assoc c (u zero) (v zero))
sequenceCauchyProduct-scale-left c u v (suc n) =
  cong₂
    _+ᶜ_
    (sym (mulᶜ-assoc c (u zero) (v (suc n))))
    (sequenceCauchyProduct-scale-left
      c
      (λ k → u (suc k))
      v
      n) ∙
  sym
    (mulᶜ-distrib-right
      c
      (u zero ·ᶜ v (suc n))
      (sequenceCauchyProduct (λ k → u (suc k)) v n))


partialSum-sequenceCauchyProduct-tail :
  (u v : ℕ → ℝᶜ) →
  (n : ℕ) →
  partialSum (λ k → sequenceCauchyProduct u v (suc k)) n ≡
  partialSum (λ k → u zero ·ᶜ v (suc k)) n +ᶜ
  partialSum (sequenceCauchyProduct (λ k → u (suc k)) v) n
partialSum-sequenceCauchyProduct-tail u v n =
  cong
    (λ w → partialSum w n)
    tailTermsPath ∙
  partialSum-add
    (λ k → u zero ·ᶜ v (suc k))
    (sequenceCauchyProduct (λ k → u (suc k)) v)
    n
  where
  tailTermsPath :
    (λ k → sequenceCauchyProduct u v (suc k)) ≡
    (λ k →
      u zero ·ᶜ v (suc k) +ᶜ
      sequenceCauchyProduct (λ i → u (suc i)) v k)
  tailTermsPath =
    funExt (sequenceCauchyProduct-suc u v)


partialSum-sequenceCauchyProduct :
  (u v : ℕ → ℝᶜ) →
  (n : ℕ) →
  partialSum (sequenceCauchyProduct u v) (suc n) ≡
  u zero ·ᶜ partialSum v (suc n) +ᶜ
  partialSum (sequenceCauchyProduct (λ k → u (suc k)) v) n
partialSum-sequenceCauchyProduct u v n =
  partialSum-suc (sequenceCauchyProduct u v) n ∙
  cong
    (u zero ·ᶜ v zero +ᶜ_)
    (partialSum-sequenceCauchyProduct-tail u v n) ∙
  add-assoc
    (u zero ·ᶜ v zero)
    (partialSum (λ k → u zero ·ᶜ v (suc k)) n)
    tailPartial ∙
  cong
    (λ z → (u zero ·ᶜ v zero +ᶜ z) +ᶜ tailPartial)
    (partialSum-mulLeft u0 (λ k → v (suc k)) n) ∙
  cong
    (_+ᶜ tailPartial)
    (sym
      (mulᶜ-distrib-right
        u0
        (v zero)
        (partialSum (λ k → v (suc k)) n))) ∙
  cong
    (λ z → u0 ·ᶜ z +ᶜ tailPartial)
    (sym (partialSum-suc v n))
  where
  u0 : ℝᶜ
  u0 =
    u zero

  tailPartial : ℝᶜ
  tailPartial =
    partialSum (sequenceCauchyProduct (λ k → u (suc k)) v) n


rectangularRows :
  (ℕ → ℝᶜ) →
  (ℕ → ℝᶜ) →
  ℕ →
  ℕ →
  ℝᶜ
rectangularRows u v zero n =
  0ᶜ
rectangularRows u v (suc m) n =
  u zero ·ᶜ partialSum v n +ᶜ
  rectangularRows (λ k → u (suc k)) v m n


triangularRows :
  (ℕ → ℝᶜ) →
  (ℕ → ℝᶜ) →
  ℕ →
  ℝᶜ
triangularRows u v zero =
  0ᶜ
triangularRows u v (suc n) =
  u zero ·ᶜ partialSum v (suc n) +ᶜ
  triangularRows (λ k → u (suc k)) v n


rectangularTriangularRemainder :
  (ℕ → ℝᶜ) →
  (ℕ → ℝᶜ) →
  ℕ →
  ℕ →
  ℝᶜ
rectangularTriangularRemainder u v zero q =
  0ᶜ
rectangularTriangularRemainder u v (suc m) q =
  u zero ·ᶜ (partialSum v q +ᶜ (-ᶜ partialSum v (suc m))) +ᶜ
  rectangularTriangularRemainder (λ k → u (suc k)) v m q


rectangularRows-partialProduct :
  (u v : ℕ → ℝᶜ) →
  (m n : ℕ) →
  partialSum u m ·ᶜ partialSum v n ≡
  rectangularRows u v m n
rectangularRows-partialProduct u v zero n =
  mulᶜ-zero-left (partialSum v n)
rectangularRows-partialProduct u v (suc m) n =
  cong
    (_·ᶜ partialSum v n)
    (partialSum-suc u m) ∙
  mulᶜ-distrib-left
    (u zero)
    (partialSum (λ k → u (suc k)) m)
    (partialSum v n) ∙
  cong
    (u zero ·ᶜ partialSum v n +ᶜ_)
    (rectangularRows-partialProduct (λ k → u (suc k)) v m n)


triangularRows-partialCauchyProduct :
  (u v : ℕ → ℝᶜ) →
  (n : ℕ) →
  partialSum (sequenceCauchyProduct u v) n ≡
  triangularRows u v n
triangularRows-partialCauchyProduct u v zero =
  refl
triangularRows-partialCauchyProduct u v (suc n) =
  partialSum-sequenceCauchyProduct u v n ∙
  cong
    (u zero ·ᶜ partialSum v (suc n) +ᶜ_)
    (triangularRows-partialCauchyProduct
      (λ k → u (suc k))
      v
      n)


rectangularRows-triangularRows-remainder :
  (u v : ℕ → ℝᶜ) →
  (m q : ℕ) →
  rectangularRows u v m q +ᶜ (-ᶜ triangularRows u v m) ≡
  rectangularTriangularRemainder u v m q
rectangularRows-triangularRows-remainder u v zero q =
  add-inverse-right 0ᶜ
rectangularRows-triangularRows-remainder u v (suc m) q =
  SolverHelpers.rectangular-triangular-remainder-step
    CauchyRealsCommRing
    (u zero)
    (partialSum v q)
    (partialSum v (suc m))
    rectTail
    triangleTail ∙
  cong
    (u zero ·ᶜ
      (partialSum v q +ᶜ (-ᶜ partialSum v (suc m))) +ᶜ_)
    (rectangularRows-triangularRows-remainder
      (λ k → u (suc k))
      v
      m
      q)
  where
  rectTail : ℝᶜ
  rectTail =
    rectangularRows (λ k → u (suc k)) v m q

  triangleTail : ℝᶜ
  triangleTail =
    triangularRows (λ k → u (suc k)) v m


partialProduct-sequenceCauchyProductRemainder :
  (u v : ℕ → ℝᶜ) →
  (n : ℕ) →
  (partialSum u n ·ᶜ partialSum v n) +ᶜ
    (-ᶜ partialSum (sequenceCauchyProduct u v) n)
  ≡
  rectangularTriangularRemainder u v n n
partialProduct-sequenceCauchyProductRemainder u v n =
  cong₂
    (λ x y → x +ᶜ (-ᶜ y))
    (rectangularRows-partialProduct u v n n)
    (triangularRows-partialCauchyProduct u v n) ∙
  rectangularRows-triangularRows-remainder u v n n


seriesSumFromFiniteTailBound-cong :
  {u v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  (u≡v : u ≡ v) →
  (uTail : TailBound u μ) →
  (μ-antitone : AntitoneTailModulus μ) →
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


sequenceCauchyProductPartialSumsConvergeToProductFromRemainderConvergence :
  (u v : ℕ → ℝᶜ) →
  (ν τ χ β : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneTailModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneTailModulus τ) →
  BoundedByᶜ ι (seriesSumFromFiniteTailBound u ν uTail ν-antitone) →
  SeqAlg.EventuallyBoundedByWith β κ (partialSumSequence v) →
  SeqConv.ConvergesWithModulus
    (λ n → rectangularTriangularRemainder u v n n)
    0ᶜ
    χ →
  SeqConv.ConvergesTo
    (partialSumSequence (sequenceCauchyProduct u v))
    (seriesSumFromFiniteTailBound u ν uTail ν-antitone ·ᶜ
     seriesSumFromFiniteTailBound v τ vTail τ-antitone)
sequenceCauchyProductPartialSumsConvergeToProductFromRemainderConvergence
  u
  v
  ν
  τ
  χ
  β
  κ
  ι
  uTail
  ν-antitone
  vTail
  τ-antitone
  sumU-bound
  partialV-bound
  remainder→0 =
  alignedModulus , aligned-converges
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


sequenceCauchyProductSumProductFromRemainderConvergence :
  (u v : ℕ → ℝᶜ) →
  (ν τ μ χ β : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneTailModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneTailModulus τ) →
  (productTail : TailBound (sequenceCauchyProduct u v) μ) →
  (μ-antitone : AntitoneTailModulus μ) →
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
  (ν-antitone : AntitoneTailModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneTailModulus τ) →
  (productTail : TailBound (sequenceCauchyProduct u v) μ) →
  (μ-antitone : AntitoneTailModulus μ) →
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


mulᶜ-nonnegative :
  (x y : ℝᶜ) →
  0ᶜ ≤ᶜ x →
  0ᶜ ≤ᶜ y →
  0ᶜ ≤ᶜ x ·ᶜ y
mulᶜ-nonnegative x y 0≤x 0≤y =
  subst
    (λ z → z ≤ᶜ x ·ᶜ y)
    (mulᶜ-zero-left y)
    (mulᶜ-pres≤ᶜ-right 0ᶜ x y 0≤y 0≤x)


absᶜ-mul≤product :
  (x y X Y : ℝᶜ) →
  0ᶜ ≤ᶜ X →
  0ᶜ ≤ᶜ Y →
  absᶜ x ≤ᶜ X →
  absᶜ y ≤ᶜ Y →
  absᶜ (x ·ᶜ y) ≤ᶜ X ·ᶜ Y
absᶜ-mul≤product x y X Y 0≤X 0≤Y absx≤X absy≤Y =
  absᶜ-least
    (x ·ᶜ y)
    (X ·ᶜ Y)
    (mulᶜ-nonnegative X Y 0≤X 0≤Y)
    (≤ᶜ-trans
      {x = x ·ᶜ y}
      {y = absᶜ x ·ᶜ absᶜ y}
      {z = X ·ᶜ Y}
      (mulᶜ≤abs-product x y)
      absProduct≤majorantProduct)
    (≤ᶜ-trans
      {x = -ᶜ (x ·ᶜ y)}
      {y = absᶜ x ·ᶜ absᶜ y}
      {z = X ·ᶜ Y}
      (neg-mulᶜ≤abs-product x y)
      absProduct≤majorantProduct)
  where
  absProduct≤majorantProduct :
    absᶜ x ·ᶜ absᶜ y ≤ᶜ X ·ᶜ Y
  absProduct≤majorantProduct =
    ≤ᶜ-trans
      {x = absᶜ x ·ᶜ absᶜ y}
      {y = X ·ᶜ absᶜ y}
      {z = X ·ᶜ Y}
      (mulᶜ-pres≤ᶜ-right
        (absᶜ x)
        X
        (absᶜ y)
        (absᶜ-nonnegative y)
        absx≤X)
      (subst2
        _≤ᶜ_
        (mulᶜ-comm (absᶜ y) X)
        (mulᶜ-comm Y X)
        (mulᶜ-pres≤ᶜ-right
          (absᶜ y)
          Y
          X
          0≤X
          absy≤Y))


n≤sucn : (n : ℕ) → NatOrder._≤_ n (suc n)
n≤sucn n =
  suc zero , refl


add-nonnegative-right≤ :
  {x y : ℝᶜ} →
  0ᶜ ≤ᶜ y →
  x ≤ᶜ x +ᶜ y
add-nonnegative-right≤ {x = x} {y = y} 0≤y =
  subst
    (λ z → z ≤ᶜ x +ᶜ y)
    (add-zero-right x)
    (≤ᶜ-add
      {a = x}
      {b = x}
      {c = 0ᶜ}
      {d = y}
      (≤ᶜ-refl x)
      0≤y)


close-zero→bounded-byᶜ :
  {δ ε : ℚ⁺} →
  (x : ℝᶜ) →
  δ <⁺ ε →
  x ∼[ δ ] 0ᶜ →
  BoundedByᶜ ε x
close-zero→bounded-byᶜ {δ = δ} {ε = ε} x δ<ε x∼0 =
  bounded-byᶜ upperBound lowerBound
  where
  normalizeUpper :
    rational (Rational.0ℚ ℚ.+ radius ε) ≡ rational (radius ε)
  normalizeUpper =
    cong rational (ℚ.+IdL (radius ε))

  upperBound :
    x ≤ᶜ rational (radius ε)
  upperBound =
    subst
      (x ≤ᶜ_)
      normalizeUpper
      (close-rational-upper-bound
        x
        Rational.0ℚ
        δ
        ε
        δ<ε
        x∼0)

  -x∼0 :
    (-ᶜ x) ∼[ δ ] 0ᶜ
  -x∼0 =
    subst
      (λ y → (-ᶜ x) ∼[ δ ] y)
      (cong rational Rational.neg-zero)
      (neg-close x∼0)

  lowerBound :
    (-ᶜ x) ≤ᶜ rational (radius ε)
  lowerBound =
    subst
      ((-ᶜ x) ≤ᶜ_)
      normalizeUpper
      (close-rational-upper-bound
        (-ᶜ x)
        (ℚ.- Rational.0ℚ)
        δ
        ε
        δ<ε
        -x∼0)


close→difference-bounded-byᶜ :
  {δ ε : ℚ⁺} →
  (x y : ℝᶜ) →
  δ <⁺ ε →
  x ∼[ δ ] y →
  BoundedByᶜ ε (x +ᶜ (-ᶜ y))
close→difference-bounded-byᶜ {δ = δ} x y δ<ε x∼y =
  close-zero→bounded-byᶜ (x +ᶜ (-ᶜ y)) δ<ε diff∼0
  where
  diff∼0 :
    (x +ᶜ (-ᶜ y)) ∼[ δ ] 0ᶜ
  diff∼0 =
    subst
      (λ z → (x +ᶜ (-ᶜ y)) ∼[ δ ] z)
      (add-inverse-right y)
      (add-close-left x∼y (-ᶜ y))


tailBoundFromConvergesWithModulus :
  (u : ℕ → ℝᶜ) →
  (x : ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  SeqConv.ConvergesWithModulus (partialSumSequence u) x μ →
  TailBound u (λ ε → μ (quarter⁺ ε))
tailBoundFromConvergesWithModulus u x μ converges ε m k μ≤m =
  subst
    (BoundedByᶜ ε)
    diffPath
    diff-bound
  where
  α : ℚ⁺
  α =
    quarter⁺ ε

  n : ℕ
  n =
    m Nat.+ k

  m≤n : NatOrder._≤_ m n
  m≤n =
    k , Nat.+-comm k m

  μ≤n : NatOrder._≤_ (μ α) n
  μ≤n =
    NatOrder.≤-trans μ≤m m≤n

  partialN∼x :
    partialSum u n ∼[ α ] x
  partialN∼x =
    converges α n μ≤n

  partialM∼x :
    partialSum u m ∼[ α ] x
  partialM∼x =
    converges α m μ≤m

  partialN∼partialM :
    partialSum u n ∼[ half⁺ ε ] partialSum u m
  partialN∼partialM =
    subst
      (λ ρ → partialSum u n ∼[ ρ ] partialSum u m)
      (ℚ⁺Path (quarter-sum≡half ε))
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        partialN∼x
        (MetricSpace.close-sym CauchyRealsMetricSpace partialM∼x))

  diff : ℝᶜ
  diff =
    partialSum u n +ᶜ (-ᶜ partialSum u m)

  tailDiff =
    partialSum-diff-right-tail≤ u m n m≤n

  diffPath :
    diff ≡ tailSum u m k
  diffPath =
    tailDiff .snd

  diff-bound :
    BoundedByᶜ ε diff
  diff-bound =
    close→difference-bounded-byᶜ
      (partialSum u n)
      (partialSum u m)
      (half< ε)
      partialN∼partialM


sequenceCauchyProductTailBoundFromRemainderConvergence :
  (u v : ℕ → ℝᶜ) →
  (ν τ χ β : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneTailModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneTailModulus τ) →
  (sumU-bound :
    BoundedByᶜ ι (seriesSumFromFiniteTailBound u ν uTail ν-antitone)) →
  (partialV-bound :
    SeqAlg.EventuallyBoundedByWith β κ (partialSumSequence v)) →
  (remainder→0 :
    SeqConv.ConvergesWithModulus
      (λ n → rectangularTriangularRemainder u v n n)
      0ᶜ
      χ) →
  TailBound
    (sequenceCauchyProduct u v)
    (λ ε →
      sequenceCauchyProductPartialSumsConvergeToProductFromRemainderConvergence
        u
        v
        ν
        τ
        χ
        β
        κ
        ι
        uTail
        ν-antitone
        vTail
        τ-antitone
        sumU-bound
        partialV-bound
        remainder→0
        .fst
        (quarter⁺ ε))
sequenceCauchyProductTailBoundFromRemainderConvergence
  u
  v
  ν
  τ
  χ
  β
  κ
  ι
  uTail
  ν-antitone
  vTail
  τ-antitone
  sumU-bound
  partialV-bound
  remainder→0 =
  tailBoundFromConvergesWithModulus
    (sequenceCauchyProduct u v)
    productLimit
    (productConverges .fst)
    (productConverges .snd)
  where
  productLimit : ℝᶜ
  productLimit =
    seriesSumFromFiniteTailBound u ν uTail ν-antitone ·ᶜ
    seriesSumFromFiniteTailBound v τ vTail τ-antitone

  productConverges :
    SeqConv.ConvergesTo
      (partialSumSequence (sequenceCauchyProduct u v))
      productLimit
  productConverges =
    sequenceCauchyProductPartialSumsConvergeToProductFromRemainderConvergence
      u
      v
      ν
      τ
      χ
      β
      κ
      ι
      uTail
      ν-antitone
      vTail
      τ-antitone
      sumU-bound
      partialV-bound
      remainder→0


sequenceCauchyProductTailBoundFromRemainderBound :
  (u v : ℕ → ℝᶜ) →
  (ν τ χ β : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneTailModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneTailModulus τ) →
  (sumU-bound :
    BoundedByᶜ ι (seriesSumFromFiniteTailBound u ν uTail ν-antitone)) →
  (partialV-bound :
    SeqAlg.EventuallyBoundedByWith β κ (partialSumSequence v)) →
  (remainderBound :
    (ε : ℚ⁺) →
    (n : ℕ) →
    NatOrder._≤_ (χ ε) n →
    BoundedByᶜ ε (rectangularTriangularRemainder u v n n)) →
  TailBound
    (sequenceCauchyProduct u v)
    (λ ε →
      sequenceCauchyProductPartialSumsConvergeToProductFromRemainderConvergence
        u
        v
        ν
        τ
        (λ ε → χ (half⁺ ε))
        β
        κ
        ι
        uTail
        ν-antitone
        vTail
        τ-antitone
        sumU-bound
        partialV-bound
        (rectangularTriangularRemainderConvergesFromBound u v χ remainderBound)
        .fst
        (quarter⁺ ε))
sequenceCauchyProductTailBoundFromRemainderBound
  u
  v
  ν
  τ
  χ
  β
  κ
  ι
  uTail
  ν-antitone
  vTail
  τ-antitone
  sumU-bound
  partialV-bound
  remainderBound =
  sequenceCauchyProductTailBoundFromRemainderConvergence
    u
    v
    ν
    τ
    (λ ε → χ (half⁺ ε))
    β
    κ
    ι
    uTail
    ν-antitone
    vTail
    τ-antitone
    sumU-bound
    partialV-bound
    (rectangularTriangularRemainderConvergesFromBound u v χ remainderBound)


tailSum-length-monotone :
  (u : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ u n) →
  (m k q : ℕ) →
  NatOrder._≤_ k q →
  tailSum u m k ≤ᶜ tailSum u m q
tailSum-length-monotone u 0≤u m k q k≤q =
  diffᶜ-nonnegative→≤ᶜ
    (subst
      (λ x → 0ᶜ ≤ᶜ x)
      (sym diffPath)
      tailNonnegative)
  where
  diff =
    partialSum-diff-right-tail≤ (drop m u) k q k≤q

  d : ℕ
  d =
    diff .fst

  diffPath :
    tailSum u m q +ᶜ (-ᶜ tailSum u m k) ≡
    tailSum (drop m u) k d
  diffPath =
    diff .snd

  dropNonnegative :
    (n : ℕ) → 0ᶜ ≤ᶜ drop m u n
  dropNonnegative n =
    subst
      (λ x → 0ᶜ ≤ᶜ x)
      (sym (drop-index m u n))
      (0≤u (m Nat.+ n))

  tailNonnegative :
    0ᶜ ≤ᶜ tailSum (drop m u) k d
  tailNonnegative =
    tailSum-nonnegative (drop m u) dropNonnegative k d


partialSum-difference≤tailSum :
  (u : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ u n) →
  (m q : ℕ) →
  NatOrder._≤_ m q →
  partialSum u q +ᶜ (-ᶜ partialSum u m) ≤ᶜ
  tailSum u m q
partialSum-difference≤tailSum u 0≤u m q (k , k+m≡q) =
  subst
    (λ x → x ≤ᶜ tailSum u m q)
    (sym diffPath)
    (tailSum-length-monotone u 0≤u m k q k≤q)
  where
  diff =
    partialSum-diff-right-tail≤ u m q (k , k+m≡q)

  diffPath :
    partialSum u q +ᶜ (-ᶜ partialSum u m) ≡ tailSum u m k
  diffPath =
    diff .snd

  k≤q : NatOrder._≤_ k q
  k≤q =
    m , Nat.+-comm m k ∙ k+m≡q


partialSum-differenceMajorizedBy :
  (v V : ℕ → ℝᶜ) →
  SeriesMajorizedBy v V →
  (m q : ℕ) →
  NatOrder._≤_ m q →
  absᶜ (partialSum v q +ᶜ (-ᶜ partialSum v m)) ≤ᶜ
  partialSum V q +ᶜ (-ᶜ partialSum V m)
partialSum-differenceMajorizedBy v V majorized m q m≤q =
  subst2
    (λ x y → absᶜ x ≤ᶜ y)
    (sym vTailPath)
    (sym VTailPath)
    (tailSum-comparison majorized m k)
  where
  vDiff =
    partialSum-diff-right-tail≤ v m q m≤q

  VDiff =
    partialSum-diff-right-tail≤ V m q m≤q

  k : ℕ
  k =
    vDiff .fst

  vTailPath :
    partialSum v q +ᶜ (-ᶜ partialSum v m) ≡ _
  vTailPath =
    vDiff .snd

  VTailPath :
    partialSum V q +ᶜ (-ᶜ partialSum V m) ≡ _
  VTailPath =
    VDiff .snd


partialSum-differenceMajorant-nonnegative :
  (V : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ V n) →
  (m q : ℕ) →
  NatOrder._≤_ m q →
  0ᶜ ≤ᶜ partialSum V q +ᶜ (-ᶜ partialSum V m)
partialSum-differenceMajorant-nonnegative V 0≤V m q m≤q =
  subst
    (λ x → 0ᶜ ≤ᶜ x)
    (sym VTailPath)
    (tailSum-nonnegative V 0≤V m k)
  where
  VDiff =
    partialSum-diff-right-tail≤ V m q m≤q

  k : ℕ
  k =
    VDiff .fst

  VTailPath :
    partialSum V q +ᶜ (-ᶜ partialSum V m) ≡ _
  VTailPath =
    VDiff .snd


rectangularTriangularRemainder-nonnegative :
  (U V : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ U n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ V n) →
  (m q : ℕ) →
  NatOrder._≤_ m q →
  0ᶜ ≤ᶜ rectangularTriangularRemainder U V m q
rectangularTriangularRemainder-nonnegative U V 0≤U 0≤V zero q m≤q =
  ≤ᶜ-refl 0ᶜ
rectangularTriangularRemainder-nonnegative U V 0≤U 0≤V (suc m) q sucm≤q =
  nonnegativeᶜ-add
    {x = U zero ·ᶜ difference}
    {y = rectangularTriangularRemainder (λ k → U (suc k)) V m q}
    (mulᶜ-nonnegative
      (U zero)
      difference
      (0≤U zero)
      difference-nonnegative)
    (rectangularTriangularRemainder-nonnegative
      (λ k → U (suc k))
      V
      (λ k → 0≤U (suc k))
      0≤V
      m
      q
      m≤q)
  where
  difference : ℝᶜ
  difference =
    partialSum V q +ᶜ (-ᶜ partialSum V (suc m))

  m≤q : NatOrder._≤_ m q
  m≤q =
    NatOrder.≤-trans (n≤sucn m) sucm≤q

  difference-nonnegative :
    0ᶜ ≤ᶜ difference
  difference-nonnegative =
    partialSum-differenceMajorant-nonnegative V 0≤V (suc m) q sucm≤q


rectangularTriangularRemainder-termMajorized :
  (u v U V : ℕ → ℝᶜ) →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (m q : ℕ) →
  NatOrder._≤_ m q →
  absᶜ (rectangularTriangularRemainder u v m q) ≤ᶜ
  rectangularTriangularRemainder U V m q
rectangularTriangularRemainder-termMajorized u v U V uMajorized vMajorized
    zero q m≤q =
  subst
    (λ x → x ≤ᶜ 0ᶜ)
    (sym absᶜ-zero)
    (≤ᶜ-refl 0ᶜ)
rectangularTriangularRemainder-termMajorized u v U V uMajorized vMajorized
    (suc m) q sucm≤q =
  ≤ᶜ-trans
    {x = absᶜ (u zero ·ᶜ vDifference +ᶜ tailRemainder)}
    {y = absᶜ (u zero ·ᶜ vDifference) +ᶜ absᶜ tailRemainder}
    {z = U zero ·ᶜ VDifference +ᶜ majorantTailRemainder}
    (absᶜ-triangle (u zero ·ᶜ vDifference) tailRemainder)
    (≤ᶜ-add
      {a = absᶜ (u zero ·ᶜ vDifference)}
      {b = U zero ·ᶜ VDifference}
      {c = absᶜ tailRemainder}
      {d = majorantTailRemainder}
      head≤
      tail≤)
  where
  vDifference : ℝᶜ
  vDifference =
    partialSum v q +ᶜ (-ᶜ partialSum v (suc m))

  VDifference : ℝᶜ
  VDifference =
    partialSum V q +ᶜ (-ᶜ partialSum V (suc m))

  tailRemainder : ℝᶜ
  tailRemainder =
    rectangularTriangularRemainder (λ k → u (suc k)) v m q

  majorantTailRemainder : ℝᶜ
  majorantTailRemainder =
    rectangularTriangularRemainder (λ k → U (suc k)) V m q

  V-nonnegative :
    (n : ℕ) → 0ᶜ ≤ᶜ V n
  V-nonnegative n =
    SeriesMajorizedBy.majorantNonnegative vMajorized zero n

  U0-nonnegative :
    0ᶜ ≤ᶜ U zero
  U0-nonnegative =
    SeriesMajorizedBy.majorantNonnegative uMajorized zero zero

  VDifference-nonnegative :
    0ᶜ ≤ᶜ VDifference
  VDifference-nonnegative =
    partialSum-differenceMajorant-nonnegative
      V
      V-nonnegative
      (suc m)
      q
      sucm≤q

  u0≤U0 :
    absᶜ (u zero) ≤ᶜ U zero
  u0≤U0 =
    SeriesMajorizedBy.termMajorized uMajorized zero zero

  vDifference≤VDifference :
    absᶜ vDifference ≤ᶜ VDifference
  vDifference≤VDifference =
    partialSum-differenceMajorizedBy
      v
      V
      vMajorized
      (suc m)
      q
      sucm≤q

  head≤ :
    absᶜ (u zero ·ᶜ vDifference) ≤ᶜ U zero ·ᶜ VDifference
  head≤ =
    absᶜ-mul≤product
      (u zero)
      vDifference
      (U zero)
      VDifference
      U0-nonnegative
      VDifference-nonnegative
      u0≤U0
      vDifference≤VDifference

  shiftedUMajorized :
    SeriesMajorizedBy (λ k → u (suc k)) (λ k → U (suc k))
  shiftedUMajorized =
    seriesMajorizedByTerms
      (λ n → SeriesMajorizedBy.termMajorized uMajorized zero (suc n))
      (λ n → SeriesMajorizedBy.majorantNonnegative uMajorized zero (suc n))

  m≤q : NatOrder._≤_ m q
  m≤q =
    NatOrder.≤-trans (n≤sucn m) sucm≤q

  tail≤ :
    absᶜ tailRemainder ≤ᶜ majorantTailRemainder
  tail≤ =
    rectangularTriangularRemainder-termMajorized
      (λ k → u (suc k))
      v
      (λ k → U (suc k))
      V
      shiftedUMajorized
      vMajorized
      m
      q
      m≤q


rectangularTriangularRemainderBoundFromMajorant :
  {u v U V : ℕ → ℝᶜ} →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (ε : ℚ⁺) →
  (n : ℕ) →
  BoundedByᶜ
    ε
    (rectangularTriangularRemainder U V n n) →
  BoundedByᶜ
    ε
    (rectangularTriangularRemainder u v n n)
rectangularTriangularRemainderBoundFromMajorant {u = u} {v = v} {U = U} {V = V}
    uMajorized vMajorized ε n majorantBound =
  bounded-byᶜ
    (≤ᶜ-trans
      {x = actualRemainder}
      {y = absᶜ actualRemainder}
      {z = rational (radius ε)}
      (≤ᶜabsᶜ-left actualRemainder)
      absActual≤ε)
    (≤ᶜ-trans
      {x = -ᶜ actualRemainder}
      {y = absᶜ actualRemainder}
      {z = rational (radius ε)}
      (≤ᶜabsᶜ-right actualRemainder)
      absActual≤ε)
  where
  actualRemainder : ℝᶜ
  actualRemainder =
    rectangularTriangularRemainder u v n n

  majorantRemainder : ℝᶜ
  majorantRemainder =
    rectangularTriangularRemainder U V n n

  absActual≤majorant :
    absᶜ actualRemainder ≤ᶜ majorantRemainder
  absActual≤majorant =
    rectangularTriangularRemainder-termMajorized
      u
      v
      U
      V
      uMajorized
      vMajorized
      n
      n
      NatOrder.≤-refl

  absActual≤ε :
    absᶜ actualRemainder ≤ᶜ rational (radius ε)
  absActual≤ε =
    ≤ᶜ-trans
      {x = absᶜ actualRemainder}
      {y = majorantRemainder}
      {z = rational (radius ε)}
      absActual≤majorant
      (upperᶜ majorantBound)


rectangularTriangularRemainderConvergesFromMajorantBound :
  {u v U V : ℕ → ℝᶜ} →
  SeriesMajorizedBy u U →
  SeriesMajorizedBy v V →
  (χ : ℚ⁺ → ℕ) →
  ((ε : ℚ⁺) →
    (n : ℕ) →
    NatOrder._≤_ (χ ε) n →
    BoundedByᶜ
      ε
      (rectangularTriangularRemainder U V n n)) →
  SeqConv.ConvergesWithModulus
    (λ n → rectangularTriangularRemainder u v n n)
    0ᶜ
    (λ ε → χ (half⁺ ε))
rectangularTriangularRemainderConvergesFromMajorantBound
    {u = u} {v = v} uMajorized vMajorized χ majorantBound =
  rectangularTriangularRemainderConvergesFromBound
    u
    v
    χ
    (λ ε n χ≤n →
      rectangularTriangularRemainderBoundFromMajorant
        uMajorized
        vMajorized
        ε
        n
        (majorantBound ε n χ≤n))


sequenceCauchyProductTailBoundFromMajorantRemainderBound :
  {u v U V : ℕ → ℝᶜ} →
  (ν τ χ β : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneTailModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneTailModulus τ) →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (sumU-bound :
    BoundedByᶜ ι (seriesSumFromFiniteTailBound u ν uTail ν-antitone)) →
  (partialV-bound :
    SeqAlg.EventuallyBoundedByWith β κ (partialSumSequence v)) →
  (majorantRemainderBound :
    (ε : ℚ⁺) →
    (n : ℕ) →
    NatOrder._≤_ (χ ε) n →
    BoundedByᶜ ε (rectangularTriangularRemainder U V n n)) →
  TailBound
    (sequenceCauchyProduct u v)
    (λ ε →
      sequenceCauchyProductPartialSumsConvergeToProductFromRemainderConvergence
        u
        v
        ν
        τ
        (λ ε → χ (half⁺ ε))
        β
        κ
        ι
        uTail
        ν-antitone
        vTail
        τ-antitone
        sumU-bound
        partialV-bound
        (rectangularTriangularRemainderConvergesFromMajorantBound
          uMajorized
          vMajorized
          χ
          majorantRemainderBound)
        .fst
        (quarter⁺ ε))
sequenceCauchyProductTailBoundFromMajorantRemainderBound
  {u = u}
  {v = v}
  ν
  τ
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
  sumU-bound
  partialV-bound
  majorantRemainderBound =
  sequenceCauchyProductTailBoundFromRemainderBound
    u
    v
    ν
    τ
    χ
    β
    κ
    ι
    uTail
    ν-antitone
    vTail
    τ-antitone
    sumU-bound
    partialV-bound
    (λ ε n χ≤n →
      rectangularTriangularRemainderBoundFromMajorant
        uMajorized
        vMajorized
        ε
        n
        (majorantRemainderBound ε n χ≤n))


rectangularTriangularRemainderBoundFromProductTail :
  (U V : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ U n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ V n) →
  ((n : ℕ) →
    rectangularTriangularRemainder U V n n ≤ᶜ
    tailSum (sequenceCauchyProduct U V) n n) →
  {μ : ℚ⁺ → ℕ} →
  TailBound (sequenceCauchyProduct U V) μ →
  (ε : ℚ⁺) →
  (n : ℕ) →
  NatOrder._≤_ (μ ε) n →
  BoundedByᶜ ε (rectangularTriangularRemainder U V n n)
rectangularTriangularRemainderBoundFromProductTail
    U V 0≤U 0≤V remainder≤tail productTail ε n μ≤n =
  nonnegative-upper→bounded-byᶜ
    (rectangularTriangularRemainder-nonnegative
      U
      V
      0≤U
      0≤V
      n
      n
      NatOrder.≤-refl)
    (≤ᶜ-trans
      {x = rectangularTriangularRemainder U V n n}
      {y = tailSum (sequenceCauchyProduct U V) n n}
      {z = rational (radius ε)}
      (remainder≤tail n)
      (upperᶜ (productTail ε n n μ≤n)))


tailSum-sequenceCauchyProduct-suc :
  (u v : ℕ → ℝᶜ) →
  (m q : ℕ) →
  tailSum (sequenceCauchyProduct u v) (suc m) q ≡
  u zero ·ᶜ tailSum v (suc m) q +ᶜ
  tailSum (sequenceCauchyProduct (λ k → u (suc k)) v) m q
tailSum-sequenceCauchyProduct-suc u v m zero =
  sym
    (cong
      (_+ᶜ 0ᶜ)
      (mulᶜ-zero-right (u zero)) ∙
    add-zero-left 0ᶜ)
tailSum-sequenceCauchyProduct-suc u v m (suc q) =
  tailSum-suc-start (sequenceCauchyProduct u v) (suc m) q ∙
  cong₂
    _+ᶜ_
    (sequenceCauchyProduct-suc u v m)
    (tailSum-sequenceCauchyProduct-suc u v (suc m) q) ∙
  SolverHelpers.tail-cauchy-product-decomposition-step
    CauchyRealsCommRing
    (u zero)
    (v (suc m))
    (tailSum v (suc (suc m)) q)
    (sequenceCauchyProduct (λ k → u (suc k)) v m)
    (tailSum
      (sequenceCauchyProduct (λ k → u (suc k)) v)
      (suc m)
      q) ∙
  cong₂
    _+ᶜ_
    (cong
      (u zero ·ᶜ_)
      (sym (tailSum-suc-start v (suc m) q)))
    (sym
      (tailSum-suc-start
        (sequenceCauchyProduct (λ k → u (suc k)) v)
        m
        q))


sequenceCauchyProduct-nonnegative :
  (u v : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ u n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ v n) →
  (n : ℕ) →
  0ᶜ ≤ᶜ sequenceCauchyProduct u v n
sequenceCauchyProduct-nonnegative u v 0≤u 0≤v zero =
  mulᶜ-nonnegative (u zero) (v zero) (0≤u zero) (0≤v zero)
sequenceCauchyProduct-nonnegative u v 0≤u 0≤v (suc n) =
  nonnegativeᶜ-add
    {x = u zero ·ᶜ v (suc n)}
    {y = sequenceCauchyProduct (λ k → u (suc k)) v n}
    (mulᶜ-nonnegative
      (u zero)
      (v (suc n))
      (0≤u zero)
      (0≤v (suc n)))
    (sequenceCauchyProduct-nonnegative
      (λ k → u (suc k))
      v
      (λ k → 0≤u (suc k))
      0≤v
      n)


tailSum-sequenceCauchyProduct-shift≤ :
  (u v : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ u n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ v n) →
  (m q : ℕ) →
  tailSum (sequenceCauchyProduct (λ k → u (suc k)) v) m q ≤ᶜ
  tailSum (sequenceCauchyProduct u v) (suc m) q
tailSum-sequenceCauchyProduct-shift≤ u v 0≤u 0≤v m q =
  subst
    (λ z → shiftTail ≤ᶜ z)
    (sym (tailSum-sequenceCauchyProduct-suc u v m q))
    shiftTail≤decomposed
  where
  headTail : ℝᶜ
  headTail =
    u zero ·ᶜ tailSum v (suc m) q

  shiftTail : ℝᶜ
  shiftTail =
    tailSum (sequenceCauchyProduct (λ k → u (suc k)) v) m q

  headTail-nonnegative :
    0ᶜ ≤ᶜ headTail
  headTail-nonnegative =
    mulᶜ-nonnegative
      (u zero)
      (tailSum v (suc m) q)
      (0≤u zero)
      (tailSum-nonnegative v 0≤v (suc m) q)

  shiftTail≤shiftPlusHead :
    shiftTail ≤ᶜ shiftTail +ᶜ headTail
  shiftTail≤shiftPlusHead =
    add-nonnegative-right≤ headTail-nonnegative

  shiftTail≤decomposed :
    shiftTail ≤ᶜ headTail +ᶜ shiftTail
  shiftTail≤decomposed =
    subst
      (λ z → shiftTail ≤ᶜ z)
      (add-comm shiftTail headTail)
      shiftTail≤shiftPlusHead


rectangularTriangularRemainder≤cauchyProductTail :
  (U V : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ U n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ V n) →
  (m q : ℕ) →
  NatOrder._≤_ m q →
  rectangularTriangularRemainder U V m q ≤ᶜ
  tailSum (sequenceCauchyProduct U V) m q
rectangularTriangularRemainder≤cauchyProductTail U V 0≤U 0≤V zero q _ =
  tailSum-nonnegative
    (sequenceCauchyProduct U V)
    (sequenceCauchyProduct-nonnegative U V 0≤U 0≤V)
    zero
    q
rectangularTriangularRemainder≤cauchyProductTail U V 0≤U 0≤V
    (suc m) q sucm≤q =
  subst
    (λ z →
      rectangularTriangularRemainder U V (suc m) q ≤ᶜ z)
    (sym (tailSum-sequenceCauchyProduct-suc U V m q))
    remainder≤decomposedTail
  where
  difference : ℝᶜ
  difference =
    partialSum V q +ᶜ (-ᶜ partialSum V (suc m))

  fullTail : ℝᶜ
  fullTail =
    tailSum V (suc m) q

  headRemainder : ℝᶜ
  headRemainder =
    U zero ·ᶜ difference

  headTail : ℝᶜ
  headTail =
    U zero ·ᶜ fullTail

  tailRemainder : ℝᶜ
  tailRemainder =
    rectangularTriangularRemainder (λ k → U (suc k)) V m q

  shiftTail : ℝᶜ
  shiftTail =
    tailSum (sequenceCauchyProduct (λ k → U (suc k)) V) m q

  m≤q : NatOrder._≤_ m q
  m≤q =
    NatOrder.≤-trans (n≤sucn m) sucm≤q

  difference≤fullTail :
    difference ≤ᶜ fullTail
  difference≤fullTail =
    partialSum-difference≤tailSum V 0≤V (suc m) q sucm≤q

  head≤ :
    headRemainder ≤ᶜ headTail
  head≤ =
    subst2
      _≤ᶜ_
      (mulᶜ-comm difference (U zero))
      (mulᶜ-comm fullTail (U zero))
      (mulᶜ-pres≤ᶜ-right
        difference
        fullTail
        (U zero)
        (0≤U zero)
        difference≤fullTail)

  tail≤ :
    tailRemainder ≤ᶜ shiftTail
  tail≤ =
    rectangularTriangularRemainder≤cauchyProductTail
      (λ k → U (suc k))
      V
      (λ k → 0≤U (suc k))
      0≤V
      m
      q
      m≤q

  remainder≤decomposedTail :
    rectangularTriangularRemainder U V (suc m) q ≤ᶜ
    headTail +ᶜ shiftTail
  remainder≤decomposedTail =
    ≤ᶜ-add
      {a = headRemainder}
      {b = headTail}
      {c = tailRemainder}
      {d = shiftTail}
      head≤
      tail≤


sequenceCauchyProduct-termMajorized :
  (u v U V : ℕ → ℝᶜ) →
  ((n : ℕ) → absᶜ (u n) ≤ᶜ U n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ U n) →
  ((n : ℕ) → absᶜ (v n) ≤ᶜ V n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ V n) →
  (n : ℕ) →
  absᶜ (sequenceCauchyProduct u v n) ≤ᶜ
  sequenceCauchyProduct U V n
sequenceCauchyProduct-termMajorized u v U V u≤U 0≤U v≤V 0≤V zero =
  absᶜ-mul≤product
    (u zero)
    (v zero)
    (U zero)
    (V zero)
    (0≤U zero)
    (0≤V zero)
    (u≤U zero)
    (v≤V zero)
sequenceCauchyProduct-termMajorized u v U V u≤U 0≤U v≤V 0≤V (suc n) =
  ≤ᶜ-trans
    {x = absᶜ
      (u zero ·ᶜ v (suc n) +ᶜ
       sequenceCauchyProduct (λ k → u (suc k)) v n)}
    {y =
      absᶜ (u zero ·ᶜ v (suc n)) +ᶜ
      absᶜ (sequenceCauchyProduct (λ k → u (suc k)) v n)}
    {z =
      U zero ·ᶜ V (suc n) +ᶜ
      sequenceCauchyProduct (λ k → U (suc k)) V n}
    (absᶜ-triangle
      (u zero ·ᶜ v (suc n))
      (sequenceCauchyProduct (λ k → u (suc k)) v n))
    (≤ᶜ-add
      {a = absᶜ (u zero ·ᶜ v (suc n))}
      {b = U zero ·ᶜ V (suc n)}
      {c = absᶜ (sequenceCauchyProduct (λ k → u (suc k)) v n)}
      {d = sequenceCauchyProduct (λ k → U (suc k)) V n}
      (absᶜ-mul≤product
        (u zero)
        (v (suc n))
        (U zero)
        (V (suc n))
        (0≤U zero)
        (0≤V (suc n))
        (u≤U zero)
        (v≤V (suc n)))
      (sequenceCauchyProduct-termMajorized
        (λ k → u (suc k))
        v
        (λ k → U (suc k))
        V
        (λ k → u≤U (suc k))
        (λ k → 0≤U (suc k))
        v≤V
        0≤V
        n))


sequenceCauchyProductMajorizedByTerms :
  {u v U V : ℕ → ℝᶜ} →
  ((n : ℕ) → absᶜ (u n) ≤ᶜ U n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ U n) →
  ((n : ℕ) → absᶜ (v n) ≤ᶜ V n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ V n) →
  SeriesMajorizedBy
    (sequenceCauchyProduct u v)
    (sequenceCauchyProduct U V)
sequenceCauchyProductMajorizedByTerms {u = u} {v = v} {U = U} {V = V}
  u≤U
  0≤U
  v≤V
  0≤V =
  seriesMajorizedByTerms
    (sequenceCauchyProduct-termMajorized u v U V u≤U 0≤U v≤V 0≤V)
    (sequenceCauchyProduct-nonnegative U V 0≤U 0≤V)


sequenceCauchyProductMajorizedBy :
  {u v U V : ℕ → ℝᶜ} →
  SeriesMajorizedBy u U →
  SeriesMajorizedBy v V →
  SeriesMajorizedBy
    (sequenceCauchyProduct u v)
    (sequenceCauchyProduct U V)
sequenceCauchyProductMajorizedBy u-majorized v-majorized =
  sequenceCauchyProductMajorizedByTerms
    (λ n → SeriesMajorizedBy.termMajorized u-majorized zero n)
    (λ n → SeriesMajorizedBy.majorantNonnegative u-majorized zero n)
    (λ n → SeriesMajorizedBy.termMajorized v-majorized zero n)
    (λ n → SeriesMajorizedBy.majorantNonnegative v-majorized zero n)


sequenceCauchyProductTailBoundFromMajorant :
  {u v U V : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  SeriesMajorizedBy u U →
  SeriesMajorizedBy v V →
  TailBound (sequenceCauchyProduct U V) μ →
  TailBound (sequenceCauchyProduct u v) μ
sequenceCauchyProductTailBoundFromMajorant u-majorized v-majorized =
  comparisonTest
    (sequenceCauchyProductMajorizedBy u-majorized v-majorized)


seriesPartialSumsEventuallyBoundedBySum :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (uTail : TailBound u μ) →
  (μ-antitone : AntitoneTailModulus μ) →
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


sequenceCauchyProductTailBoundFromMajorantRemainderBoundAndSumBounds :
  {u v U V : ℕ → ℝᶜ} →
  (ν τ χ : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneTailModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneTailModulus τ) →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (sumU-bound :
    BoundedByᶜ ι (seriesSumFromFiniteTailBound u ν uTail ν-antitone)) →
  (sumV-bound :
    BoundedByᶜ κ (seriesSumFromFiniteTailBound v τ vTail τ-antitone)) →
  (majorantRemainderBound :
    (ε : ℚ⁺) →
    (n : ℕ) →
    NatOrder._≤_ (χ ε) n →
    BoundedByᶜ ε (rectangularTriangularRemainder U V n n)) →
  TailBound
    (sequenceCauchyProduct u v)
    (λ ε →
      sequenceCauchyProductPartialSumsConvergeToProductFromRemainderConvergence
        u
        v
        ν
        τ
        (λ ε → χ (half⁺ ε))
        (λ _ → τ (quarter⁺ (half⁺ (half⁺ 1⁺))))
        (1⁺ +⁺ κ)
        ι
        uTail
        ν-antitone
        vTail
        τ-antitone
        sumU-bound
        (seriesPartialSumsEventuallyBoundedBySum
          _
          τ
          vTail
          τ-antitone
          κ
          sumV-bound)
        (rectangularTriangularRemainderConvergesFromMajorantBound
          uMajorized
          vMajorized
          χ
          majorantRemainderBound)
        .fst
        (quarter⁺ ε))
sequenceCauchyProductTailBoundFromMajorantRemainderBoundAndSumBounds
  {u = u}
  {v = v}
  ν
  τ
  χ
  κ
  ι
  uTail
  ν-antitone
  vTail
  τ-antitone
  uMajorized
  vMajorized
  sumU-bound
  sumV-bound
  majorantRemainderBound =
  sequenceCauchyProductTailBoundFromMajorantRemainderBound
    {u = u}
    {v = v}
    ν
    τ
    χ
    (λ _ → τ (quarter⁺ (half⁺ (half⁺ 1⁺))))
    (1⁺ +⁺ κ)
    ι
    uTail
    ν-antitone
    vTail
    τ-antitone
    uMajorized
    vMajorized
    sumU-bound
    (seriesPartialSumsEventuallyBoundedBySum
      _
      τ
      vTail
      τ-antitone
      κ
      sumV-bound)
    majorantRemainderBound


sequenceCauchyProductSumProductFromMajorantRemainderBound :
  {u v U V : ℕ → ℝᶜ} →
  (ν τ μ χ β : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneTailModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneTailModulus τ) →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (productMajorTail : TailBound (sequenceCauchyProduct U V) μ) →
  (μ-antitone : AntitoneTailModulus μ) →
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
  (ν-antitone : AntitoneTailModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneTailModulus τ) →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (productMajorTail : TailBound (sequenceCauchyProduct U V) μ) →
  (μ-antitone : AntitoneTailModulus μ) →
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
  (ν-antitone : AntitoneTailModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneTailModulus τ) →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (productMajorTail : TailBound (sequenceCauchyProduct U V) μ) →
  (μ-antitone : AntitoneTailModulus μ) →
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
  (ν-antitone : AntitoneTailModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneTailModulus τ) →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (productMajorTail : TailBound (sequenceCauchyProduct U V) μ) →
  (μ-antitone : AntitoneTailModulus μ) →
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


cauchyProductPowerSeries-sequenceCauchyProduct :
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a b n ≡ sequenceCauchyProduct a b n
cauchyProductPowerSeries-sequenceCauchyProduct a b zero =
  refl
cauchyProductPowerSeries-sequenceCauchyProduct a b (suc n) =
  cong
    (a zero ·ᶜ b (suc n) +ᶜ_)
    (cauchyProductPowerSeries-sequenceCauchyProduct
      (shiftPowerSeries a)
      b
      n)


cauchyProductPowerSeriesMajorizedBy :
  {a b A B : PowerSeries} →
  SeriesMajorizedBy a A →
  SeriesMajorizedBy b B →
  SeriesMajorizedBy
    (cauchyProductPowerSeries a b)
    (sequenceCauchyProduct A B)
cauchyProductPowerSeriesMajorizedBy {a = a} {b = b} {A = A} {B = B}
  a-majorized
  b-majorized =
  seriesMajorizedByTerms termMajorized majorantNonnegative
  where
  sequenceMajorized :
    SeriesMajorizedBy
      (sequenceCauchyProduct a b)
      (sequenceCauchyProduct A B)
  sequenceMajorized =
    sequenceCauchyProductMajorizedBy a-majorized b-majorized

  termMajorized :
    (n : ℕ) →
    absᶜ (cauchyProductPowerSeries a b n) ≤ᶜ
    sequenceCauchyProduct A B n
  termMajorized n =
    subst
      (λ z → absᶜ z ≤ᶜ sequenceCauchyProduct A B n)
      (sym (cauchyProductPowerSeries-sequenceCauchyProduct a b n))
      (SeriesMajorizedBy.termMajorized sequenceMajorized zero n)

  majorantNonnegative :
    (n : ℕ) →
    0ᶜ ≤ᶜ sequenceCauchyProduct A B n
  majorantNonnegative n =
    SeriesMajorizedBy.majorantNonnegative sequenceMajorized zero n


cauchyProductPowerSeriesTailBoundFromMajorant :
  {a b A B : PowerSeries} →
  {μ : ℚ⁺ → ℕ} →
  SeriesMajorizedBy a A →
  SeriesMajorizedBy b B →
  TailBound (sequenceCauchyProduct A B) μ →
  TailBound (cauchyProductPowerSeries a b) μ
cauchyProductPowerSeriesTailBoundFromMajorant a-majorized b-majorized =
  comparisonTest
    (cauchyProductPowerSeriesMajorizedBy a-majorized b-majorized)


powerSeriesTerm-shift-scale :
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  h ·ᶜ powerSeriesTerm (shiftPowerSeries a) h n ≡
  powerSeriesTerm a h (suc n)
powerSeriesTerm-shift-scale a h n =
  mulᶜ-assoc h (a (suc n)) (realPower h n) ∙
  cong
    (_·ᶜ realPower h n)
    (mulᶜ-comm h (a (suc n))) ∙
  sym (mulᶜ-assoc (a (suc n)) h (realPower h n)) ∙
  cong
    (a (suc n) ·ᶜ_)
    (sym (realPower-suc h n))


mul-realPower-suc-reassociate :
  (x h : ℝᶜ) →
  (n : ℕ) →
  x ·ᶜ realPower h (suc n) ≡
  h ·ᶜ (x ·ᶜ realPower h n)
mul-realPower-suc-reassociate x h n =
  cong (x ·ᶜ_) (realPower-suc h n) ∙
  mulᶜ-assoc x h (realPower h n) ∙
  cong
    (_·ᶜ realPower h n)
    (mulᶜ-comm x h) ∙
  sym (mulᶜ-assoc h x (realPower h n))


cauchyProductTerm-head-path :
  (x y h : ℝᶜ) →
  (n : ℕ) →
  (x ·ᶜ y) ·ᶜ realPower h n ≡
  (x ·ᶜ realPower h zero) ·ᶜ (y ·ᶜ realPower h n)
cauchyProductTerm-head-path x y h n =
  sym (mulᶜ-assoc x y (realPower h n)) ∙
  cong
    (_·ᶜ (y ·ᶜ realPower h n))
    (sym
      (cong
        (x ·ᶜ_)
        (realPower-zero h) ∙
       mulᶜ-one-right x))


cauchyProductPowerSeriesTerm-sequenceCauchyProduct :
  (a b : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm (cauchyProductPowerSeries a b) h n ≡
  sequenceCauchyProduct (powerSeriesTerm a h) (powerSeriesTerm b h) n
cauchyProductPowerSeriesTerm-sequenceCauchyProduct a b h zero =
  cauchyProductTerm-head-path
    (a zero)
    (b zero)
    h
    zero
cauchyProductPowerSeriesTerm-sequenceCauchyProduct a b h (suc n) =
  mulᶜ-distrib-left
    (a zero ·ᶜ b (suc n))
    (cauchyProductPowerSeries (shiftPowerSeries a) b n)
    (realPower h (suc n)) ∙
  cong₂
    _+ᶜ_
    (cauchyProductTerm-head-path
      (a zero)
      (b (suc n))
      h
      (suc n))
    tail-path
  where
  tail-path :
    cauchyProductPowerSeries (shiftPowerSeries a) b n ·ᶜ
      realPower h (suc n)
    ≡
    sequenceCauchyProduct
      (λ k → powerSeriesTerm a h (suc k))
      (powerSeriesTerm b h)
      n
  tail-path =
    mul-realPower-suc-reassociate
      (cauchyProductPowerSeries (shiftPowerSeries a) b n)
      h
      n ∙
    cong
      (h ·ᶜ_)
      (cauchyProductPowerSeriesTerm-sequenceCauchyProduct
        (shiftPowerSeries a)
        b
        h
        n) ∙
    sym
      (sequenceCauchyProduct-scale-left
        h
        (powerSeriesTerm (shiftPowerSeries a) h)
        (powerSeriesTerm b h)
        n) ∙
    sequenceCauchyProduct-cong-left
      (powerSeriesTerm-shift-scale a h)
      n


cauchyProductPowerSeriesPartialSum-sequenceCauchyProduct :
  (a b : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesPartialSum (cauchyProductPowerSeries a b) h n ≡
  partialSum
    (sequenceCauchyProduct (powerSeriesTerm a h) (powerSeriesTerm b h))
    n
cauchyProductPowerSeriesPartialSum-sequenceCauchyProduct a b h n =
  cong
    (λ u → partialSum u n)
    (funExt (cauchyProductPowerSeriesTerm-sequenceCauchyProduct a b h))


cauchyProductPowerSeriesPartialSum-triangularRows :
  (a b : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesPartialSum (cauchyProductPowerSeries a b) h n ≡
  triangularRows (powerSeriesTerm a h) (powerSeriesTerm b h) n
cauchyProductPowerSeriesPartialSum-triangularRows a b h n =
  cauchyProductPowerSeriesPartialSum-sequenceCauchyProduct a b h n ∙
  triangularRows-partialCauchyProduct
    (powerSeriesTerm a h)
    (powerSeriesTerm b h)
    n


powerSeriesPartialSum-product-rectangularRows :
  (a b : PowerSeries) →
  (h : ℝᶜ) →
  (m n : ℕ) →
  powerSeriesPartialSum a h m ·ᶜ powerSeriesPartialSum b h n ≡
  rectangularRows (powerSeriesTerm a h) (powerSeriesTerm b h) m n
powerSeriesPartialSum-product-rectangularRows a b h =
  rectangularRows-partialProduct (powerSeriesTerm a h) (powerSeriesTerm b h)


powerSeriesPartialProduct-cauchyProductRemainder :
  (a b : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  (powerSeriesPartialSum a h n ·ᶜ powerSeriesPartialSum b h n) +ᶜ
    (-ᶜ powerSeriesPartialSum (cauchyProductPowerSeries a b) h n)
  ≡
  rectangularTriangularRemainder
    (powerSeriesTerm a h)
    (powerSeriesTerm b h)
    n
    n
powerSeriesPartialProduct-cauchyProductRemainder a b h n =
  cong₂
    (λ x y → x +ᶜ (-ᶜ y))
    (powerSeriesPartialSum-product-rectangularRows a b h n n)
    (cauchyProductPowerSeriesPartialSum-triangularRows a b h n) ∙
  rectangularRows-triangularRows-remainder
    (powerSeriesTerm a h)
    (powerSeriesTerm b h)
    n
    n


cauchyProductPowerSeriesSumProductFromRemainderBound :
  (a b : PowerSeries) →
  (h : ℝᶜ) →
  (ν τ μ χ β : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (leftTail : PowerSeriesTailBound a h ν) →
  (ν-antitone : AntitoneTailModulus ν) →
  (rightTail : PowerSeriesTailBound b h τ) →
  (τ-antitone : AntitoneTailModulus τ) →
  (productTail :
    PowerSeriesTailBound (cauchyProductPowerSeries a b) h μ) →
  (μ-antitone : AntitoneTailModulus μ) →
  BoundedByᶜ
    ι
    (powerSeriesSumFromFiniteTailBound
      a
      h
      ν
      leftTail
      ν-antitone) →
  SeqAlg.EventuallyBoundedByWith
    β
    κ
    (partialSumSequence (powerSeriesTerm b h)) →
  ((ε : ℚ⁺) →
    (n : ℕ) →
    NatOrder._≤_ (χ ε) n →
    BoundedByᶜ
      ε
      (rectangularTriangularRemainder
        (powerSeriesTerm a h)
        (powerSeriesTerm b h)
        n
        n)) →
  powerSeriesSumFromFiniteTailBound
    (cauchyProductPowerSeries a b)
    h
    μ
    productTail
    μ-antitone
  ≡
  powerSeriesSumFromFiniteTailBound a h ν leftTail ν-antitone ·ᶜ
  powerSeriesSumFromFiniteTailBound b h τ rightTail τ-antitone
cauchyProductPowerSeriesSumProductFromRemainderBound
  a
  b
  h
  ν
  τ
  μ
  χ
  β
  κ
  ι
  leftTail
  ν-antitone
  rightTail
  τ-antitone
  productTail
  μ-antitone
  leftSum-bound
  rightPartial-bound
  remainderBound =
  seriesSumFromFiniteTailBound-cong termPath productTail μ-antitone ∙
  sequenceCauchyProductSumProductFromRemainderBound
    (powerSeriesTerm a h)
    (powerSeriesTerm b h)
    ν
    τ
    μ
    χ
    β
    κ
    ι
    leftTail
    ν-antitone
    rightTail
    τ-antitone
    sequenceProductTail
    μ-antitone
    leftSum-bound
    rightPartial-bound
    remainderBound
  where
  termPath :
    powerSeriesTerm (cauchyProductPowerSeries a b) h ≡
    sequenceCauchyProduct (powerSeriesTerm a h) (powerSeriesTerm b h)
  termPath =
    funExt (cauchyProductPowerSeriesTerm-sequenceCauchyProduct a b h)

  sequenceProductTail :
    TailBound
      (sequenceCauchyProduct (powerSeriesTerm a h) (powerSeriesTerm b h))
      μ
  sequenceProductTail =
    subst (λ w → TailBound w μ) termPath productTail


cauchyProductPowerSeriesSumOnBallProductFromRemainderBound :
  (a b : PowerSeries) →
  {ρ : ℚ⁺} →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  {ν τ μ χ β : ℚ⁺ → ℕ} →
  (κ ι : ℚ⁺) →
  (leftConvergence : HasPowerSeriesOnBallWith a ρ ν) →
  (rightConvergence : HasPowerSeriesOnBallWith b ρ τ) →
  (productConvergence :
    HasPowerSeriesOnBallWith (cauchyProductPowerSeries a b) ρ μ) →
  BoundedByᶜ
    ι
    (powerSeriesSumOnBall a ρ ν leftConvergence h h-bound) →
  SeqAlg.EventuallyBoundedByWith
    β
    κ
    (partialSumSequence (powerSeriesTerm b h)) →
  ((ε : ℚ⁺) →
    (n : ℕ) →
    NatOrder._≤_ (χ ε) n →
    BoundedByᶜ
      ε
      (rectangularTriangularRemainder
        (powerSeriesTerm a h)
        (powerSeriesTerm b h)
        n
        n)) →
  powerSeriesSumOnBall
    (cauchyProductPowerSeries a b)
    ρ
    μ
    productConvergence
    h
    h-bound
  ≡
  powerSeriesSumOnBall a ρ ν leftConvergence h h-bound ·ᶜ
  powerSeriesSumOnBall b ρ τ rightConvergence h h-bound
cauchyProductPowerSeriesSumOnBallProductFromRemainderBound
  a
  b
  {ρ = ρ}
  h
  h-bound
  {ν = ν}
  {τ = τ}
  {μ = μ}
  {χ = χ}
  {β = β}
  κ
  ι
  leftConvergence
  rightConvergence
  productConvergence =
  cauchyProductPowerSeriesSumProductFromRemainderBound
    a
    b
    h
    ν
    τ
    μ
    χ
    β
    κ
    ι
    (HasPowerSeriesOnBallWith.tailBound leftConvergence h h-bound)
    (HasPowerSeriesOnBallWith.antitoneModulus leftConvergence)
    (HasPowerSeriesOnBallWith.tailBound rightConvergence h h-bound)
    (HasPowerSeriesOnBallWith.antitoneModulus rightConvergence)
    (HasPowerSeriesOnBallWith.tailBound productConvergence h h-bound)
    (HasPowerSeriesOnBallWith.antitoneModulus productConvergence)


cauchyProductPowerSeriesMajorizedOnBallFromMajorants :
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ : ℚ⁺ → ℕ} →
  PowerSeriesMajorizedOnBall a ρ A ν →
  PowerSeriesMajorizedOnBall b ρ B τ →
  TailBound (sequenceCauchyProduct A B) μ →
  AntitoneTailModulus μ →
  PowerSeriesMajorizedOnBall
    (cauchyProductPowerSeries a b)
    ρ
    (sequenceCauchyProduct A B)
    μ
cauchyProductPowerSeriesMajorizedOnBallFromMajorants
  {a = a}
  {b = b}
  {A = A}
  {B = B}
  {ρ = ρ}
  {ν = ν}
  {τ = τ}
  left
  right
  productTail
  productAntitone =
  termMajorized ,
  productTail ,
  productAntitone
  where
  termMajorized :
    (h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy
      (powerSeriesTerm (cauchyProductPowerSeries a b) h)
      (sequenceCauchyProduct A B)
  termMajorized h h-bound =
    seriesMajorizedByTerms termBound majorantNonnegative
    where
    sequenceMajorized :
      SeriesMajorizedBy
        (sequenceCauchyProduct (powerSeriesTerm a h) (powerSeriesTerm b h))
        (sequenceCauchyProduct A B)
    sequenceMajorized =
      sequenceCauchyProductMajorizedBy
        (PowerSeriesMajorizedOnBall.termMajorized
          {a = a}
          {ρ = ρ}
          {v = A}
          {μ = ν}
          left
          h
          h-bound)
        (PowerSeriesMajorizedOnBall.termMajorized
          {a = b}
          {ρ = ρ}
          {v = B}
          {μ = τ}
          right
          h
          h-bound)

    termBound :
      (n : ℕ) →
      absᶜ (powerSeriesTerm (cauchyProductPowerSeries a b) h n) ≤ᶜ
      sequenceCauchyProduct A B n
    termBound n =
      subst
        (λ z → absᶜ z ≤ᶜ sequenceCauchyProduct A B n)
        (sym (cauchyProductPowerSeriesTerm-sequenceCauchyProduct a b h n))
        (SeriesMajorizedBy.termMajorized sequenceMajorized zero n)

    majorantNonnegative :
      (n : ℕ) →
      0ᶜ ≤ᶜ sequenceCauchyProduct A B n
    majorantNonnegative n =
      SeriesMajorizedBy.majorantNonnegative sequenceMajorized zero n


cauchyProductPowerSeriesOnBallWithFromMajorants :
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ : ℚ⁺ → ℕ} →
  PowerSeriesMajorizedOnBall a ρ A ν →
  PowerSeriesMajorizedOnBall b ρ B τ →
  TailBound (sequenceCauchyProduct A B) μ →
  AntitoneTailModulus μ →
  HasPowerSeriesOnBallWith
    (cauchyProductPowerSeries a b)
    ρ
    μ
cauchyProductPowerSeriesOnBallWithFromMajorants left right productTail productAntitone =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (cauchyProductPowerSeriesMajorizedOnBallFromMajorants
      left
      right
      productTail
      productAntitone)


cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndRemainderBound :
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ χ β : ℚ⁺ → ℕ} →
  (left : PowerSeriesMajorizedOnBall a ρ A ν) →
  (right : PowerSeriesMajorizedOnBall b ρ B τ) →
  (productTail : TailBound (sequenceCauchyProduct A B) μ) →
  (productAntitone : AntitoneTailModulus μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (κ ι : ℚ⁺) →
  BoundedByᶜ
    ι
    (powerSeriesSumOnBall
      a
      ρ
      ν
      (majorizedOnBall→hasPowerSeriesOnBallWith left)
      h
      h-bound) →
  SeqAlg.EventuallyBoundedByWith
    β
    κ
    (partialSumSequence (powerSeriesTerm b h)) →
  ((ε : ℚ⁺) →
    (n : ℕ) →
    NatOrder._≤_ (χ ε) n →
    BoundedByᶜ
      ε
      (rectangularTriangularRemainder
        (powerSeriesTerm a h)
        (powerSeriesTerm b h)
        n
        n)) →
  powerSeriesSumOnBall
    (cauchyProductPowerSeries a b)
    ρ
    μ
    (cauchyProductPowerSeriesOnBallWithFromMajorants
      left
      right
      productTail
      productAntitone)
    h
    h-bound
  ≡
  powerSeriesSumOnBall
    a
    ρ
    ν
    (majorizedOnBall→hasPowerSeriesOnBallWith left)
    h
    h-bound
  ·ᶜ
  powerSeriesSumOnBall
    b
    ρ
    τ
    (majorizedOnBall→hasPowerSeriesOnBallWith right)
    h
    h-bound
cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndRemainderBound
  {a = a}
  {b = b}
  left
  right
  productTail
  productAntitone
  h
  h-bound
  κ
  ι =
  cauchyProductPowerSeriesSumOnBallProductFromRemainderBound
    a
    b
    h
    h-bound
    κ
    ι
    (majorizedOnBall→hasPowerSeriesOnBallWith left)
    (majorizedOnBall→hasPowerSeriesOnBallWith right)
    (cauchyProductPowerSeriesOnBallWithFromMajorants
      left
      right
      productTail
      productAntitone)


cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndMajorantRemainderBound :
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ χ β : ℚ⁺ → ℕ} →
  (left : PowerSeriesMajorizedOnBall a ρ A ν) →
  (right : PowerSeriesMajorizedOnBall b ρ B τ) →
  (productTail : TailBound (sequenceCauchyProduct A B) μ) →
  (productAntitone : AntitoneTailModulus μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (κ ι : ℚ⁺) →
  BoundedByᶜ
    ι
    (powerSeriesSumOnBall
      a
      ρ
      ν
      (majorizedOnBall→hasPowerSeriesOnBallWith left)
      h
      h-bound) →
  SeqAlg.EventuallyBoundedByWith
    β
    κ
    (partialSumSequence (powerSeriesTerm b h)) →
  ((ε : ℚ⁺) →
    (n : ℕ) →
    NatOrder._≤_ (χ ε) n →
    BoundedByᶜ
      ε
      (rectangularTriangularRemainder A B n n)) →
  powerSeriesSumOnBall
    (cauchyProductPowerSeries a b)
    ρ
    μ
    (cauchyProductPowerSeriesOnBallWithFromMajorants
      left
      right
      productTail
      productAntitone)
    h
    h-bound
  ≡
  powerSeriesSumOnBall
    a
    ρ
    ν
    (majorizedOnBall→hasPowerSeriesOnBallWith left)
    h
    h-bound
  ·ᶜ
  powerSeriesSumOnBall
    b
    ρ
    τ
    (majorizedOnBall→hasPowerSeriesOnBallWith right)
    h
    h-bound
cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndMajorantRemainderBound
  left
  right
  productTail
  productAntitone
  h
  h-bound
  κ
  ι
  leftSum-bound
  rightPartial-bound
  majorantRemainderBound =
  cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndRemainderBound
    left
    right
    productTail
    productAntitone
    h
    h-bound
    κ
    ι
    leftSum-bound
    rightPartial-bound
    (λ ε n χ≤n →
      rectangularTriangularRemainderBoundFromMajorant
        (PowerSeriesMajorizedOnBall.termMajorized left h h-bound)
        (PowerSeriesMajorizedOnBall.termMajorized right h h-bound)
        ε
        n
        (majorantRemainderBound ε n χ≤n))


cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTailSubset :
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ β : ℚ⁺ → ℕ} →
  (left : PowerSeriesMajorizedOnBall a ρ A ν) →
  (right : PowerSeriesMajorizedOnBall b ρ B τ) →
  (productTail : TailBound (sequenceCauchyProduct A B) μ) →
  (productAntitone : AntitoneTailModulus μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (κ ι : ℚ⁺) →
  BoundedByᶜ
    ι
    (powerSeriesSumOnBall
      a
      ρ
      ν
      (majorizedOnBall→hasPowerSeriesOnBallWith left)
      h
      h-bound) →
  SeqAlg.EventuallyBoundedByWith
    β
    κ
    (partialSumSequence (powerSeriesTerm b h)) →
  ((n : ℕ) →
    rectangularTriangularRemainder A B n n ≤ᶜ
    tailSum (sequenceCauchyProduct A B) n n) →
  powerSeriesSumOnBall
    (cauchyProductPowerSeries a b)
    ρ
    μ
    (cauchyProductPowerSeriesOnBallWithFromMajorants
      left
      right
      productTail
      productAntitone)
    h
    h-bound
  ≡
  powerSeriesSumOnBall
    a
    ρ
    ν
    (majorizedOnBall→hasPowerSeriesOnBallWith left)
    h
    h-bound
  ·ᶜ
  powerSeriesSumOnBall
    b
    ρ
    τ
    (majorizedOnBall→hasPowerSeriesOnBallWith right)
    h
    h-bound
cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTailSubset
  {A = A}
  {B = B}
  {μ = μ}
  left
  right
  productTail
  productAntitone
  h
  h-bound
  κ
  ι
  leftSum-bound
  rightPartial-bound
  remainder≤tail =
  cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndMajorantRemainderBound
    {χ = μ}
    left
    right
    productTail
    productAntitone
    h
    h-bound
    κ
    ι
    leftSum-bound
    rightPartial-bound
    (rectangularTriangularRemainderBoundFromProductTail
      A
      B
      A-nonnegative
      B-nonnegative
      remainder≤tail
      productTail)
  where
  A-nonnegative :
    (n : ℕ) → 0ᶜ ≤ᶜ A n
  A-nonnegative n =
    SeriesMajorizedBy.majorantNonnegative
      (PowerSeriesMajorizedOnBall.termMajorized left h h-bound)
      zero
      n

  B-nonnegative :
    (n : ℕ) → 0ᶜ ≤ᶜ B n
  B-nonnegative n =
    SeriesMajorizedBy.majorantNonnegative
      (PowerSeriesMajorizedOnBall.termMajorized right h h-bound)
      zero
      n


cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTailWithPartialBound :
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ β : ℚ⁺ → ℕ} →
  (left : PowerSeriesMajorizedOnBall a ρ A ν) →
  (right : PowerSeriesMajorizedOnBall b ρ B τ) →
  (productTail : TailBound (sequenceCauchyProduct A B) μ) →
  (productAntitone : AntitoneTailModulus μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (κ ι : ℚ⁺) →
  BoundedByᶜ
    ι
    (powerSeriesSumOnBall
      a
      ρ
      ν
      (majorizedOnBall→hasPowerSeriesOnBallWith left)
      h
      h-bound) →
  SeqAlg.EventuallyBoundedByWith
    β
    κ
    (partialSumSequence (powerSeriesTerm b h)) →
  powerSeriesSumOnBall
    (cauchyProductPowerSeries a b)
    ρ
    μ
    (cauchyProductPowerSeriesOnBallWithFromMajorants
      left
      right
      productTail
      productAntitone)
    h
    h-bound
  ≡
  powerSeriesSumOnBall
    a
    ρ
    ν
    (majorizedOnBall→hasPowerSeriesOnBallWith left)
    h
    h-bound
  ·ᶜ
  powerSeriesSumOnBall
    b
    ρ
    τ
    (majorizedOnBall→hasPowerSeriesOnBallWith right)
    h
    h-bound
cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTailWithPartialBound
  {A = A}
  {B = B}
  left
  right
  productTail
  productAntitone
  h
  h-bound
  κ
  ι
  leftSum-bound
  rightPartial-bound =
  cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTailSubset
    left
    right
    productTail
    productAntitone
    h
    h-bound
    κ
    ι
    leftSum-bound
    rightPartial-bound
    (λ n →
      rectangularTriangularRemainder≤cauchyProductTail
        A
        B
        A-nonnegative
        B-nonnegative
        n
        n
        NatOrder.≤-refl)
  where
  A-nonnegative :
    (n : ℕ) → 0ᶜ ≤ᶜ A n
  A-nonnegative n =
    SeriesMajorizedBy.majorantNonnegative
      (PowerSeriesMajorizedOnBall.termMajorized left h h-bound)
      zero
      n

  B-nonnegative :
    (n : ℕ) → 0ᶜ ≤ᶜ B n
  B-nonnegative n =
    SeriesMajorizedBy.majorantNonnegative
      (PowerSeriesMajorizedOnBall.termMajorized right h h-bound)
      zero
      n


cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTailAndSumBounds :
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ : ℚ⁺ → ℕ} →
  (left : PowerSeriesMajorizedOnBall a ρ A ν) →
  (right : PowerSeriesMajorizedOnBall b ρ B τ) →
  (productTail : TailBound (sequenceCauchyProduct A B) μ) →
  (productAntitone : AntitoneTailModulus μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (κ ι : ℚ⁺) →
  BoundedByᶜ
    ι
    (powerSeriesSumOnBall
      a
      ρ
      ν
      (majorizedOnBall→hasPowerSeriesOnBallWith left)
      h
      h-bound) →
  BoundedByᶜ
    κ
    (powerSeriesSumOnBall
      b
      ρ
      τ
      (majorizedOnBall→hasPowerSeriesOnBallWith right)
      h
      h-bound) →
  powerSeriesSumOnBall
    (cauchyProductPowerSeries a b)
    ρ
    μ
    (cauchyProductPowerSeriesOnBallWithFromMajorants
      left
      right
      productTail
      productAntitone)
    h
    h-bound
  ≡
  powerSeriesSumOnBall
    a
    ρ
    ν
    (majorizedOnBall→hasPowerSeriesOnBallWith left)
    h
    h-bound
  ·ᶜ
  powerSeriesSumOnBall
    b
    ρ
    τ
    (majorizedOnBall→hasPowerSeriesOnBallWith right)
    h
    h-bound
cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTailAndSumBounds
  {b = b}
  {ρ = ρ}
  {τ = τ}
  left
  right
  productTail
  productAntitone
  h
  h-bound
  κ
  ι
  leftSum-bound
  rightSum-bound =
  cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTailWithPartialBound
    left
    right
    productTail
    productAntitone
    h
    h-bound
    (1⁺ +⁺ κ)
    ι
    leftSum-bound
    (seriesPartialSumsEventuallyBoundedBySum
      (powerSeriesTerm b h)
      τ
      rightTail
      rightAntitone
      κ
      rightSum-bound)
  where
  rightConvergence :
    HasPowerSeriesOnBallWith b ρ τ
  rightConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith right

  rightTail :
    TailBound (powerSeriesTerm b h) τ
  rightTail =
    HasPowerSeriesOnBallWith.tailBound rightConvergence h h-bound

  rightAntitone :
    AntitoneTailModulus τ
  rightAntitone =
    HasPowerSeriesOnBallWith.antitoneModulus rightConvergence


cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTail :
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ : ℚ⁺ → ℕ} →
  (left : PowerSeriesMajorizedOnBall a ρ A ν) →
  (right : PowerSeriesMajorizedOnBall b ρ B τ) →
  (productTail : TailBound (sequenceCauchyProduct A B) μ) →
  (productAntitone : AntitoneTailModulus μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (cauchyProductPowerSeries a b)
    ρ
    μ
    (cauchyProductPowerSeriesOnBallWithFromMajorants
      left
      right
      productTail
      productAntitone)
    h
    h-bound
  ≡
  powerSeriesSumOnBall
    a
    ρ
    ν
    (majorizedOnBall→hasPowerSeriesOnBallWith left)
    h
    h-bound
  ·ᶜ
  powerSeriesSumOnBall
    b
    ρ
    τ
    (majorizedOnBall→hasPowerSeriesOnBallWith right)
    h
    h-bound
cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTail
  {a = a}
  {b = b}
  {ρ = ρ}
  {μ = μ}
  {ν = ν}
  {τ = τ}
  left
  right
  productTail
  productAntitone
  h
  h-bound =
  Prop.rec
    (isSetCompletion productSum productOfSums)
    step-left
    (merely-boundedᶜ leftSum)
  where
  leftConvergence :
    HasPowerSeriesOnBallWith a ρ ν
  leftConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith left

  rightConvergence :
    HasPowerSeriesOnBallWith b ρ τ
  rightConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith right

  productConvergence :
    HasPowerSeriesOnBallWith (cauchyProductPowerSeries a b) ρ μ
  productConvergence =
    cauchyProductPowerSeriesOnBallWithFromMajorants
      left
      right
      productTail
      productAntitone

  productSum : ℝᶜ
  productSum =
    powerSeriesSumOnBall
      (cauchyProductPowerSeries a b)
      ρ
      μ
      productConvergence
      h
      h-bound

  leftSum : ℝᶜ
  leftSum =
    powerSeriesSumOnBall a ρ ν leftConvergence h h-bound

  rightSum : ℝᶜ
  rightSum =
    powerSeriesSumOnBall b ρ τ rightConvergence h h-bound

  productOfSums : ℝᶜ
  productOfSums =
    leftSum ·ᶜ rightSum

  step-left :
    Σ[ ι ∈ ℚ⁺ ] BoundedByᶜ ι leftSum →
    productSum ≡ productOfSums
  step-left (ι , leftSum-bound) =
    Prop.rec
      (isSetCompletion productSum productOfSums)
      step-right
      (merely-boundedᶜ rightSum)
    where
    step-right :
      Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ rightSum →
      productSum ≡ productOfSums
    step-right (κ , rightSum-bound) =
      cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTailAndSumBounds
        left
        right
        productTail
        productAntitone
        h
        h-bound
        κ
        ι
        leftSum-bound
        rightSum-bound


cauchyProductPowerSeriesOnBallFromMajorants :
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ : ℚ⁺ → ℕ} →
  PowerSeriesMajorizedOnBall a ρ A ν →
  PowerSeriesMajorizedOnBall b ρ B τ →
  TailBound (sequenceCauchyProduct A B) μ →
  AntitoneTailModulus μ →
  HasPowerSeriesOnBall (cauchyProductPowerSeries a b) ρ
cauchyProductPowerSeriesOnBallFromMajorants left right productTail productAntitone =
  majorizedOnBall→hasPowerSeriesOnBall
    (cauchyProductPowerSeriesMajorizedOnBallFromMajorants
      left
      right
      productTail
      productAntitone)


cauchyProductPowerSeries-zero :
  (a b : PowerSeries) →
  cauchyProductPowerSeries a b zero ≡ a zero ·ᶜ b zero
cauchyProductPowerSeries-zero a b =
  refl


cauchyProductPowerSeries-suc :
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a b (suc n) ≡
  a zero ·ᶜ b (suc n) +ᶜ
  cauchyProductPowerSeries (shiftPowerSeries a) b n
cauchyProductPowerSeries-suc a b n =
  refl


cauchyProductPowerSeries-suc-right :
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a b (suc n) ≡
  cauchyProductPowerSeries a (shiftPowerSeries b) n +ᶜ
  a (suc n) ·ᶜ b zero
cauchyProductPowerSeries-suc-right a b zero =
  refl
cauchyProductPowerSeries-suc-right a b (suc n) =
  cong
    (a zero ·ᶜ b (suc (suc n)) +ᶜ_)
    (cauchyProductPowerSeries-suc-right (shiftPowerSeries a) b n) ∙
  add-assoc
    (a zero ·ᶜ b (suc (suc n)))
    (cauchyProductPowerSeries (shiftPowerSeries a) (shiftPowerSeries b) n)
    (a (suc (suc n)) ·ᶜ b zero)


cauchyProductPowerSeries-cong :
  {a b c d : PowerSeries} →
  ((n : ℕ) → a n ≡ c n) →
  ((n : ℕ) → b n ≡ d n) →
  (n : ℕ) →
  cauchyProductPowerSeries a b n ≡
  cauchyProductPowerSeries c d n
cauchyProductPowerSeries-cong a≡c b≡d zero =
  cong₂ _·ᶜ_ (a≡c zero) (b≡d zero)
cauchyProductPowerSeries-cong {a = a} {b = b} {c = c} {d = d} a≡c b≡d (suc n) =
  cong₂
    _+ᶜ_
    (cong₂ _·ᶜ_ (a≡c zero) (b≡d (suc n)))
    (cauchyProductPowerSeries-cong
      (λ k → a≡c (suc k))
      b≡d
      n)


cauchyProductPowerSeries-cong-left :
  {a b c : PowerSeries} →
  ((n : ℕ) → a n ≡ c n) →
  (n : ℕ) →
  cauchyProductPowerSeries a b n ≡
  cauchyProductPowerSeries c b n
cauchyProductPowerSeries-cong-left a≡c =
  cauchyProductPowerSeries-cong a≡c (λ _ → refl)


cauchyProductPowerSeries-cong-right :
  {a b d : PowerSeries} →
  ((n : ℕ) → b n ≡ d n) →
  (n : ℕ) →
  cauchyProductPowerSeries a b n ≡
  cauchyProductPowerSeries a d n
cauchyProductPowerSeries-cong-right b≡d =
  cauchyProductPowerSeries-cong (λ _ → refl) b≡d


cauchyProductPowerSeries-zero-left :
  (b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries zeroPowerSeries b n ≡ 0ᶜ
cauchyProductPowerSeries-zero-left b zero =
  mulᶜ-zero-left (b zero)
cauchyProductPowerSeries-zero-left b (suc n) =
  cong₂
    _+ᶜ_
    (mulᶜ-zero-left (b (suc n)))
    (cauchyProductPowerSeries-cong-left
      (λ _ → refl)
      n ∙
    cauchyProductPowerSeries-zero-left b n) ∙
  add-zero-left 0ᶜ


cauchyProductPowerSeries-zero-right :
  (a : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a zeroPowerSeries n ≡ 0ᶜ
cauchyProductPowerSeries-zero-right a zero =
  mulᶜ-zero-right (a zero)
cauchyProductPowerSeries-zero-right a (suc n) =
  cong₂
    _+ᶜ_
    (mulᶜ-zero-right (a zero))
    (cauchyProductPowerSeries-zero-right (shiftPowerSeries a) n) ∙
  add-zero-left 0ᶜ


cauchyProductPowerSeries-constant-left :
  (c : ℝᶜ) →
  (a : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries (constantPowerSeries c) a n ≡ c ·ᶜ a n
cauchyProductPowerSeries-constant-left c a zero =
  refl
cauchyProductPowerSeries-constant-left c a (suc n) =
  cong
    (c ·ᶜ a (suc n) +ᶜ_)
    (cauchyProductPowerSeries-cong-left
      {a = shiftPowerSeries (constantPowerSeries c)}
      {b = a}
      {c = zeroPowerSeries}
      (λ _ → refl)
      n ∙
    cauchyProductPowerSeries-zero-left a n) ∙
  add-zero-right (c ·ᶜ a (suc n))


cauchyProductPowerSeries-one-left :
  (a : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries (constantPowerSeries 1ᶜ) a n ≡ a n
cauchyProductPowerSeries-one-left a n =
  cauchyProductPowerSeries-constant-left 1ᶜ a n ∙
  mulᶜ-one-left (a n)


private
  mulᶜ-neg-left :
    (x y : ℝᶜ) →
    (-ᶜ x) ·ᶜ y ≡ -ᶜ (x ·ᶜ y)
  mulᶜ-neg-left x y =
    mulᶜ-comm (-ᶜ x) y ∙
    mulᶜ-neg-right y x ∙
    cong -ᶜ_ (mulᶜ-comm y x)


cauchyProductPowerSeries-comm :
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a b n ≡
  cauchyProductPowerSeries b a n
cauchyProductPowerSeries-comm a b zero =
  mulᶜ-comm (a zero) (b zero)
cauchyProductPowerSeries-comm a b (suc n) =
  cauchyProductPowerSeries-suc-right a b n ∙
  cong₂
    _+ᶜ_
    (cauchyProductPowerSeries-comm a (shiftPowerSeries b) n)
    (mulᶜ-comm (a (suc n)) (b zero)) ∙
  add-comm
    (cauchyProductPowerSeries (shiftPowerSeries b) a n)
    (b zero ·ᶜ a (suc n))


cauchyProductPowerSeries-constant-right :
  (c : ℝᶜ) →
  (a : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a (constantPowerSeries c) n ≡ a n ·ᶜ c
cauchyProductPowerSeries-constant-right c a n =
  cauchyProductPowerSeries-comm a (constantPowerSeries c) n ∙
  cauchyProductPowerSeries-constant-left c a n ∙
  mulᶜ-comm c (a n)


cauchyProductPowerSeries-one-right :
  (a : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a (constantPowerSeries 1ᶜ) n ≡ a n
cauchyProductPowerSeries-one-right a n =
  cauchyProductPowerSeries-constant-right 1ᶜ a n ∙
  mulᶜ-one-right (a n)


cauchyProductPowerSeries-add-left :
  (a b c : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries (addPowerSeries a b) c n ≡
  cauchyProductPowerSeries a c n +ᶜ
  cauchyProductPowerSeries b c n
cauchyProductPowerSeries-add-left a b c zero =
  mulᶜ-distrib-left (a zero) (b zero) (c zero)
cauchyProductPowerSeries-add-left a b c (suc n) =
  cong₂
    _+ᶜ_
    (mulᶜ-distrib-left (a zero) (b zero) (c (suc n)))
    (cauchyProductPowerSeries-cong-left
      (λ _ → refl)
      n ∙
    cauchyProductPowerSeries-add-left
      (shiftPowerSeries a)
      (shiftPowerSeries b)
      c
      n) ∙
  add-interchange
    (a zero ·ᶜ c (suc n))
    (b zero ·ᶜ c (suc n))
    (cauchyProductPowerSeries (shiftPowerSeries a) c n)
    (cauchyProductPowerSeries (shiftPowerSeries b) c n)


cauchyProductPowerSeries-add-right :
  (a b c : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a (addPowerSeries b c) n ≡
  cauchyProductPowerSeries a b n +ᶜ
  cauchyProductPowerSeries a c n
cauchyProductPowerSeries-add-right a b c n =
  cauchyProductPowerSeries-comm a (addPowerSeries b c) n ∙
  cauchyProductPowerSeries-add-left b c a n ∙
  cong₂
    _+ᶜ_
    (cauchyProductPowerSeries-comm b a n)
    (cauchyProductPowerSeries-comm c a n)


cauchyProductPowerSeries-neg-left :
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries (negPowerSeries a) b n ≡
  negPowerSeries (cauchyProductPowerSeries a b) n
cauchyProductPowerSeries-neg-left a b zero =
  mulᶜ-neg-left (a zero) (b zero)
cauchyProductPowerSeries-neg-left a b (suc n) =
  cong₂
    _+ᶜ_
    (mulᶜ-neg-left (a zero) (b (suc n)))
    (cauchyProductPowerSeries-cong-left
      (λ _ → refl)
      n ∙
    cauchyProductPowerSeries-neg-left (shiftPowerSeries a) b n) ∙
  sym
    (neg-add
      (a zero ·ᶜ b (suc n))
      (cauchyProductPowerSeries (shiftPowerSeries a) b n))


cauchyProductPowerSeries-neg-right :
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a (negPowerSeries b) n ≡
  negPowerSeries (cauchyProductPowerSeries a b) n
cauchyProductPowerSeries-neg-right a b n =
  cauchyProductPowerSeries-comm a (negPowerSeries b) n ∙
  cauchyProductPowerSeries-neg-left b a n ∙
  cong -ᶜ_ (cauchyProductPowerSeries-comm b a n)


cauchyProductPowerSeries-sub-left :
  (a b c : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries (subPowerSeries a b) c n ≡
  subPowerSeries
    (cauchyProductPowerSeries a c)
    (cauchyProductPowerSeries b c)
    n
cauchyProductPowerSeries-sub-left a b c n =
  cauchyProductPowerSeries-add-left a (negPowerSeries b) c n ∙
  cong
    (cauchyProductPowerSeries a c n +ᶜ_)
    (cauchyProductPowerSeries-neg-left b c n)


cauchyProductPowerSeries-sub-right :
  (a b c : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a (subPowerSeries b c) n ≡
  subPowerSeries
    (cauchyProductPowerSeries a b)
    (cauchyProductPowerSeries a c)
    n
cauchyProductPowerSeries-sub-right a b c n =
  cauchyProductPowerSeries-add-right a b (negPowerSeries c) n ∙
  cong
    (cauchyProductPowerSeries a b n +ᶜ_)
    (cauchyProductPowerSeries-neg-right a c n)


cauchyProductPowerSeries-rationalScale-left :
  (q : ℚ) →
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries (rationalScalePowerSeries q a) b n ≡
  rationalScalePowerSeries q (cauchyProductPowerSeries a b) n
cauchyProductPowerSeries-rationalScale-left q a b zero =
  sym (mulᶜ-assoc-rational-left q (a zero) (b zero))
cauchyProductPowerSeries-rationalScale-left q a b (suc n) =
  cong₂
    _+ᶜ_
    (sym (mulᶜ-assoc-rational-left q (a zero) (b (suc n))))
    (cauchyProductPowerSeries-cong-left
      (λ _ → refl)
      n ∙
    cauchyProductPowerSeries-rationalScale-left
      q
      (shiftPowerSeries a)
      b
      n) ∙
  sym
    (mulᶜ-distrib-rational-left
      q
      (a zero ·ᶜ b (suc n))
      (cauchyProductPowerSeries (shiftPowerSeries a) b n))


cauchyProductPowerSeries-rationalScale-right :
  (q : ℚ) →
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a (rationalScalePowerSeries q b) n ≡
  rationalScalePowerSeries q (cauchyProductPowerSeries a b) n
cauchyProductPowerSeries-rationalScale-right q a b n =
  cauchyProductPowerSeries-comm a (rationalScalePowerSeries q b) n ∙
  cauchyProductPowerSeries-rationalScale-left q b a n ∙
  cong
    (rational q ·ᶜ_)
    (cauchyProductPowerSeries-comm b a n)
