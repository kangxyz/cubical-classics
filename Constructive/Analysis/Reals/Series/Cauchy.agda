{-

Series cauchy infrastructure for HoTT Cauchy reals

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Cauchy where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Sum using (inl ; inr)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Modulus
  using (AntitoneNatModulus ; NatModulus ; half-mono-≤)
import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
  using (≤ᶜ-add ; negᶜ-pres≤ᶜ)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace

open import Constructive.Analysis.Reals.Series.Finite
open import Constructive.Analysis.Reals.Series.Tail
open import Constructive.Analysis.Reals.Sequences.Base using (Sequence)
import Constructive.Analysis.Reals.Sequences.Algebra as SeqAlg
import Constructive.Analysis.Reals.Sequences.Cauchy as SeqCauchy
import Constructive.Analysis.Reals.Sequences.Convergence as SeqConv
import Constructive.Analysis.Reals.Sequences.Order as SeqOrder

partialSumSequence :
  (ℕ → ℝᶜ) →
  Sequence
partialSumSequence u =
  partialSum u


seriesRegularCauchyWithModulus :
  (u : ℕ → ℝᶜ) →
  NatModulus →
  Type₀
seriesRegularCauchyWithModulus u μ =
  SeqCauchy.RegularCauchyWithModulus (partialSumSequence u) μ


SeriesTailBound :
  (ℕ → ℝᶜ) →
  (ℚ⁺ → ℕ) →
  Type₀
SeriesTailBound u μ =
  (ε δ : ℚ⁺) →
  BoundedByᶜ
    (half⁺ (ε +⁺ δ))
    (partialSum u (μ ε) +ᶜ (-ᶜ partialSum u (μ δ)))


abstract
  tailBound→SeriesTailBound :
    {u : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
    TailBound u μ →
    AntitoneNatModulus μ →
    SeriesTailBound u (λ ε → μ (half⁺ ε))
  tailBound→SeriesTailBound {u = u} {μ = μ} tailBound μ-antitone ε δ =
    tailBound-pair
      tailBound
      κ
      (μ (half⁺ ε))
      (μ (half⁺ δ))
      μκ≤με/2
      μκ≤μδ/2
    where
    κ : ℚ⁺
    κ =
      half⁺ (ε +⁺ δ)

    ε≤ε+δ : radius ε ℚOrder.≤ radius (ε +⁺ δ)
    ε≤ε+δ =
      ℚOrder.<Weaken≤ (radius ε) (radius (ε +⁺ δ)) (summand-left<sum ε δ)

    δ≤ε+δ : radius δ ℚOrder.≤ radius (ε +⁺ δ)
    δ≤ε+δ =
      ℚOrder.<Weaken≤ (radius δ) (radius (ε +⁺ δ)) (summand-right<sum ε δ)

    ε/2≤κ : radius (half⁺ ε) ℚOrder.≤ radius κ
    ε/2≤κ =
      half-mono-≤ {ε = ε} {δ = ε +⁺ δ} ε≤ε+δ

    δ/2≤κ : radius (half⁺ δ) ℚOrder.≤ radius κ
    δ/2≤κ =
      half-mono-≤ {ε = δ} {δ = ε +⁺ δ} δ≤ε+δ

    μκ≤με/2 : NatOrder._≤_ (μ κ) (μ (half⁺ ε))
    μκ≤με/2 =
      μ-antitone ε/2≤κ

    μκ≤μδ/2 : NatOrder._≤_ (μ κ) (μ (half⁺ δ))
    μκ≤μδ/2 =
      μ-antitone δ/2≤κ


diff-close-zero→close :
  {x y : ℝᶜ} {ε : ℚ⁺} →
  (x +ᶜ (-ᶜ y)) ∼[ ε ] 0ᶜ →
  x ∼[ ε ] y
diff-close-zero→close {x = x} {y = y} {ε = ε} diff∼0 =
  subst2
    (λ u v → u ∼[ ε ] v)
    (minus-plus-cancel-right x y)
    (add-zero-left y)
    (add-close-left diff∼0 y)


seriesTailBound→regularCauchyWithModulus :
  {u : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
  SeriesTailBound u μ →
  seriesRegularCauchyWithModulus u μ
seriesTailBound→regularCauchyWithModulus {u = u} {μ = μ} tailBound ε δ =
  diff-close-zero→close
    (bounded-byᶜ-close-zero
      (half⁺ (ε +⁺ δ))
      (ε +⁺ δ)
      (partialSum u (μ ε) +ᶜ (-ᶜ partialSum u (μ δ)))
      (tailBound ε δ)
      (half< (ε +⁺ δ)))


seriesCauchyApproximationFromTailBound :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  SeriesTailBound u μ →
  MetricCauchy.CauchyApproximation CauchyRealsMetricSpace
seriesCauchyApproximationFromTailBound u μ tailBound =
  SeqCauchy.sequenceCauchyApproximation
    (partialSumSequence u)
    μ
    (seriesTailBound→regularCauchyWithModulus {u = u} {μ = μ} tailBound)


seriesCauchyApproximationFromFiniteTailBound :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  TailBound u μ →
  AntitoneNatModulus μ →
  MetricCauchy.CauchyApproximation CauchyRealsMetricSpace
seriesCauchyApproximationFromFiniteTailBound u μ tailBound μ-antitone =
  seriesCauchyApproximationFromTailBound
    u
    (λ ε → μ (half⁺ ε))
    (tailBound→SeriesTailBound {u = u} {μ = μ} tailBound μ-antitone)


seriesSum :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  SeriesTailBound u μ →
  ℝᶜ
seriesSum u μ tailBound =
  SeqCauchy.cauchyLimit
    (partialSumSequence u)
    μ
    (seriesTailBound→regularCauchyWithModulus {u = u} {μ = μ} tailBound)


seriesSumFromFiniteTailBound :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  TailBound u μ →
  AntitoneNatModulus μ →
  ℝᶜ
seriesSumFromFiniteTailBound u μ tailBound μ-antitone =
  seriesSum
    u
    (λ ε → μ (half⁺ ε))
    (tailBound→SeriesTailBound {u = u} {μ = μ} tailBound μ-antitone)


seriesSumConverges :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : SeriesTailBound u μ) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromTailBound u μ tailBound)
    (seriesSum u μ tailBound)
seriesSumConverges u μ tailBound =
  SeqCauchy.regularCauchyLimitConverges
    (partialSumSequence u)
    μ
    (seriesTailBound→regularCauchyWithModulus {u = u} {μ = μ} tailBound)


seriesSumFromFiniteTailBoundConverges :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : TailBound u μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound u μ tailBound μ-antitone)
    (seriesSumFromFiniteTailBound u μ tailBound μ-antitone)
seriesSumFromFiniteTailBoundConverges u μ tailBound μ-antitone =
  seriesSumConverges
    u
    (λ ε → μ (half⁺ ε))
    (tailBound→SeriesTailBound {u = u} {μ = μ} tailBound μ-antitone)


seriesSumFromFiniteTailBoundConvergesAt :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : TailBound u μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  (ε : ℚ⁺) →
  (n : ℕ) →
  NatOrder._≤_ (μ (quarter⁺ (half⁺ ε))) n →
  seriesSumFromFiniteTailBound u μ tailBound μ-antitone ∼[ ε ]
  partialSum u n
seriesSumFromFiniteTailBoundConvergesAt u μ tailBound μ-antitone ε n μθ≤n =
  subst
    (λ ρ → limitPoint ∼[ ρ ] partialSum u n)
    (half⁺+half⁺≡ ε)
    (MetricSpace.close-triangle
      CauchyRealsMetricSpace
      limit∼approx
      approx∼n)
  where
  η : ℚ⁺
  η =
    half⁺ ε

  κ : ℚ⁺
  κ =
    quarter⁺ ε

  θ : ℚ⁺
  θ =
    quarter⁺ (half⁺ ε)

  approxIndex : ℕ
  approxIndex =
    μ θ

  limitPoint : ℝᶜ
  limitPoint =
    seriesSumFromFiniteTailBound u μ tailBound μ-antitone

  θ≤κ : radius θ ℚOrder.≤ radius κ
  θ≤κ =
    ℚOrder.<Weaken≤
      (radius θ)
      (radius κ)
      (half< κ)

  μκ≤approx : NatOrder._≤_ (μ κ) approxIndex
  μκ≤approx =
    μ-antitone θ≤κ

  μκ≤n : NatOrder._≤_ (μ κ) n
  μκ≤n =
    NatOrder.≤-trans μκ≤approx μθ≤n

  limit∼approx :
    limitPoint ∼[ η ] partialSum u approxIndex
  limit∼approx =
    seriesSumFromFiniteTailBoundConverges
      u
      μ
      tailBound
      μ-antitone
      η
      κ
      (half< η)

  approxDiffBound :
    BoundedByᶜ κ (partialSum u approxIndex +ᶜ (-ᶜ partialSum u n))
  approxDiffBound =
    tailBound-pair
      tailBound
      κ
      approxIndex
      n
      μκ≤approx
      μκ≤n

  approx∼n :
    partialSum u approxIndex ∼[ η ] partialSum u n
  approx∼n =
    diff-close-zero→close
      (bounded-byᶜ-close-zero
        κ
        η
        (partialSum u approxIndex +ᶜ (-ᶜ partialSum u n))
        approxDiffBound
        (half< η))


seriesSumFromFiniteTailBoundConvergesTo :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : TailBound u μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  SeqConv.ConvergesTo
    (partialSumSequence u)
    (seriesSumFromFiniteTailBound u μ tailBound μ-antitone)
seriesSumFromFiniteTailBoundConvergesTo u μ tailBound μ-antitone =
  (λ ε → μ (quarter⁺ (half⁺ ε))) , converges
  where
  converges :
    SeqConv.ConvergesWithModulus
      (partialSumSequence u)
      (seriesSumFromFiniteTailBound u μ tailBound μ-antitone)
      (λ ε → μ (quarter⁺ (half⁺ ε)))
  converges ε n μθ≤n =
    MetricSpace.close-sym
      CauchyRealsMetricSpace
      (seriesSumFromFiniteTailBoundConvergesAt
        u
        μ
        tailBound
        μ-antitone
        ε
        n
        μθ≤n)


seriesSumFromFiniteTailBound-mul-left-convergesAt :
  (a : ℝᶜ) →
  (κ : ℚ⁺) →
  (a-bound : BoundedByᶜ κ a) →
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : TailBound u μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  (ε : ℚ⁺) →
  (n : ℕ) →
  NatOrder._≤_
    (μ (quarter⁺ (half⁺
      (fst (mulᶜ-continuous-right-with-bound κ a a-bound) ε))))
    n →
  a ·ᶜ seriesSumFromFiniteTailBound u μ tailBound μ-antitone ∼[ ε ]
  a ·ᶜ partialSum u n
seriesSumFromFiniteTailBound-mul-left-convergesAt
  a
  κ
  a-bound
  u
  μ
  tailBound
  μ-antitone
  ε
  n
  μθ≤n =
  MetricSpace.close-sym
    CauchyRealsMetricSpace
    (mul-converges .snd ε n μθ≤n)
  where
  cont =
    mulᶜ-continuous-right-with-bound κ a a-bound

  mul-converges :
    SeqConv.ConvergesTo
      (SeqAlg.mulRightSequence a (partialSumSequence u))
      (a ·ᶜ seriesSumFromFiniteTailBound u μ tailBound μ-antitone)
  mul-converges =
    SeqAlg.mulRightConvergesToWithBound
      κ
      a
      a-bound
      (seriesSumFromFiniteTailBoundConvergesTo
        u
        μ
        tailBound
        μ-antitone)


seriesSumFromFiniteTailBound-drop :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : TailBound u μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  (m : ℕ) →
  seriesSumFromFiniteTailBound u μ tailBound μ-antitone ≡
  partialSum u m +ᶜ
  seriesSumFromFiniteTailBound
    (drop m u)
    μ
    (tailBound-drop tailBound m)
    μ-antitone
seriesSumFromFiniteTailBound-drop u μ tailBound μ-antitone m =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    limitPoint
    shiftedLimit
    closeAt
  where
  limitPoint : ℝᶜ
  limitPoint =
    seriesSumFromFiniteTailBound u μ tailBound μ-antitone

  dropLimit : ℝᶜ
  dropLimit =
    seriesSumFromFiniteTailBound
      (drop m u)
      μ
      (tailBound-drop tailBound m)
      μ-antitone

  shiftedLimit : ℝᶜ
  shiftedLimit =
    partialSum u m +ᶜ dropLimit

  closeAt :
    (ε : ℚ⁺) →
    limitPoint ∼[ ε ] shiftedLimit
  closeAt ε =
    subst
      (λ ρ → limitPoint ∼[ ρ ] shiftedLimit)
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        limit∼target
        (MetricSpace.close-sym CauchyRealsMetricSpace shifted∼target))
    where
    η : ℚ⁺
    η =
      half⁺ ε

    n : ℕ
    n =
      μ (quarter⁺ (half⁺ η))

    n≤m+n : NatOrder._≤_ n (m + n)
    n≤m+n =
      m , refl

    limit∼partial :
      limitPoint ∼[ η ] partialSum u (m + n)
    limit∼partial =
      seriesSumFromFiniteTailBoundConvergesAt
        u
        μ
        tailBound
        μ-antitone
        η
        (m + n)
        n≤m+n

    limit∼target :
      limitPoint ∼[ η ]
      (partialSum u m +ᶜ partialSum (drop m u) n)
    limit∼target =
      subst
        (λ z → limitPoint ∼[ η ] z)
        (partialSum-append u m n)
        limit∼partial

    drop∼partial :
      dropLimit ∼[ η ] partialSum (drop m u) n
    drop∼partial =
      seriesSumFromFiniteTailBoundConvergesAt
        (drop m u)
        μ
        (tailBound-drop tailBound m)
        μ-antitone
        η
        n
        NatOrder.≤-refl

    shifted∼target :
      shiftedLimit ∼[ η ]
      (partialSum u m +ᶜ partialSum (drop m u) n)
    shifted∼target =
      add-close-right (partialSum u m) drop∼partial


absoluteSummable→SeriesTailBound :
  {u : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
  AbsolutelySummableWith u μ →
  AntitoneNatModulus μ →
  SeriesTailBound u (λ ε → μ (half⁺ ε))
absoluteSummable→SeriesTailBound absTail μ-antitone =
  tailBound→SeriesTailBound
    (absoluteSummable→tailBound absTail)
    μ-antitone


absoluteSummable→seriesSum :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  AbsolutelySummableWith u μ →
  AntitoneNatModulus μ →
  ℝᶜ
absoluteSummable→seriesSum u μ absTail μ-antitone =
  seriesSumFromFiniteTailBound
    u
    μ
    (absoluteSummable→tailBound absTail)
    μ-antitone


seriesSumFromFiniteTailBound-unique :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : TailBound u μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  (x : ℝᶜ) →
  SeqConv.ConvergesTo (partialSumSequence u) x →
  x ≡ seriesSumFromFiniteTailBound u μ tailBound μ-antitone
seriesSumFromFiniteTailBound-unique u μ tailBound μ-antitone x x-converges =
  SeqConv.convergesToPath
    x-converges
    (seriesSumFromFiniteTailBoundConvergesTo u μ tailBound μ-antitone)


seriesSumFromFiniteTailBound-neg :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : TailBound u μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  seriesSumFromFiniteTailBound
    (λ n → -ᶜ u n)
    μ
    (tailBound-neg tailBound)
    μ-antitone ≡
  -ᶜ seriesSumFromFiniteTailBound u μ tailBound μ-antitone
seriesSumFromFiniteTailBound-neg u μ tailBound μ-antitone =
  SeqConv.convergesToPath
    neg-series-converges
    neg-algebra-converges
  where
  u-converges :
    SeqConv.ConvergesTo
      (partialSumSequence u)
      (seriesSumFromFiniteTailBound u μ tailBound μ-antitone)
  u-converges =
    seriesSumFromFiniteTailBoundConvergesTo u μ tailBound μ-antitone

  neg-raw-converges :
    SeqConv.ConvergesTo
      (SeqAlg.negSequence (partialSumSequence u))
      (-ᶜ seriesSumFromFiniteTailBound u μ tailBound μ-antitone)
  neg-raw-converges =
    SeqAlg.negConvergesTo u-converges

  neg-align :
    SeqOrder.EventuallyWith
      (fst neg-raw-converges)
      (λ _ n →
        SeqAlg.negSequence (partialSumSequence u) n ≡
        partialSumSequence (λ k → -ᶜ u k) n)
  neg-align ε n _ =
    sym (partialSum-neg u n)

  neg-algebra-converges :
    SeqConv.ConvergesTo
      (partialSumSequence (λ k → -ᶜ u k))
      (-ᶜ seriesSumFromFiniteTailBound u μ tailBound μ-antitone)
  neg-algebra-converges =
    SeqOrder.eventuallyEqualPreservesConvergesTo
      neg-raw-converges
      neg-align

  neg-series-converges :
    SeqConv.ConvergesTo
      (partialSumSequence (λ k → -ᶜ u k))
      (seriesSumFromFiniteTailBound
        (λ k → -ᶜ u k)
        μ
        (tailBound-neg tailBound)
        μ-antitone)
  neg-series-converges =
    seriesSumFromFiniteTailBoundConvergesTo
      (λ k → -ᶜ u k)
      μ
      (tailBound-neg tailBound)
      μ-antitone


seriesSumFromFiniteTailBound-add :
  (u v : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (uTailBound : TailBound u μ) →
  (vTailBound : TailBound v μ) →
  (sumTailBound : TailBound (λ n → u n +ᶜ v n) μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  seriesSumFromFiniteTailBound
    (λ n → u n +ᶜ v n)
    μ
    sumTailBound
    μ-antitone ≡
  seriesSumFromFiniteTailBound u μ uTailBound μ-antitone +ᶜ
  seriesSumFromFiniteTailBound v μ vTailBound μ-antitone
seriesSumFromFiniteTailBound-add u v μ uTailBound vTailBound sumTailBound μ-antitone =
  SeqConv.convergesToPath
    sum-series-converges
    sum-algebra-converges
  where
  u-converges :
    SeqConv.ConvergesTo
      (partialSumSequence u)
      (seriesSumFromFiniteTailBound u μ uTailBound μ-antitone)
  u-converges =
    seriesSumFromFiniteTailBoundConvergesTo u μ uTailBound μ-antitone

  v-converges :
    SeqConv.ConvergesTo
      (partialSumSequence v)
      (seriesSumFromFiniteTailBound v μ vTailBound μ-antitone)
  v-converges =
    seriesSumFromFiniteTailBoundConvergesTo v μ vTailBound μ-antitone

  sum-raw-converges :
    SeqConv.ConvergesTo
      (SeqAlg.addSequence (partialSumSequence u) (partialSumSequence v))
      (seriesSumFromFiniteTailBound u μ uTailBound μ-antitone +ᶜ
       seriesSumFromFiniteTailBound v μ vTailBound μ-antitone)
  sum-raw-converges =
    SeqAlg.addConvergesTo u-converges v-converges

  sum-align :
    SeqOrder.EventuallyWith
      (fst sum-raw-converges)
      (λ _ n →
        SeqAlg.addSequence (partialSumSequence u) (partialSumSequence v) n ≡
        partialSumSequence (λ k → u k +ᶜ v k) n)
  sum-align ε n _ =
    sym (partialSum-add u v n)

  sum-algebra-converges :
    SeqConv.ConvergesTo
      (partialSumSequence (λ k → u k +ᶜ v k))
      (seriesSumFromFiniteTailBound u μ uTailBound μ-antitone +ᶜ
       seriesSumFromFiniteTailBound v μ vTailBound μ-antitone)
  sum-algebra-converges =
    SeqOrder.eventuallyEqualPreservesConvergesTo
      sum-raw-converges
      sum-align

  sum-series-converges :
    SeqConv.ConvergesTo
      (partialSumSequence (λ k → u k +ᶜ v k))
      (seriesSumFromFiniteTailBound
        (λ k → u k +ᶜ v k)
        μ
        sumTailBound
        μ-antitone)
  sum-series-converges =
    seriesSumFromFiniteTailBoundConvergesTo
      (λ k → u k +ᶜ v k)
      μ
      sumTailBound
      μ-antitone
