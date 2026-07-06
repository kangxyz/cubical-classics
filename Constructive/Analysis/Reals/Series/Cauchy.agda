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
import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Metric.Instances.CauchyReals
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

private
  half-mono-≤ :
    {ε δ : ℚ⁺} →
    radius ε ℚOrder.≤ radius δ →
    radius (half⁺ ε) ℚOrder.≤ radius (half⁺ δ)
  half-mono-≤ {ε = ε} {δ = δ} ε≤δ =
    ℚOrder.≤-·o
      (radius ε)
      (radius δ)
      Rational.1/2
      (ℚOrder.<Weaken≤ 0ℚ Rational.1/2 Rational.0<1/2)
      ε≤δ

partialSumsCauchyWithModulus :
  (ℕ → ℝᶜ) →
  (ℚ⁺ → ℕ) →
  Type₀
partialSumsCauchyWithModulus u μ =
  (ε δ : ℚ⁺) →
  partialSum u (μ ε) ∼[ ε +⁺ δ ] partialSum u (μ δ)


seriesCauchyApproximation :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  partialSumsCauchyWithModulus u μ →
  MetricCauchy.CauchyApproximation CauchyRealsMetricSpace
seriesCauchyApproximation u μ u-cauchy =
  MetricCauchy.cauchy-approximation
    (λ ε → partialSum u (μ ε))
    u-cauchy


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
    AntitoneTailModulus μ →
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


seriesTailBound→partialSumsCauchy :
  {u : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
  SeriesTailBound u μ →
  partialSumsCauchyWithModulus u μ
seriesTailBound→partialSumsCauchy {u = u} {μ = μ} tailBound ε δ =
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
  seriesCauchyApproximation
    u
    μ
    (seriesTailBound→partialSumsCauchy {u = u} {μ = μ} tailBound)


seriesCauchyApproximationFromFiniteTailBound :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  TailBound u μ →
  AntitoneTailModulus μ →
  MetricCauchy.CauchyApproximation CauchyRealsMetricSpace
seriesCauchyApproximationFromFiniteTailBound u μ tailBound μ-antitone =
  seriesCauchyApproximationFromTailBound
    u
    (λ ε → μ (half⁺ ε))
    (tailBound→SeriesTailBound {u = u} {μ = μ} tailBound μ-antitone)


seriesLimit :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : SeriesTailBound u μ) →
  MetricCauchy.CauchyLimit
    (seriesCauchyApproximationFromTailBound u μ tailBound)
seriesLimit u μ tailBound =
  CauchyRealsIsCauchyComplete
    (seriesCauchyApproximationFromTailBound u μ tailBound)


seriesSum :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  SeriesTailBound u μ →
  ℝᶜ
seriesSum u μ tailBound =
  MetricCauchy.limitPoint (seriesLimit u μ tailBound)


seriesSumFromFiniteTailBound :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  TailBound u μ →
  AntitoneTailModulus μ →
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
  MetricCauchy.converges (seriesLimit u μ tailBound)


seriesSumFromFiniteTailBoundConverges :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : TailBound u μ) →
  (μ-antitone : AntitoneTailModulus μ) →
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
  (μ-antitone : AntitoneTailModulus μ) →
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


seriesSumFromFiniteTailBound-mul-left-convergesAt :
  (a : ℝᶜ) →
  (κ : ℚ⁺) →
  (a-bound : BoundedByᶜ κ a) →
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : TailBound u μ) →
  (μ-antitone : AntitoneTailModulus μ) →
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
  snd cont ε series-close
  where
  cont =
    mulᶜ-continuous-right-with-bound κ a a-bound

  θ : ℚ⁺
  θ =
    fst cont ε

  series-close :
    seriesSumFromFiniteTailBound u μ tailBound μ-antitone ∼[ θ ]
    partialSum u n
  series-close =
    seriesSumFromFiniteTailBoundConvergesAt
      u
      μ
      tailBound
      μ-antitone
      θ
      n
      μθ≤n


seriesSumFromFiniteTailBound-drop :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : TailBound u μ) →
  (μ-antitone : AntitoneTailModulus μ) →
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
  AntitoneTailModulus μ →
  SeriesTailBound u (λ ε → μ (half⁺ ε))
absoluteSummable→SeriesTailBound absTail μ-antitone =
  tailBound→SeriesTailBound
    (absoluteSummable→tailBound absTail)
    μ-antitone


absoluteSummable→seriesSum :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  AbsolutelySummableWith u μ →
  AntitoneTailModulus μ →
  ℝᶜ
absoluteSummable→seriesSum u μ absTail μ-antitone =
  seriesSumFromFiniteTailBound
    u
    μ
    (absoluteSummable→tailBound absTail)
    μ-antitone


cauchyLimit-unique :
  {x : MetricCauchy.CauchyApproximation CauchyRealsMetricSpace} →
  {a b : ℝᶜ} →
  MetricCauchy.ConvergesTo x a →
  MetricCauchy.ConvergesTo x b →
  a ≡ b
cauchyLimit-unique {x = x} {a = a} {b = b} a-conv b-conv =
  MetricSpace.close-separated CauchyRealsMetricSpace a b closeAt
  where
  closeAt :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace a ε b
  closeAt ε =
    subst
      (λ ρ → MetricSpace.Close CauchyRealsMetricSpace a ρ b)
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        (a-conv (half⁺ ε) (quarter⁺ ε) (half< (half⁺ ε)))
        (MetricSpace.close-sym
          CauchyRealsMetricSpace
          (b-conv (half⁺ ε) (quarter⁺ ε) (half< (half⁺ ε)))))


seriesSum-unique :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : SeriesTailBound u μ) →
  (x : ℝᶜ) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromTailBound u μ tailBound)
    x →
  x ≡ seriesSum u μ tailBound
seriesSum-unique u μ tailBound x x-conv =
  cauchyLimit-unique
    {x = seriesCauchyApproximationFromTailBound u μ tailBound}
    {a = x}
    {b = seriesSum u μ tailBound}
    x-conv
    (seriesSumConverges u μ tailBound)


seriesSum-neg :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : SeriesTailBound u μ) →
  (negTailBound : SeriesTailBound (λ n → -ᶜ u n) μ) →
  seriesSum (λ n → -ᶜ u n) μ negTailBound ≡
  -ᶜ seriesSum u μ tailBound
seriesSum-neg u μ tailBound negTailBound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    negLimit
    (-ᶜ limitPoint)
    closeAt
  where
  limitPoint : ℝᶜ
  limitPoint =
    seriesSum u μ tailBound

  negLimit : ℝᶜ
  negLimit =
    seriesSum (λ n → -ᶜ u n) μ negTailBound

  closeAt :
    (ε : ℚ⁺) →
    negLimit ∼[ ε ] (-ᶜ limitPoint)
  closeAt ε =
    subst
      (λ ρ → negLimit ∼[ ρ ] (-ᶜ limitPoint))
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        negConverges
        (MetricSpace.close-sym CauchyRealsMetricSpace limitConverges))
    where
    η : ℚ⁺
    η =
      half⁺ ε

    θ : ℚ⁺
    θ =
      quarter⁺ ε

    θ<η : θ <⁺ η
    θ<η =
      half< η

    n : ℕ
    n =
      μ θ

    negConverges :
      negLimit ∼[ η ] (-ᶜ partialSum u n)
    negConverges =
      subst
        (λ z → negLimit ∼[ η ] z)
        (partialSum-neg u n)
        (seriesSumConverges
          (λ k → -ᶜ u k)
          μ
          negTailBound
          η
          θ
          θ<η)

    limitConverges :
      (-ᶜ limitPoint) ∼[ η ] (-ᶜ partialSum u n)
    limitConverges =
      neg-close
        (seriesSumConverges
          u
          μ
          tailBound
          η
          θ
          θ<η)


seriesSum-add :
  (u v : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (uTailBound : SeriesTailBound u μ) →
  (vTailBound : SeriesTailBound v μ) →
  (sumTailBound : SeriesTailBound (λ n → u n +ᶜ v n) μ) →
  seriesSum (λ n → u n +ᶜ v n) μ sumTailBound ≡
  seriesSum u μ uTailBound +ᶜ seriesSum v μ vTailBound
seriesSum-add u v μ uTailBound vTailBound sumTailBound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    sumLimit
    (uLimit +ᶜ vLimit)
    closeAt
  where
  uLimit : ℝᶜ
  uLimit =
    seriesSum u μ uTailBound

  vLimit : ℝᶜ
  vLimit =
    seriesSum v μ vTailBound

  sumLimit : ℝᶜ
  sumLimit =
    seriesSum (λ n → u n +ᶜ v n) μ sumTailBound

  closeAt :
    (ε : ℚ⁺) →
    sumLimit ∼[ ε ] (uLimit +ᶜ vLimit)
  closeAt ε =
    MetricSpace.close-mono
      CauchyRealsMetricSpace
      (three-quarter< ε)
      (subst
        (λ ρ → sumLimit ∼[ ρ ] (uLimit +ᶜ vLimit))
        (sym (+⁺-assoc η η η))
        closeThreeQuarters)
    where
    η : ℚ⁺
    η =
      quarter⁺ ε

    θ : ℚ⁺
    θ =
      quarter⁺ η

    θ<η : θ <⁺ η
    θ<η =
      quarter< η

    n : ℕ
    n =
      μ θ

    sumConverges :
      sumLimit ∼[ η ] partialSum (λ k → u k +ᶜ v k) n
    sumConverges =
      seriesSumConverges
        (λ k → u k +ᶜ v k)
        μ
        sumTailBound
        η
        θ
        θ<η

    sumConvergesAdd :
      sumLimit ∼[ η ] (partialSum u n +ᶜ partialSum v n)
    sumConvergesAdd =
      subst
        (λ z → sumLimit ∼[ η ] z)
        (partialSum-add u v n)
        sumConverges

    uConverges :
      uLimit ∼[ η ] partialSum u n
    uConverges =
      seriesSumConverges u μ uTailBound η θ θ<η

    vConverges :
      vLimit ∼[ η ] partialSum v n
    vConverges =
      seriesSumConverges v μ vTailBound η θ θ<η

    addConverges :
      uLimit +ᶜ vLimit ∼[ η +⁺ η ]
      partialSum u n +ᶜ partialSum v n
    addConverges =
      add-close uConverges vConverges

    closeThreeQuarters :
      sumLimit ∼[ η +⁺ (η +⁺ η) ] (uLimit +ᶜ vLimit)
    closeThreeQuarters =
      MetricSpace.close-triangle
        CauchyRealsMetricSpace
        sumConvergesAdd
        (MetricSpace.close-sym CauchyRealsMetricSpace addConverges)


seriesSumFromFiniteTailBound-neg :
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : TailBound u μ) →
  (μ-antitone : AntitoneTailModulus μ) →
  seriesSumFromFiniteTailBound
    (λ n → -ᶜ u n)
    μ
    (tailBound-neg tailBound)
    μ-antitone ≡
  -ᶜ seriesSumFromFiniteTailBound u μ tailBound μ-antitone
seriesSumFromFiniteTailBound-neg u μ tailBound μ-antitone =
  seriesSum-neg
    u
    (λ ε → μ (half⁺ ε))
    (tailBound→SeriesTailBound {u = u} {μ = μ} tailBound μ-antitone)
    (tailBound→SeriesTailBound
      {u = λ n → -ᶜ u n}
      {μ = μ}
      (tailBound-neg tailBound)
      μ-antitone)


seriesSumFromFiniteTailBound-add :
  (u v : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (uTailBound : TailBound u μ) →
  (vTailBound : TailBound v μ) →
  (sumTailBound : TailBound (λ n → u n +ᶜ v n) μ) →
  (μ-antitone : AntitoneTailModulus μ) →
  seriesSumFromFiniteTailBound
    (λ n → u n +ᶜ v n)
    μ
    sumTailBound
    μ-antitone ≡
  seriesSumFromFiniteTailBound u μ uTailBound μ-antitone +ᶜ
  seriesSumFromFiniteTailBound v μ vTailBound μ-antitone
seriesSumFromFiniteTailBound-add u v μ uTailBound vTailBound sumTailBound μ-antitone =
  seriesSum-add
    u
    v
    (λ ε → μ (half⁺ ε))
    (tailBound→SeriesTailBound {u = u} {μ = μ} uTailBound μ-antitone)
    (tailBound→SeriesTailBound {u = v} {μ = μ} vTailBound μ-antitone)
    (tailBound→SeriesTailBound
      {u = λ n → u n +ᶜ v n}
      {μ = μ}
      sumTailBound
      μ-antitone)
