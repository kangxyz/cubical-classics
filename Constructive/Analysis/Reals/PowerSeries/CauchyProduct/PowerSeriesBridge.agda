{-

Part of Constructive.Analysis.Reals.PowerSeries.CauchyProduct

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.CauchyProduct.PowerSeriesBridge where

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

open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Internal
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Core
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Remainder
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Bounds
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.MajorantRemainder
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.MajorantProduct

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
