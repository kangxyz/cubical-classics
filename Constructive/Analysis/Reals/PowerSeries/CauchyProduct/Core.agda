{-

Part of Constructive.Analysis.Reals.PowerSeries.CauchyProduct

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Core where

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
