{-

Part of Constructive.Analysis.Reals.PowerSeries.CauchyProduct

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.CauchyProduct.PowerSeriesBridge where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)

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
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (absᶜ)
open import Constructive.Analysis.Reals.Series
  using
    ( SeriesMajorizedBy
    ; TailBound
    ; comparisonTest
    ; drop
    ; partialSum
    ; partialSumSequence
    ; seriesSumFromFiniteTailBound
    ; seriesMajorizedByTerms
    ; tailSum
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
  using (majorizedOnBall→hasPowerSeriesOnBall)
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using (shiftPowerSeries)
open import Constructive.Data.PositiveRationals

open ClosenessOf RationalsMetricSpace

import Constructive.Analysis.Reals.Sequences.Algebra as SeqAlg
open import Constructive.Analysis.Modulus
  using (AntitoneNatModulus ; maxModulus)

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
