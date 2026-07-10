{-

Part of Constructive.Analysis.Reals.PowerSeries.CauchyProduct

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.CauchyProduct.PowerSeriesMajorants where

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
open import Constructive.Analysis.Reals.CauchyReals.Metric
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
    ( SeriesMajorizedBy
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
open import Constructive.Analysis.Modulus
  using
    ( AntitoneNatModulus
    ; maxModulus
    ; maxModulus-left≤
    ; maxModulus-right≤
    )

open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Internal
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Core
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Remainder
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Bounds
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.MajorantRemainder
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.MajorantProduct
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.PowerSeriesBridge

cauchyProductPowerSeriesMajorizedOnBallFromMajorants :
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ : ℚ⁺ → ℕ} →
  PowerSeriesMajorizedOnBall a ρ A ν →
  PowerSeriesMajorizedOnBall b ρ B τ →
  TailBound (sequenceCauchyProduct A B) μ →
  AntitoneNatModulus μ →
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
  AntitoneNatModulus μ →
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
  (productAntitone : AntitoneNatModulus μ) →
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
  (productAntitone : AntitoneNatModulus μ) →
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
  (productAntitone : AntitoneNatModulus μ) →
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
  (productAntitone : AntitoneNatModulus μ) →
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
  (productAntitone : AntitoneNatModulus μ) →
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
    AntitoneNatModulus τ
  rightAntitone =
    HasPowerSeriesOnBallWith.antitoneModulus rightConvergence


cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTail :
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ : ℚ⁺ → ℕ} →
  (left : PowerSeriesMajorizedOnBall a ρ A ν) →
  (right : PowerSeriesMajorizedOnBall b ρ B τ) →
  (productTail : TailBound (sequenceCauchyProduct A B) μ) →
  (productAntitone : AntitoneNatModulus μ) →
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
  AntitoneNatModulus μ →
  HasPowerSeriesOnBall (cauchyProductPowerSeries a b) ρ
cauchyProductPowerSeriesOnBallFromMajorants left right productTail productAntitone =
  majorizedOnBall→hasPowerSeriesOnBall
    (cauchyProductPowerSeriesMajorizedOnBallFromMajorants
      left
      right
      productTail
      productAntitone)
