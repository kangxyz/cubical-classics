{-

Untruncated approximate IVT transfer from finite sampled grids

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.IVT.Approximate where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; _×_ ; Σ≡Prop)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
  using (≤ℚ→rational≤ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.Interval
open import Constructive.Analysis.Reals.Interval.Grid
open import Constructive.Analysis.Reals.Interval.Grid.Affine
open import Constructive.Analysis.Reals.Interval.Grid.Rational
open import Constructive.Analysis.Reals.IVT.Budget
  using
    ( IVTErrorBudget
    ; RationalStepIVTBudget
    ; defaultIVTErrorBudget
    ; defaultRationalStepIVTBudget
    )
open import Constructive.Analysis.Reals.IVT.Endpoint
open import Constructive.Analysis.Reals.IVT.GridSearch
open import Constructive.Analysis.Reals.IVT.Sampling
open import Constructive.Analysis.Reals.IVT.Uniform
open import Constructive.Analysis.Reals.Locator.Base using (Locator)
open import Constructive.Analysis.Reals.Locator.Map
  using (ApproxEvaluable ; LocatedMap)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


approximate-IVTΣ-grid :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (samplePrecision movementPrecision boundPrecision targetPrecision : ℚ⁺) →
  samplePrecision <⁺ boundPrecision →
  (((samplePrecision +⁺ movementPrecision) +⁺ samplePrecision) +⁺ boundPrecision)
    <⁺ targetPrecision →
  AdjacentClose G
    (uniformModulus {a = a} {b = b} {f = f}
      (IVTFunctionData.uniformlyContinuous ivtData)
      movementPrecision) →
  gridSampleValues ivtData G samplePrecision Fin.zero ℚOrder.< 0ℚ →
  0ℚ ℚOrder.≤ gridSampleValues ivtData G samplePrecision (Fin.fromℕ (suc n)) →
  Σ[ x ∈ [ a , b ]ᶜ ] absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-grid {a = a} {b = b} {a≤b = a≤b} f ivtData {n = n}
    G samplePrecision movementPrecision boundPrecision targetPrecision
    sample<bound small+bound<target adjacentClose first<0 0≤last =
  Grid.point G nearIndex ,
  sampleNonnegativeSmallAbs<
    ivtData
    G
    samplePrecision
    boundPrecision
    smallPrecision
    targetPrecision
    sample<bound
    small+bound<target
    nearIndex
    nearSmall
  where
  smallPrecision : ℚ⁺
  smallPrecision =
    (samplePrecision +⁺ movementPrecision) +⁺ samplePrecision

  near :
    Σ[ i ∈ Fin (suc (suc n)) ]
      NonnegativeSmall
        (gridSampleValues ivtData G samplePrecision)
        smallPrecision
        i
  near =
    gridNearZeroRight
      n
      (gridSampleValues ivtData G samplePrecision)
      smallPrecision
      (adjacentSampleValuesClose
        ivtData
        G
        samplePrecision
        movementPrecision
        adjacentClose)
      first<0
      0≤last

  nearIndex : Fin (suc (suc n))
  nearIndex =
    near .fst

  nearSmall :
    NonnegativeSmall
      (gridSampleValues ivtData G samplePrecision)
      smallPrecision
      nearIndex
  nearSmall =
    near .snd


approximate-IVTΣ-grid-margins :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (samplePrecision movementPrecision boundPrecision targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  samplePrecision <⁺ boundPrecision →
  boundPrecision <⁺ leftMargin →
  boundPrecision <⁺ rightMargin →
  (((samplePrecision +⁺ movementPrecision) +⁺ samplePrecision) +⁺ boundPrecision)
    <⁺ targetPrecision →
  AdjacentClose G
    (uniformModulus {a = a} {b = b} {f = f}
      (IVTFunctionData.uniformlyContinuous ivtData)
      movementPrecision) →
  NegativeMarginᶜ
    leftMargin
    (f (leftEndpoint {a = a} {b = b} a≤b)) →
  PositiveMarginᶜ
    rightMargin
    (f (rightEndpoint {a = a} {b = b} a≤b)) →
  Σ[ x ∈ [ a , b ]ᶜ ] absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-grid-margins {a = a} {b = b} {a≤b = a≤b} f ivtData
    {n = n} G samplePrecision movementPrecision boundPrecision targetPrecision
    leftMargin rightMargin sample<bound bound<left bound<right small+bound<target
    adjacentClose leftNegative rightPositive =
  approximate-IVTΣ-grid
    f
    ivtData
    G
    samplePrecision
    movementPrecision
    boundPrecision
    targetPrecision
    sample<bound
    small+bound<target
    adjacentClose
    (leftEndpointSampleNegative
      ivtData
      G
      samplePrecision
      boundPrecision
      leftMargin
      sample<bound
      bound<left
      leftNegative)
    (rightEndpointSampleNonnegative
      ivtData
      G
      samplePrecision
      boundPrecision
      rightMargin
      sample<bound
      bound<right
      rightPositive)


approximate-IVTΣ-grid-located-margins :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (samplePrecision movementPrecision boundPrecision targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  samplePrecision <⁺ boundPrecision →
  boundPrecision <⁺ leftMargin →
  boundPrecision <⁺ rightMargin →
  (((samplePrecision +⁺ movementPrecision) +⁺ samplePrecision) +⁺ boundPrecision)
    <⁺ targetPrecision →
  AdjacentClose G
    (uniformModulus {a = a} {b = b} {f = f}
      uc
      movementPrecision) →
  NegativeMarginᶜ
    leftMargin
    (f (leftEndpoint {a = a} {b = b} a≤b)) →
  PositiveMarginᶜ
    rightMargin
    (f (rightEndpoint {a = a} {b = b} a≤b)) →
  Σ[ x ∈ [ a , b ]ᶜ ] absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-grid-located-margins f located uc G samplePrecision
    movementPrecision boundPrecision targetPrecision leftMargin rightMargin =
  approximate-IVTΣ-grid-margins
    f
    (locatedIVTFunctionData located uc)
    G
    samplePrecision
    movementPrecision
    boundPrecision
    targetPrecision
    leftMargin
    rightMargin


approximate-IVTΣ-grid-budget :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  (budget : IVTErrorBudget leftMargin rightMargin targetPrecision) →
  AdjacentClose G
    (uniformModulus {a = a} {b = b} {f = f}
      (IVTFunctionData.uniformlyContinuous ivtData)
      (IVTErrorBudget.movementPrecision budget)) →
  NegativeMarginᶜ
    leftMargin
    (f (leftEndpoint {a = a} {b = b} a≤b)) →
  PositiveMarginᶜ
    rightMargin
    (f (rightEndpoint {a = a} {b = b} a≤b)) →
  Σ[ x ∈ [ a , b ]ᶜ ] absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-grid-budget f ivtData G targetPrecision
    leftMargin rightMargin budget =
  approximate-IVTΣ-grid-margins
    f
    ivtData
    G
    sample
    movement
    bound
    targetPrecision
    leftMargin
    rightMargin
    (IVTErrorBudget.sample<bound budget)
    (IVTErrorBudget.bound<left budget)
    (IVTErrorBudget.bound<right budget)
    (IVTErrorBudget.small+bound<target budget)
  where
  sample movement bound : ℚ⁺
  sample =
    IVTErrorBudget.samplePrecision budget
  movement =
    IVTErrorBudget.movementPrecision budget
  bound =
    IVTErrorBudget.boundPrecision budget


approximate-IVTΣ-grid-located-budget :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  (budget : IVTErrorBudget leftMargin rightMargin targetPrecision) →
  AdjacentClose G
    (uniformModulus {a = a} {b = b} {f = f}
      uc
      (IVTErrorBudget.movementPrecision budget)) →
  NegativeMarginᶜ
    leftMargin
    (f (leftEndpoint {a = a} {b = b} a≤b)) →
  PositiveMarginᶜ
    rightMargin
    (f (rightEndpoint {a = a} {b = b} a≤b)) →
  Σ[ x ∈ [ a , b ]ᶜ ] absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-grid-located-budget f located uc =
  approximate-IVTΣ-grid-budget
    f
    (locatedIVTFunctionData located uc)


approximate-IVTΣ-grid-default-budget :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  AdjacentClose G
    (uniformModulus {a = a} {b = b} {f = f}
      (IVTFunctionData.uniformlyContinuous ivtData)
      (IVTErrorBudget.movementPrecision
        (defaultIVTErrorBudget leftMargin rightMargin targetPrecision))) →
  NegativeMarginᶜ
    leftMargin
    (f (leftEndpoint {a = a} {b = b} a≤b)) →
  PositiveMarginᶜ
    rightMargin
    (f (rightEndpoint {a = a} {b = b} a≤b)) →
  Σ[ x ∈ [ a , b ]ᶜ ] absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-grid-default-budget f ivtData G targetPrecision
    leftMargin rightMargin =
  approximate-IVTΣ-grid-budget
    f
    ivtData
    G
    targetPrecision
    leftMargin
    rightMargin
    (defaultIVTErrorBudget leftMargin rightMargin targetPrecision)


approximate-IVTΣ-grid-located-default-budget :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  AdjacentClose G
    (uniformModulus {a = a} {b = b} {f = f}
      uc
      (IVTErrorBudget.movementPrecision
        (defaultIVTErrorBudget leftMargin rightMargin targetPrecision))) →
  NegativeMarginᶜ
    leftMargin
    (f (leftEndpoint {a = a} {b = b} a≤b)) →
  PositiveMarginᶜ
    rightMargin
    (f (rightEndpoint {a = a} {b = b} a≤b)) →
  Σ[ x ∈ [ a , b ]ᶜ ] absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-grid-located-default-budget f located uc =
  approximate-IVTΣ-grid-default-budget
    f
    (locatedIVTFunctionData located uc)


approximate-IVT∥∥-grid-strict :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (targetPrecision : ℚ⁺) →
  (budgetAt :
    (leftMargin rightMargin : ℚ⁺) →
    IVTErrorBudget leftMargin rightMargin targetPrecision) →
  ((leftMargin rightMargin : ℚ⁺) →
    AdjacentClose G
      (uniformModulus {a = a} {b = b} {f = f}
        (IVTFunctionData.uniformlyContinuous ivtData)
        (IVTErrorBudget.movementPrecision
          (budgetAt leftMargin rightMargin)))) →
  f (leftEndpoint {a = a} {b = b} a≤b) <ᶜ 0ᶜ →
  0ᶜ <ᶜ f (rightEndpoint {a = a} {b = b} a≤b) →
  ∥ Σ[ x ∈ [ a , b ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
approximate-IVT∥∥-grid-strict {a = a} {b = b} {a≤b = a≤b}
    f ivtData G targetPrecision budgetAt adjacentAt leftNegative rightPositive =
  Prop.rec2 squash₁ combine leftMargins rightMargins
  where
  leftEndpointᶜ : [ a , b ]ᶜ
  leftEndpointᶜ =
    leftEndpoint {a = a} {b = b} a≤b

  rightEndpointᶜ : [ a , b ]ᶜ
  rightEndpointᶜ =
    rightEndpoint {a = a} {b = b} a≤b

  leftMargins :
    ∥ Σ[ margin ∈ ℚ⁺ ] NegativeMarginᶜ margin (f leftEndpointᶜ) ∥₁
  leftMargins =
    negativeStrictMargins (f leftEndpointᶜ) leftNegative

  rightMargins :
    ∥ Σ[ margin ∈ ℚ⁺ ] PositiveMarginᶜ margin (f rightEndpointᶜ) ∥₁
  rightMargins =
    positiveStrictMargins (f rightEndpointᶜ) rightPositive

  combine :
    Σ[ leftMargin ∈ ℚ⁺ ] NegativeMarginᶜ leftMargin (f leftEndpointᶜ) →
    Σ[ rightMargin ∈ ℚ⁺ ] PositiveMarginᶜ rightMargin (f rightEndpointᶜ) →
    ∥ Σ[ x ∈ [ a , b ]ᶜ ]
        absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
  combine (leftMargin , leftMarginData) (rightMargin , rightMarginData) =
    ∣ approximate-IVTΣ-grid-budget
        f
        ivtData
        G
        targetPrecision
        leftMargin
        rightMargin
        (budgetAt leftMargin rightMargin)
        (adjacentAt leftMargin rightMargin)
        leftMarginData
        rightMarginData
    ∣₁


approximate-IVT∥∥-grid-located-strict :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (targetPrecision : ℚ⁺) →
  (budgetAt :
    (leftMargin rightMargin : ℚ⁺) →
    IVTErrorBudget leftMargin rightMargin targetPrecision) →
  ((leftMargin rightMargin : ℚ⁺) →
    AdjacentClose G
      (uniformModulus {a = a} {b = b} {f = f}
        uc
        (IVTErrorBudget.movementPrecision
          (budgetAt leftMargin rightMargin)))) →
  f (leftEndpoint {a = a} {b = b} a≤b) <ᶜ 0ᶜ →
  0ᶜ <ᶜ f (rightEndpoint {a = a} {b = b} a≤b) →
  ∥ Σ[ x ∈ [ a , b ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
approximate-IVT∥∥-grid-located-strict f located uc =
  approximate-IVT∥∥-grid-strict
    f
    (locatedIVTFunctionData located uc)


approximate-IVTΣ-grid-located-strict :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (targetPrecision : ℚ⁺) →
  (budgetAt :
    (leftMargin rightMargin : ℚ⁺) →
    IVTErrorBudget leftMargin rightMargin targetPrecision) →
  ((leftMargin rightMargin : ℚ⁺) →
    AdjacentClose G
      (uniformModulus {a = a} {b = b} {f = f}
        uc
        (IVTErrorBudget.movementPrecision
          (budgetAt leftMargin rightMargin)))) →
  f (leftEndpoint {a = a} {b = b} a≤b) <ᶜ 0ᶜ →
  0ᶜ <ᶜ f (rightEndpoint {a = a} {b = b} a≤b) →
  Σ[ x ∈ [ a , b ]ᶜ ] absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-grid-located-strict {a = a} {b = b} {a≤b = a≤b}
    f located uc G targetPrecision budgetAt adjacentAt leftNegative rightPositive =
  approximate-IVTΣ-grid-budget
    f
    (locatedIVTFunctionData located uc)
    G
    targetPrecision
    leftMargin
    rightMargin
    (budgetAt leftMargin rightMargin)
    (adjacentAt leftMargin rightMargin)
    leftMarginData
    rightMarginData
  where
  leftEndpointᶜ : [ a , b ]ᶜ
  leftEndpointᶜ =
    leftEndpoint {a = a} {b = b} a≤b

  rightEndpointᶜ : [ a , b ]ᶜ
  rightEndpointᶜ =
    rightEndpoint {a = a} {b = b} a≤b

  signData : SignData (f leftEndpointᶜ) (f rightEndpointᶜ)
  signData =
    locatedStrictSignData
      (f leftEndpointᶜ)
      (f rightEndpointᶜ)
      (LocatedMap.locatorAt located leftEndpointᶜ)
      (LocatedMap.locatorAt located rightEndpointᶜ)
      leftNegative
      rightPositive

  leftMargin : ℚ⁺
  leftMargin =
    signData .fst .fst

  rightMargin : ℚ⁺
  rightMargin =
    signData .snd .fst

  leftMarginData :
    NegativeMarginᶜ leftMargin (f leftEndpointᶜ)
  leftMarginData =
    signData .fst .snd

  rightMarginData :
    PositiveMarginᶜ rightMargin (f rightEndpointᶜ)
  rightMarginData =
    signData .snd .snd


approximate-IVTΣ-with-gap-bound :
  {a b : ℝᶜ} →
  (a≤b : a ≤ᶜ b) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (gapᶜ a b) →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  IVTFunctionData a b f →
  Locator (f (leftEndpoint {a = a} {b = b} a≤b)) →
  Locator (f (rightEndpoint {a = a} {b = b} a≤b)) →
  (targetPrecision : ℚ⁺) →
  f (leftEndpoint {a = a} {b = b} a≤b) <ᶜ 0ᶜ →
  0ᶜ <ᶜ f (rightEndpoint {a = a} {b = b} a≤b) →
  Σ[ x ∈ [ a , b ]ᶜ ] absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-with-gap-bound {a = a} {b = b}
    a≤b κ gap-bound f ivtData loc-left loc-right targetPrecision
    leftNegative rightPositive =
  approximate-IVTΣ-grid-budget
    f
    ivtData
    G
    targetPrecision
    leftMargin
    rightMargin
    budget
    adjacent
    leftMarginData
    rightMarginData
  where
  leftEndpointᶜ : [ a , b ]ᶜ
  leftEndpointᶜ =
    leftEndpoint {a = a} {b = b} a≤b

  rightEndpointᶜ : [ a , b ]ᶜ
  rightEndpointᶜ =
    rightEndpoint {a = a} {b = b} a≤b

  signData : SignData (f leftEndpointᶜ) (f rightEndpointᶜ)
  signData =
    locatedStrictSignData
      (f leftEndpointᶜ)
      (f rightEndpointᶜ)
      loc-left
      loc-right
      leftNegative
      rightPositive

  leftMargin : ℚ⁺
  leftMargin =
    signData .fst .fst

  rightMargin : ℚ⁺
  rightMargin =
    signData .snd .fst

  leftMarginData :
    NegativeMarginᶜ leftMargin (f leftEndpointᶜ)
  leftMarginData =
    signData .fst .snd

  rightMarginData :
    PositiveMarginᶜ rightMargin (f rightEndpointᶜ)
  rightMarginData =
    signData .snd .snd

  budget : IVTErrorBudget leftMargin rightMargin targetPrecision
  budget =
    defaultIVTErrorBudget leftMargin rightMargin targetPrecision

  mesh : ℚ⁺
  mesh =
    uniformModulus {a = a} {b = b} {f = f}
      (IVTFunctionData.uniformlyContinuous ivtData)
      (IVTErrorBudget.movementPrecision budget)

  gridData :
    Σ[ n ∈ ℕ ]
      Σ[ G ∈ Grid a b a≤b (suc n) ]
        AdjacentClose G mesh
  gridData =
    locatedAffineGridData a b a≤b κ gap-bound mesh

  n : ℕ
  n =
    gridData .fst

  G : Grid a b a≤b (suc n)
  G =
    gridData .snd .fst

  adjacent : AdjacentClose G mesh
  adjacent =
    gridData .snd .snd


approximate-IVTΣ-located-with-gap-bound :
  {a b : ℝᶜ} →
  (a≤b : a ≤ᶜ b) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (gapᶜ a b) →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval a b f) →
  (targetPrecision : ℚ⁺) →
  f (leftEndpoint {a = a} {b = b} a≤b) <ᶜ 0ᶜ →
  0ᶜ <ᶜ f (rightEndpoint {a = a} {b = b} a≤b) →
  Σ[ x ∈ [ a , b ]ᶜ ] absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-located-with-gap-bound {a = a} {b = b}
    a≤b κ gap-bound f located uc =
  approximate-IVTΣ-with-gap-bound
    a≤b
    κ
    gap-bound
    f
    (locatedIVTFunctionData located uc)
    (LocatedMap.locatorAt located (leftEndpoint {a = a} {b = b} a≤b))
    (LocatedMap.locatorAt located (rightEndpoint {a = a} {b = b} a≤b))


approximate-IVTΣ :
  {a b : ℝᶜ} →
  Locator a →
  Locator b →
  (a≤b : a ≤ᶜ b) →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  IVTFunctionData a b f →
  Locator (f (leftEndpoint {a = a} {b = b} a≤b)) →
  Locator (f (rightEndpoint {a = a} {b = b} a≤b)) →
  (targetPrecision : ℚ⁺) →
  f (leftEndpoint {a = a} {b = b} a≤b) <ᶜ 0ᶜ →
  0ᶜ <ᶜ f (rightEndpoint {a = a} {b = b} a≤b) →
  Σ[ x ∈ [ a , b ]ᶜ ] absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ {a = a} {b = b}
    loc-a loc-b a≤b f ivtData loc-left loc-right targetPrecision
    leftNegative rightPositive =
  approximate-IVTΣ-with-gap-bound
    a≤b
    (gapData .fst)
    (gapData .snd)
    f
    ivtData
    loc-left
    loc-right
    targetPrecision
    leftNegative
    rightPositive
  where
  gapData : Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ (gapᶜ a b)
  gapData =
    locatedGapBound a b loc-a loc-b


approximate-IVTΣ-located :
  {a b : ℝᶜ} →
  Locator a →
  Locator b →
  (a≤b : a ≤ᶜ b) →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval a b f) →
  (targetPrecision : ℚ⁺) →
  f (leftEndpoint {a = a} {b = b} a≤b) <ᶜ 0ᶜ →
  0ᶜ <ᶜ f (rightEndpoint {a = a} {b = b} a≤b) →
  Σ[ x ∈ [ a , b ]ᶜ ] absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-located {a = a} {b = b}
    loc-a loc-b a≤b f located uc targetPrecision leftNegative rightPositive =
  approximate-IVTΣ
    loc-a
    loc-b
    a≤b
    f
    (locatedIVTFunctionData located uc)
    (LocatedMap.locatorAt located (leftEndpoint {a = a} {b = b} a≤b))
    (LocatedMap.locatorAt located (rightEndpoint {a = a} {b = b} a≤b))
    targetPrecision
    leftNegative
    rightPositive


approximate-IVT∥∥ :
  {a b : ℝᶜ} →
  Locator a →
  Locator b →
  (a≤b : a ≤ᶜ b) →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  IVTFunctionData a b f →
  Locator (f (leftEndpoint {a = a} {b = b} a≤b)) →
  Locator (f (rightEndpoint {a = a} {b = b} a≤b)) →
  (targetPrecision : ℚ⁺) →
  f (leftEndpoint {a = a} {b = b} a≤b) <ᶜ 0ᶜ →
  0ᶜ <ᶜ f (rightEndpoint {a = a} {b = b} a≤b) →
  ∥ Σ[ x ∈ [ a , b ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
approximate-IVT∥∥
    loc-a loc-b a≤b f ivtData loc-left loc-right targetPrecision
    leftNegative rightPositive =
  ∣ approximate-IVTΣ
      loc-a
      loc-b
      a≤b
      f
      ivtData
      loc-left
      loc-right
      targetPrecision
      leftNegative
      rightPositive ∣₁


approximate-IVT∥∥-located :
  {a b : ℝᶜ} →
  Locator a →
  Locator b →
  (a≤b : a ≤ᶜ b) →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval a b f) →
  (targetPrecision : ℚ⁺) →
  f (leftEndpoint {a = a} {b = b} a≤b) <ᶜ 0ᶜ →
  0ᶜ <ᶜ f (rightEndpoint {a = a} {b = b} a≤b) →
  ∥ Σ[ x ∈ [ a , b ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
approximate-IVT∥∥-located {a = a} {b = b}
    loc-a loc-b a≤b f located uc =
  approximate-IVT∥∥
    loc-a
    loc-b
    a≤b
    f
    (locatedIVTFunctionData located uc)
    (LocatedMap.locatorAt located (leftEndpoint {a = a} {b = b} a≤b))
    (LocatedMap.locatorAt located (rightEndpoint {a = a} {b = b} a≤b))


approximate-IVT∥∥-grid-strict-default-budget :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (targetPrecision : ℚ⁺) →
  ((leftMargin rightMargin : ℚ⁺) →
    AdjacentClose G
      (uniformModulus {a = a} {b = b} {f = f}
        (IVTFunctionData.uniformlyContinuous ivtData)
        (IVTErrorBudget.movementPrecision
          (defaultIVTErrorBudget leftMargin rightMargin targetPrecision)))) →
  f (leftEndpoint {a = a} {b = b} a≤b) <ᶜ 0ᶜ →
  0ᶜ <ᶜ f (rightEndpoint {a = a} {b = b} a≤b) →
  ∥ Σ[ x ∈ [ a , b ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
approximate-IVT∥∥-grid-strict-default-budget f ivtData G targetPrecision =
  approximate-IVT∥∥-grid-strict
    f
    ivtData
    G
    targetPrecision
    (λ leftMargin rightMargin →
      defaultIVTErrorBudget leftMargin rightMargin targetPrecision)


approximate-IVT∥∥-grid-located-strict-default-budget :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (targetPrecision : ℚ⁺) →
  ((leftMargin rightMargin : ℚ⁺) →
    AdjacentClose G
      (uniformModulus {a = a} {b = b} {f = f}
        uc
        (IVTErrorBudget.movementPrecision
          (defaultIVTErrorBudget leftMargin rightMargin targetPrecision)))) →
  f (leftEndpoint {a = a} {b = b} a≤b) <ᶜ 0ᶜ →
  0ᶜ <ᶜ f (rightEndpoint {a = a} {b = b} a≤b) →
  ∥ Σ[ x ∈ [ a , b ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
approximate-IVT∥∥-grid-located-strict-default-budget f located uc =
  approximate-IVT∥∥-grid-strict-default-budget
    f
    (locatedIVTFunctionData located uc)


approximate-IVTΣ-rational-step-margins :
  (a : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (f :
    [ rational a ,
      rational (Rational.grid a (radius step) (suc n)) ]ᶜ →
    ℝᶜ) →
  (ivtData :
    IVTFunctionData
      (rational a)
      (rational (Rational.grid a (radius step) (suc n)))
      f) →
  (samplePrecision movementPrecision boundPrecision targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  samplePrecision <⁺ boundPrecision →
  boundPrecision <⁺ leftMargin →
  boundPrecision <⁺ rightMargin →
  (((samplePrecision +⁺ movementPrecision) +⁺ samplePrecision) +⁺ boundPrecision)
    <⁺ targetPrecision →
  step +⁺ step <⁺
    uniformModulus
      {a = rational a}
      {b = rational (Rational.grid a (radius step) (suc n))}
      {f = f}
      (IVTFunctionData.uniformlyContinuous ivtData)
      movementPrecision →
  NegativeMarginᶜ
    leftMargin
    (f
      (leftEndpoint
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        (gridLower≤ᶜ a step (suc n)))) →
  PositiveMarginᶜ
    rightMargin
    (f
      (rightEndpoint
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        (gridLower≤ᶜ a step (suc n)))) →
  Σ[ x ∈
    [ rational a ,
      rational (Rational.grid a (radius step) (suc n)) ]ᶜ ]
    absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-rational-step-margins a step n f ivtData
    samplePrecision movementPrecision boundPrecision targetPrecision
    leftMargin rightMargin sample<bound bound<left bound<right small+bound<target
    stepClose<mod leftNegative rightPositive =
  approximate-IVTΣ-grid-margins
    f
    ivtData
    rationalGrid
    samplePrecision
    movementPrecision
    boundPrecision
    targetPrecision
    leftMargin
    rightMargin
    sample<bound
    bound<left
    bound<right
    small+bound<target
    adjacentClose
    leftNegative
    rightPositive
  where
  rationalGrid :
    Grid
      (rational a)
      (rational (Rational.grid a (radius step) (suc n)))
      (gridLower≤ᶜ a step (suc n))
      (suc n)
  rationalGrid =
    rationalStepGrid a step (suc n)

  adjacentClose :
    AdjacentClose
      rationalGrid
      (uniformModulus
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        {f = f}
        (IVTFunctionData.uniformlyContinuous ivtData)
        movementPrecision)
  adjacentClose i =
    MetricSpace.close-mono
      (IntervalMetric
        (rational a)
        (rational (Rational.grid a (radius step) (suc n))))
      {x = Grid.point rationalGrid (Fin.weakenFin i)}
      {y = Grid.point rationalGrid (Fin.suc i)}
      {ε = step +⁺ step}
      {δ =
        uniformModulus
          {a = rational a}
          {b = rational (Rational.grid a (radius step) (suc n))}
          {f = f}
          (IVTFunctionData.uniformlyContinuous ivtData)
          movementPrecision}
      stepClose<mod
      (rationalStepGridAdjacentClose a step (suc n) i)


approximate-IVTΣ-rational-step-with-right-margins :
  (a b : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid a (radius step) (suc n) ≡ b) →
  (f : [ rational a , rational b ]ᶜ → ℝᶜ) →
  (ivtData : IVTFunctionData (rational a) (rational b) f) →
  (samplePrecision movementPrecision boundPrecision targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  samplePrecision <⁺ boundPrecision →
  boundPrecision <⁺ leftMargin →
  boundPrecision <⁺ rightMargin →
  (((samplePrecision +⁺ movementPrecision) +⁺ samplePrecision) +⁺ boundPrecision)
    <⁺ targetPrecision →
  step +⁺ step <⁺
    uniformModulus
      {a = rational a}
      {b = rational b}
      {f = f}
      (IVTFunctionData.uniformlyContinuous ivtData)
      movementPrecision →
  NegativeMarginᶜ
    leftMargin
    (f
      (leftEndpoint
        {a = rational a}
        {b = rational b}
        (gridLowerWithRight≤ᶜ a b step (suc n) right-path))) →
  PositiveMarginᶜ
    rightMargin
    (f
      (rightEndpoint
        {a = rational a}
        {b = rational b}
        (gridLowerWithRight≤ᶜ a b step (suc n) right-path))) →
  Σ[ x ∈ [ rational a , rational b ]ᶜ ]
    absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-rational-step-with-right-margins a b step n right-path
    f ivtData samplePrecision movementPrecision boundPrecision targetPrecision
    leftMargin rightMargin sample<bound bound<left bound<right small+bound<target
    stepClose<mod leftNegative rightPositive =
  approximate-IVTΣ-grid-margins
    f
    ivtData
    rationalGrid
    samplePrecision
    movementPrecision
    boundPrecision
    targetPrecision
    leftMargin
    rightMargin
    sample<bound
    bound<left
    bound<right
    small+bound<target
    adjacentClose
    leftNegative
    rightPositive
  where
  a≤b : rational a ≤ᶜ rational b
  a≤b =
    gridLowerWithRight≤ᶜ a b step (suc n) right-path

  rationalGrid :
    Grid
      (rational a)
      (rational b)
      a≤b
      (suc n)
  rationalGrid =
    rationalStepGridWithRight a b step (suc n) right-path

  adjacentClose :
    AdjacentClose
      rationalGrid
      (uniformModulus
        {a = rational a}
        {b = rational b}
        {f = f}
        (IVTFunctionData.uniformlyContinuous ivtData)
        movementPrecision)
  adjacentClose i =
    MetricSpace.close-mono
      (IntervalMetric (rational a) (rational b))
      {x = Grid.point rationalGrid (Fin.weakenFin i)}
      {y = Grid.point rationalGrid (Fin.suc i)}
      {ε = step +⁺ step}
      {δ =
        uniformModulus
          {a = rational a}
          {b = rational b}
          {f = f}
          (IVTFunctionData.uniformlyContinuous ivtData)
          movementPrecision}
      stepClose<mod
      (rationalStepGridWithRightAdjacentClose a b step (suc n) right-path i)


approximate-IVTΣ-rational-step-budget :
  (a : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (f :
    [ rational a ,
      rational (Rational.grid a (radius step) (suc n)) ]ᶜ →
    ℝᶜ) →
  (ivtData :
    IVTFunctionData
      (rational a)
      (rational (Rational.grid a (radius step) (suc n)))
      f) →
  (targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  RationalStepIVTBudget
    step
    (uniformModulus
      {a = rational a}
      {b = rational (Rational.grid a (radius step) (suc n))}
      {f = f}
      (IVTFunctionData.uniformlyContinuous ivtData))
    leftMargin
    rightMargin
    targetPrecision →
  NegativeMarginᶜ
    leftMargin
    (f
      (leftEndpoint
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        (gridLower≤ᶜ a step (suc n)))) →
  PositiveMarginᶜ
    rightMargin
    (f
      (rightEndpoint
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        (gridLower≤ᶜ a step (suc n)))) →
  Σ[ x ∈
    [ rational a ,
      rational (Rational.grid a (radius step) (suc n)) ]ᶜ ]
    absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-rational-step-budget a step n f ivtData targetPrecision
    leftMargin rightMargin budget =
  approximate-IVTΣ-rational-step-margins
    a
    step
    n
    f
    ivtData
    sample
    movement
    bound
    targetPrecision
    leftMargin
    rightMargin
    (IVTErrorBudget.sample<bound errorBudget)
    (IVTErrorBudget.bound<left errorBudget)
    (IVTErrorBudget.bound<right errorBudget)
    (IVTErrorBudget.small+bound<target errorBudget)
    (RationalStepIVTBudget.stepClose<modulus budget)
  where
  errorBudget : IVTErrorBudget leftMargin rightMargin targetPrecision
  errorBudget =
    RationalStepIVTBudget.errorBudget budget

  sample movement bound : ℚ⁺
  sample =
    IVTErrorBudget.samplePrecision errorBudget
  movement =
    IVTErrorBudget.movementPrecision errorBudget
  bound =
    IVTErrorBudget.boundPrecision errorBudget


approximate-IVTΣ-rational-step-with-right-budget :
  (a b : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid a (radius step) (suc n) ≡ b) →
  (f : [ rational a , rational b ]ᶜ → ℝᶜ) →
  (ivtData : IVTFunctionData (rational a) (rational b) f) →
  (targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  RationalStepIVTBudget
    step
    (uniformModulus
      {a = rational a}
      {b = rational b}
      {f = f}
      (IVTFunctionData.uniformlyContinuous ivtData))
    leftMargin
    rightMargin
    targetPrecision →
  NegativeMarginᶜ
    leftMargin
    (f
      (leftEndpoint
        {a = rational a}
        {b = rational b}
        (gridLowerWithRight≤ᶜ a b step (suc n) right-path))) →
  PositiveMarginᶜ
    rightMargin
    (f
      (rightEndpoint
        {a = rational a}
        {b = rational b}
        (gridLowerWithRight≤ᶜ a b step (suc n) right-path))) →
  Σ[ x ∈ [ rational a , rational b ]ᶜ ]
    absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-rational-step-with-right-budget a b step n right-path
    f ivtData targetPrecision leftMargin rightMargin budget =
  approximate-IVTΣ-rational-step-with-right-margins
    a
    b
    step
    n
    right-path
    f
    ivtData
    sample
    movement
    bound
    targetPrecision
    leftMargin
    rightMargin
    (IVTErrorBudget.sample<bound errorBudget)
    (IVTErrorBudget.bound<left errorBudget)
    (IVTErrorBudget.bound<right errorBudget)
    (IVTErrorBudget.small+bound<target errorBudget)
    (RationalStepIVTBudget.stepClose<modulus budget)
  where
  errorBudget : IVTErrorBudget leftMargin rightMargin targetPrecision
  errorBudget =
    RationalStepIVTBudget.errorBudget budget

  sample movement bound : ℚ⁺
  sample =
    IVTErrorBudget.samplePrecision errorBudget
  movement =
    IVTErrorBudget.movementPrecision errorBudget
  bound =
    IVTErrorBudget.boundPrecision errorBudget


approximate-IVTΣ-rational-step-located-budget :
  (a : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (f :
    [ rational a ,
      rational (Rational.grid a (radius step) (suc n)) ]ᶜ →
    ℝᶜ) →
  (located : LocatedMap f) →
  (uc :
    UniformlyContinuousOnInterval
      (rational a)
      (rational (Rational.grid a (radius step) (suc n)))
      f) →
  (targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  RationalStepIVTBudget
    step
    (uniformModulus
      {a = rational a}
      {b = rational (Rational.grid a (radius step) (suc n))}
      {f = f}
      uc)
    leftMargin
    rightMargin
    targetPrecision →
  NegativeMarginᶜ
    leftMargin
    (f
      (leftEndpoint
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        (gridLower≤ᶜ a step (suc n)))) →
  PositiveMarginᶜ
    rightMargin
    (f
      (rightEndpoint
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        (gridLower≤ᶜ a step (suc n)))) →
  Σ[ x ∈
    [ rational a ,
      rational (Rational.grid a (radius step) (suc n)) ]ᶜ ]
    absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-rational-step-located-budget a step n f located uc =
  approximate-IVTΣ-rational-step-budget
    a
    step
    n
    f
    (locatedIVTFunctionData located uc)


approximate-IVTΣ-rational-step-with-right-located-budget :
  (a b : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid a (radius step) (suc n) ≡ b) →
  (f : [ rational a , rational b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval (rational a) (rational b) f) →
  (targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  RationalStepIVTBudget
    step
    (uniformModulus
      {a = rational a}
      {b = rational b}
      {f = f}
      uc)
    leftMargin
    rightMargin
    targetPrecision →
  NegativeMarginᶜ
    leftMargin
    (f
      (leftEndpoint
        {a = rational a}
        {b = rational b}
        (gridLowerWithRight≤ᶜ a b step (suc n) right-path))) →
  PositiveMarginᶜ
    rightMargin
    (f
      (rightEndpoint
        {a = rational a}
        {b = rational b}
        (gridLowerWithRight≤ᶜ a b step (suc n) right-path))) →
  Σ[ x ∈ [ rational a , rational b ]ᶜ ]
    absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-rational-step-with-right-located-budget a b step n right-path
    f located uc =
  approximate-IVTΣ-rational-step-with-right-budget
    a
    b
    step
    n
    right-path
    f
    (locatedIVTFunctionData located uc)


approximate-IVTΣ-rational-step-default-budget :
  (a : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (f :
    [ rational a ,
      rational (Rational.grid a (radius step) (suc n)) ]ᶜ →
    ℝᶜ) →
  (ivtData :
    IVTFunctionData
      (rational a)
      (rational (Rational.grid a (radius step) (suc n)))
      f) →
  (targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  step +⁺ step <⁺
    uniformModulus
      {a = rational a}
      {b = rational (Rational.grid a (radius step) (suc n))}
      {f = f}
      (IVTFunctionData.uniformlyContinuous ivtData)
      (IVTErrorBudget.movementPrecision
        (defaultIVTErrorBudget leftMargin rightMargin targetPrecision)) →
  NegativeMarginᶜ
    leftMargin
    (f
      (leftEndpoint
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        (gridLower≤ᶜ a step (suc n)))) →
  PositiveMarginᶜ
    rightMargin
    (f
      (rightEndpoint
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        (gridLower≤ᶜ a step (suc n)))) →
  Σ[ x ∈
    [ rational a ,
      rational (Rational.grid a (radius step) (suc n)) ]ᶜ ]
    absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-rational-step-default-budget a step n f ivtData
    targetPrecision leftMargin rightMargin stepClose<modulus =
  approximate-IVTΣ-rational-step-budget
    a
    step
    n
    f
    ivtData
    targetPrecision
    leftMargin
    rightMargin
    (defaultRationalStepIVTBudget
      step
      (uniformModulus
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        {f = f}
        (IVTFunctionData.uniformlyContinuous ivtData))
      leftMargin
      rightMargin
      targetPrecision
      stepClose<modulus)


approximate-IVTΣ-rational-step-with-right-default-budget :
  (a b : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid a (radius step) (suc n) ≡ b) →
  (f : [ rational a , rational b ]ᶜ → ℝᶜ) →
  (ivtData : IVTFunctionData (rational a) (rational b) f) →
  (targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  step +⁺ step <⁺
    uniformModulus
      {a = rational a}
      {b = rational b}
      {f = f}
      (IVTFunctionData.uniformlyContinuous ivtData)
      (IVTErrorBudget.movementPrecision
        (defaultIVTErrorBudget leftMargin rightMargin targetPrecision)) →
  NegativeMarginᶜ
    leftMargin
    (f
      (leftEndpoint
        {a = rational a}
        {b = rational b}
        (gridLowerWithRight≤ᶜ a b step (suc n) right-path))) →
  PositiveMarginᶜ
    rightMargin
    (f
      (rightEndpoint
        {a = rational a}
        {b = rational b}
        (gridLowerWithRight≤ᶜ a b step (suc n) right-path))) →
  Σ[ x ∈ [ rational a , rational b ]ᶜ ]
    absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-rational-step-with-right-default-budget a b step n right-path
    f ivtData targetPrecision leftMargin rightMargin stepClose<modulus =
  approximate-IVTΣ-rational-step-with-right-budget
    a
    b
    step
    n
    right-path
    f
    ivtData
    targetPrecision
    leftMargin
    rightMargin
    (defaultRationalStepIVTBudget
      step
      (uniformModulus
        {a = rational a}
        {b = rational b}
        {f = f}
        (IVTFunctionData.uniformlyContinuous ivtData))
      leftMargin
      rightMargin
      targetPrecision
      stepClose<modulus)


approximate-IVTΣ-rational-step-located-default-budget :
  (a : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (f :
    [ rational a ,
      rational (Rational.grid a (radius step) (suc n)) ]ᶜ →
    ℝᶜ) →
  (located : LocatedMap f) →
  (uc :
    UniformlyContinuousOnInterval
      (rational a)
      (rational (Rational.grid a (radius step) (suc n)))
      f) →
  (targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  step +⁺ step <⁺
    uniformModulus
      {a = rational a}
      {b = rational (Rational.grid a (radius step) (suc n))}
      {f = f}
      uc
      (IVTErrorBudget.movementPrecision
        (defaultIVTErrorBudget leftMargin rightMargin targetPrecision)) →
  NegativeMarginᶜ
    leftMargin
    (f
      (leftEndpoint
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        (gridLower≤ᶜ a step (suc n)))) →
  PositiveMarginᶜ
    rightMargin
    (f
      (rightEndpoint
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        (gridLower≤ᶜ a step (suc n)))) →
  Σ[ x ∈
    [ rational a ,
      rational (Rational.grid a (radius step) (suc n)) ]ᶜ ]
    absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-rational-step-located-default-budget a step n f located uc =
  approximate-IVTΣ-rational-step-default-budget
    a
    step
    n
    f
    (locatedIVTFunctionData located uc)


approximate-IVTΣ-rational-step-with-right-located-default-budget :
  (a b : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid a (radius step) (suc n) ≡ b) →
  (f : [ rational a , rational b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval (rational a) (rational b) f) →
  (targetPrecision : ℚ⁺) →
  (leftMargin rightMargin : ℚ⁺) →
  step +⁺ step <⁺
    uniformModulus
      {a = rational a}
      {b = rational b}
      {f = f}
      uc
      (IVTErrorBudget.movementPrecision
        (defaultIVTErrorBudget leftMargin rightMargin targetPrecision)) →
  NegativeMarginᶜ
    leftMargin
    (f
      (leftEndpoint
        {a = rational a}
        {b = rational b}
        (gridLowerWithRight≤ᶜ a b step (suc n) right-path))) →
  PositiveMarginᶜ
    rightMargin
    (f
      (rightEndpoint
        {a = rational a}
        {b = rational b}
        (gridLowerWithRight≤ᶜ a b step (suc n) right-path))) →
  Σ[ x ∈ [ rational a , rational b ]ᶜ ]
    absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-rational-step-with-right-located-default-budget
    a b step n right-path f located uc =
  approximate-IVTΣ-rational-step-with-right-default-budget
    a
    b
    step
    n
    right-path
    f
    (locatedIVTFunctionData located uc)


approximate-IVT∥∥-rational-step-strict :
  (a : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (f :
    [ rational a ,
      rational (Rational.grid a (radius step) (suc n)) ]ᶜ →
    ℝᶜ) →
  (ivtData :
    IVTFunctionData
      (rational a)
      (rational (Rational.grid a (radius step) (suc n)))
      f) →
  (targetPrecision : ℚ⁺) →
  ((leftMargin rightMargin : ℚ⁺) →
    RationalStepIVTBudget
      step
      (uniformModulus
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        {f = f}
        (IVTFunctionData.uniformlyContinuous ivtData))
      leftMargin
      rightMargin
      targetPrecision) →
  f
    (leftEndpoint
      {a = rational a}
      {b = rational (Rational.grid a (radius step) (suc n))}
      (gridLower≤ᶜ a step (suc n)))
    <ᶜ 0ᶜ →
  0ᶜ <ᶜ
    f
      (rightEndpoint
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        (gridLower≤ᶜ a step (suc n))) →
  ∥ Σ[ x ∈
      [ rational a ,
        rational (Rational.grid a (radius step) (suc n)) ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
approximate-IVT∥∥-rational-step-strict a step n f ivtData targetPrecision
    budgetAt leftNegative rightPositive =
  Prop.rec2 squash₁ combine leftMargins rightMargins
  where
  leftEndpointᶜ :
    [ rational a , rational (Rational.grid a (radius step) (suc n)) ]ᶜ
  leftEndpointᶜ =
    leftEndpoint
      {a = rational a}
      {b = rational (Rational.grid a (radius step) (suc n))}
      (gridLower≤ᶜ a step (suc n))

  rightEndpointᶜ :
    [ rational a , rational (Rational.grid a (radius step) (suc n)) ]ᶜ
  rightEndpointᶜ =
    rightEndpoint
      {a = rational a}
      {b = rational (Rational.grid a (radius step) (suc n))}
      (gridLower≤ᶜ a step (suc n))

  leftMargins :
    ∥ Σ[ margin ∈ ℚ⁺ ] NegativeMarginᶜ margin (f leftEndpointᶜ) ∥₁
  leftMargins =
    negativeStrictMargins (f leftEndpointᶜ) leftNegative

  rightMargins :
    ∥ Σ[ margin ∈ ℚ⁺ ] PositiveMarginᶜ margin (f rightEndpointᶜ) ∥₁
  rightMargins =
    positiveStrictMargins (f rightEndpointᶜ) rightPositive

  combine :
    Σ[ leftMargin ∈ ℚ⁺ ] NegativeMarginᶜ leftMargin (f leftEndpointᶜ) →
    Σ[ rightMargin ∈ ℚ⁺ ] PositiveMarginᶜ rightMargin (f rightEndpointᶜ) →
    ∥ Σ[ x ∈
        [ rational a ,
          rational (Rational.grid a (radius step) (suc n)) ]ᶜ ]
        absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
  combine (leftMargin , leftMarginData) (rightMargin , rightMarginData) =
    ∣ approximate-IVTΣ-rational-step-budget
        a
        step
        n
        f
        ivtData
        targetPrecision
        leftMargin
        rightMargin
        (budgetAt leftMargin rightMargin)
        leftMarginData
        rightMarginData
    ∣₁


approximate-IVT∥∥-rational-step-with-right-strict :
  (a b : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid a (radius step) (suc n) ≡ b) →
  (f : [ rational a , rational b ]ᶜ → ℝᶜ) →
  (ivtData : IVTFunctionData (rational a) (rational b) f) →
  (targetPrecision : ℚ⁺) →
  ((leftMargin rightMargin : ℚ⁺) →
    RationalStepIVTBudget
      step
      (uniformModulus
        {a = rational a}
        {b = rational b}
        {f = f}
        (IVTFunctionData.uniformlyContinuous ivtData))
      leftMargin
      rightMargin
      targetPrecision) →
  f
    (leftEndpoint
      {a = rational a}
      {b = rational b}
      (gridLowerWithRight≤ᶜ a b step (suc n) right-path))
    <ᶜ 0ᶜ →
  0ᶜ <ᶜ
    f
      (rightEndpoint
        {a = rational a}
        {b = rational b}
        (gridLowerWithRight≤ᶜ a b step (suc n) right-path)) →
  ∥ Σ[ x ∈ [ rational a , rational b ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
approximate-IVT∥∥-rational-step-with-right-strict a b step n right-path
    f ivtData targetPrecision budgetAt =
  approximate-IVT∥∥-grid-strict
    f
    ivtData
    rationalGrid
    targetPrecision
    (λ leftMargin rightMargin →
      RationalStepIVTBudget.errorBudget (budgetAt leftMargin rightMargin))
    adjacentAt
  where
  a≤b : rational a ≤ᶜ rational b
  a≤b =
    gridLowerWithRight≤ᶜ a b step (suc n) right-path

  rationalGrid : Grid (rational a) (rational b) a≤b (suc n)
  rationalGrid =
    rationalStepGridWithRight a b step (suc n) right-path

  adjacentAt :
    (leftMargin rightMargin : ℚ⁺) →
    AdjacentClose
      rationalGrid
      (uniformModulus
        {a = rational a}
        {b = rational b}
        {f = f}
        (IVTFunctionData.uniformlyContinuous ivtData)
        (IVTErrorBudget.movementPrecision
          (RationalStepIVTBudget.errorBudget
            (budgetAt leftMargin rightMargin))))
  adjacentAt leftMargin rightMargin i =
    MetricSpace.close-mono
      (IntervalMetric (rational a) (rational b))
      {x = Grid.point rationalGrid (Fin.weakenFin i)}
      {y = Grid.point rationalGrid (Fin.suc i)}
      {ε = step +⁺ step}
      {δ =
        uniformModulus
          {a = rational a}
          {b = rational b}
          {f = f}
          (IVTFunctionData.uniformlyContinuous ivtData)
          (IVTErrorBudget.movementPrecision
            (RationalStepIVTBudget.errorBudget
              (budgetAt leftMargin rightMargin)))}
      (RationalStepIVTBudget.stepClose<modulus
        (budgetAt leftMargin rightMargin))
      (rationalStepGridWithRightAdjacentClose a b step (suc n) right-path i)


approximate-IVT∥∥-rational-step-located-strict :
  (a : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (f :
    [ rational a ,
      rational (Rational.grid a (radius step) (suc n)) ]ᶜ →
    ℝᶜ) →
  (located : LocatedMap f) →
  (uc :
    UniformlyContinuousOnInterval
      (rational a)
      (rational (Rational.grid a (radius step) (suc n)))
      f) →
  (targetPrecision : ℚ⁺) →
  ((leftMargin rightMargin : ℚ⁺) →
    RationalStepIVTBudget
      step
      (uniformModulus
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        {f = f}
        uc)
      leftMargin
      rightMargin
      targetPrecision) →
  f
    (leftEndpoint
      {a = rational a}
      {b = rational (Rational.grid a (radius step) (suc n))}
      (gridLower≤ᶜ a step (suc n)))
    <ᶜ 0ᶜ →
  0ᶜ <ᶜ
    f
      (rightEndpoint
        {a = rational a}
        {b = rational (Rational.grid a (radius step) (suc n))}
        (gridLower≤ᶜ a step (suc n))) →
  ∥ Σ[ x ∈
      [ rational a ,
        rational (Rational.grid a (radius step) (suc n)) ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
approximate-IVT∥∥-rational-step-located-strict a step n f located uc =
  approximate-IVT∥∥-rational-step-strict
    a
    step
    n
    f
    (locatedIVTFunctionData located uc)


approximate-IVTΣ-rational-step-with-right-located-strict :
  (a b : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid a (radius step) (suc n) ≡ b) →
  (f : [ rational a , rational b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval (rational a) (rational b) f) →
  (targetPrecision : ℚ⁺) →
  ((leftMargin rightMargin : ℚ⁺) →
    RationalStepIVTBudget
      step
      (uniformModulus
        {a = rational a}
        {b = rational b}
        {f = f}
        uc)
      leftMargin
      rightMargin
      targetPrecision) →
  f
    (leftEndpoint
      {a = rational a}
      {b = rational b}
      (gridLowerWithRight≤ᶜ a b step (suc n) right-path))
    <ᶜ 0ᶜ →
  0ᶜ <ᶜ
    f
      (rightEndpoint
        {a = rational a}
        {b = rational b}
        (gridLowerWithRight≤ᶜ a b step (suc n) right-path)) →
  Σ[ x ∈ [ rational a , rational b ]ᶜ ]
    absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-rational-step-with-right-located-strict
    a b step n right-path f located uc targetPrecision budgetAt =
  approximate-IVTΣ-grid-located-strict
    f
    located
    uc
    rationalGrid
    targetPrecision
    (λ leftMargin rightMargin →
      RationalStepIVTBudget.errorBudget (budgetAt leftMargin rightMargin))
    adjacentAt
  where
  a≤b : rational a ≤ᶜ rational b
  a≤b =
    gridLowerWithRight≤ᶜ a b step (suc n) right-path

  rationalGrid : Grid (rational a) (rational b) a≤b (suc n)
  rationalGrid =
    rationalStepGridWithRight a b step (suc n) right-path

  adjacentAt :
    (leftMargin rightMargin : ℚ⁺) →
    AdjacentClose
      rationalGrid
      (uniformModulus
        {a = rational a}
        {b = rational b}
        {f = f}
        uc
        (IVTErrorBudget.movementPrecision
          (RationalStepIVTBudget.errorBudget
            (budgetAt leftMargin rightMargin))))
  adjacentAt leftMargin rightMargin i =
    MetricSpace.close-mono
      (IntervalMetric (rational a) (rational b))
      {x = Grid.point rationalGrid (Fin.weakenFin i)}
      {y = Grid.point rationalGrid (Fin.suc i)}
      {ε = step +⁺ step}
      {δ =
        uniformModulus
          {a = rational a}
          {b = rational b}
          {f = f}
          uc
          (IVTErrorBudget.movementPrecision
            (RationalStepIVTBudget.errorBudget
              (budgetAt leftMargin rightMargin)))}
      (RationalStepIVTBudget.stepClose<modulus
        (budgetAt leftMargin rightMargin))
      (rationalStepGridWithRightAdjacentClose a b step (suc n) right-path i)


approximate-IVTΣ-rational-located-strict :
  (a b : ℚ) →
  (a<b : a ℚOrder.< b) →
  (f : [ rational a , rational b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval (rational a) (rational b) f) →
  (targetPrecision : ℚ⁺) →
  f
    (leftEndpoint
      {a = rational a}
      {b = rational b}
      (≤ℚ→rational≤ᶜ (Rational.<→≤ {p = a} {q = b} a<b)))
    <ᶜ 0ᶜ →
  0ᶜ <ᶜ
    f
      (rightEndpoint
        {a = rational a}
        {b = rational b}
        (≤ℚ→rational≤ᶜ (Rational.<→≤ {p = a} {q = b} a<b))) →
  Σ[ x ∈ [ rational a , rational b ]ᶜ ]
    absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ-rational-located-strict
    a b a<b f located uc targetPrecision leftNegative rightPositive =
  approximate-IVTΣ-rational-step-with-right-budget
    a
    b
    step
    n
    right-path
    f
    (locatedIVTFunctionData located uc)
    targetPrecision
    leftMargin
    rightMargin
    budget
    leftMarginData'
    rightMarginData'
  where
  direct≤ : rational a ≤ᶜ rational b
  direct≤ =
    ≤ℚ→rational≤ᶜ (Rational.<→≤ {p = a} {q = b} a<b)

  leftEndpointDirect : [ rational a , rational b ]ᶜ
  leftEndpointDirect =
    leftEndpoint {a = rational a} {b = rational b} direct≤

  rightEndpointDirect : [ rational a , rational b ]ᶜ
  rightEndpointDirect =
    rightEndpoint {a = rational a} {b = rational b} direct≤

  signData : SignData (f leftEndpointDirect) (f rightEndpointDirect)
  signData =
    locatedStrictSignData
      (f leftEndpointDirect)
      (f rightEndpointDirect)
      (LocatedMap.locatorAt located leftEndpointDirect)
      (LocatedMap.locatorAt located rightEndpointDirect)
      leftNegative
      rightPositive

  leftMargin : ℚ⁺
  leftMargin =
    signData .fst .fst

  rightMargin : ℚ⁺
  rightMargin =
    signData .snd .fst

  leftMarginData :
    NegativeMarginᶜ leftMargin (f leftEndpointDirect)
  leftMarginData =
    signData .fst .snd

  rightMarginData :
    PositiveMarginᶜ rightMargin (f rightEndpointDirect)
  rightMarginData =
    signData .snd .snd

  errorBudget : IVTErrorBudget leftMargin rightMargin targetPrecision
  errorBudget =
    defaultIVTErrorBudget leftMargin rightMargin targetPrecision

  mesh : ℚ⁺
  mesh =
    uniformModulus
      {a = rational a}
      {b = rational b}
      {f = f}
      uc
      (IVTErrorBudget.movementPrecision errorBudget)

  stepData :
    Σ[ k ∈ ℕ ]
      (Rational.grid a (radius (rationalExactStep a b a<b k)) (suc k) ≡ b) ×
      (rationalExactStep a b a<b k +⁺ rationalExactStep a b a<b k <⁺ mesh)
  stepData =
    rationalExactStepGridData a b a<b mesh

  n : ℕ
  n =
    stepData .fst

  step : ℚ⁺
  step =
    rationalExactStep a b a<b n

  right-path : Rational.grid a (radius step) (suc n) ≡ b
  right-path =
    stepData .snd .fst

  stepClose<modulus : step +⁺ step <⁺ mesh
  stepClose<modulus =
    stepData .snd .snd

  grid≤ : rational a ≤ᶜ rational b
  grid≤ =
    gridLowerWithRight≤ᶜ a b step (suc n) right-path

  leftEndpointPath :
    leftEndpoint {a = rational a} {b = rational b} grid≤ ≡
    leftEndpointDirect
  leftEndpointPath =
    Σ≡Prop (isPropIntervalBounds (rational a) (rational b)) refl

  rightEndpointPath :
    rightEndpoint {a = rational a} {b = rational b} grid≤ ≡
    rightEndpointDirect
  rightEndpointPath =
    Σ≡Prop (isPropIntervalBounds (rational a) (rational b)) refl

  leftMarginData' :
    NegativeMarginᶜ
      leftMargin
      (f
        (leftEndpoint
          {a = rational a}
          {b = rational b}
          grid≤))
  leftMarginData' =
    subst
      (λ x → NegativeMarginᶜ leftMargin (f x))
      (sym leftEndpointPath)
      leftMarginData

  rightMarginData' :
    PositiveMarginᶜ
      rightMargin
      (f
        (rightEndpoint
          {a = rational a}
          {b = rational b}
          grid≤))
  rightMarginData' =
    subst
      (λ x → PositiveMarginᶜ rightMargin (f x))
      (sym rightEndpointPath)
      rightMarginData

  budget :
    RationalStepIVTBudget
      step
      (uniformModulus
        {a = rational a}
        {b = rational b}
        {f = f}
        uc)
      leftMargin
      rightMargin
      targetPrecision
  budget =
    defaultRationalStepIVTBudget
      step
      (uniformModulus
        {a = rational a}
        {b = rational b}
        {f = f}
        uc)
      leftMargin
      rightMargin
      targetPrecision
      stepClose<modulus


approximate-IVT∥∥-rational-located-strict :
  (a b : ℚ) →
  (a<b : a ℚOrder.< b) →
  (f : [ rational a , rational b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval (rational a) (rational b) f) →
  (targetPrecision : ℚ⁺) →
  f
    (leftEndpoint
      {a = rational a}
      {b = rational b}
      (≤ℚ→rational≤ᶜ (Rational.<→≤ {p = a} {q = b} a<b)))
    <ᶜ 0ᶜ →
  0ᶜ <ᶜ
    f
      (rightEndpoint
        {a = rational a}
        {b = rational b}
        (≤ℚ→rational≤ᶜ (Rational.<→≤ {p = a} {q = b} a<b))) →
  ∥ Σ[ x ∈ [ rational a , rational b ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
approximate-IVT∥∥-rational-located-strict a b a<b f located uc targetPrecision
    leftNegative rightPositive =
  ∣ approximate-IVTΣ-rational-located-strict
      a
      b
      a<b
      f
      located
      uc
      targetPrecision
      leftNegative
      rightPositive ∣₁


approximate-IVT∥∥-rational-step-with-right-located-strict :
  (a b : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid a (radius step) (suc n) ≡ b) →
  (f : [ rational a , rational b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : UniformlyContinuousOnInterval (rational a) (rational b) f) →
  (targetPrecision : ℚ⁺) →
  ((leftMargin rightMargin : ℚ⁺) →
    RationalStepIVTBudget
      step
      (uniformModulus
        {a = rational a}
        {b = rational b}
        {f = f}
        uc)
      leftMargin
      rightMargin
      targetPrecision) →
  f
    (leftEndpoint
      {a = rational a}
      {b = rational b}
      (gridLowerWithRight≤ᶜ a b step (suc n) right-path))
    <ᶜ 0ᶜ →
  0ᶜ <ᶜ
    f
      (rightEndpoint
        {a = rational a}
        {b = rational b}
        (gridLowerWithRight≤ᶜ a b step (suc n) right-path)) →
  ∥ Σ[ x ∈ [ rational a , rational b ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
approximate-IVT∥∥-rational-step-with-right-located-strict
    a b step n right-path f located uc =
  approximate-IVT∥∥-rational-step-with-right-strict
    a
    b
    step
    n
    right-path
    f
    (locatedIVTFunctionData located uc)
