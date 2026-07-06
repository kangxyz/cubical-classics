{-

Finite-grid approximate IVT lemmas

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.IVT.Approximate.Grid where

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
open import Constructive.Analysis.Reals.IVT.Approximate.Budget
  using
    ( IVTErrorBudget
    ; RationalStepIVTBudget
    ; defaultIVTErrorBudget
    ; defaultRationalStepIVTBudget
    )
open import Constructive.Analysis.Reals.IVT.Approximate.Endpoint
open import Constructive.Analysis.Reals.IVT.GridSearch
open import Constructive.Analysis.Reals.IVT.Approximate.Sampling
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

