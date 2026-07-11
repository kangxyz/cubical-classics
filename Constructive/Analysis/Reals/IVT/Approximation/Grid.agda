{-

Finite-grid approximate IVT lemmas

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.IVT.Approximation.Grid where

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
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
  using (≤ℚ→rational≤ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.Interval.Base
open import Constructive.Analysis.Reals.Interval.Grid.Base
open import Constructive.Analysis.Reals.Interval.Grid.Affine
open import Constructive.Analysis.Reals.Interval.Grid.Rational
open import Constructive.Analysis.Reals.IVT.Approximation.Budget
  using
    ( IVTErrorBudget
    ; RationalStepIVTBudget
    ; defaultIVTErrorBudget
    ; defaultRationalStepIVTBudget
    )
open import Constructive.Analysis.Reals.IVT.Approximation.Endpoint
open import Constructive.Analysis.Reals.IVT.Approximation.GridSearch
open import Constructive.Analysis.Reals.IVT.Approximation.Sampling
open import Constructive.Analysis.Reals.IVT.Uniform
open import Constructive.Analysis.Reals.Locator
  using (ApproxEvaluable ; LocatedMap ; Locator)
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
      (IVTFunctionData.uniformlyContinuous {a = a} {b = b} {f = f} ivtData)
      movementPrecision) →
  gridSampleValues {a = a} {b = b} {f = f}
    ivtData G samplePrecision Fin.zero ℚOrder.< 0ℚ →
  0ℚ ℚOrder.≤
    gridSampleValues {a = a} {b = b} {f = f}
      ivtData G samplePrecision (Fin.fromℕ (suc n)) →
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
        (gridSampleValues {a = a} {b = b} {f = f}
          ivtData G samplePrecision)
        smallPrecision
        i
  near =
    gridNearZeroRight
      n
      (gridSampleValues {a = a} {b = b} {f = f} ivtData G samplePrecision)
      smallPrecision
      (adjacentSampleValuesClose
        {a = a}
        {b = b}
        {f = f}
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
      (gridSampleValues {a = a} {b = b} {f = f}
        ivtData G samplePrecision)
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
      (IVTFunctionData.uniformlyContinuous {a = a} {b = b} {f = f} ivtData)
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
      (IVTFunctionData.uniformlyContinuous {a = a} {b = b} {f = f} ivtData)
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


approximate-IVT∥∥-grid-budget :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (uc : isUniformlyContinuousOnInterval a b f) →
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
  ∥ Σ[ x ∈ [ a , b ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
approximate-IVT∥∥-grid-budget {a = a} {b = b} {a≤b = a≤b}
    f uc {n = n} G targetPrecision leftMargin rightMargin budget adjacentClose
    leftMarginData rightMarginData =
  Prop.rec squash₁ sampleStep
    (gridApproxValues∥∥
      {a = a}
      {b = b}
      {a≤b = a≤b}
      {f = f}
      {n = suc n}
      G
      sample)
  where
  sample movement bound small : ℚ⁺
  sample =
    IVTErrorBudget.samplePrecision budget
  movement =
    IVTErrorBudget.movementPrecision budget
  bound =
    IVTErrorBudget.boundPrecision budget
  small =
    (sample +⁺ movement) +⁺ sample

  sampleStep :
    ApproxValues (λ i → f (Grid.point G i)) sample →
    ∥ Σ[ x ∈ [ a , b ]ᶜ ]
        absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
  sampleStep (values , valuesClose) =
    ∣ Grid.point G nearIndex ,
      sampleNonnegativeSmallAbsWithValues<
        {a = a}
        {b = b}
        {a≤b = a≤b}
        {f = f}
        {n = suc n}
        G
        values
        sample
        bound
        small
        targetPrecision
        (IVTErrorBudget.sample<bound budget)
        (IVTErrorBudget.small+bound<target budget)
        valuesClose
        nearIndex
        nearSmall
    ∣₁
    where
    adjacentValues :
      (i : Fin (suc n)) →
      AdjacentValuesClose values small i
    adjacentValues =
      adjacentSampleValuesCloseWithValues
        {a = a}
        {b = b}
        {a≤b = a≤b}
        {f = f}
        uc
        {n = n}
        G
        sample
        movement
        adjacentClose
        values
        valuesClose

    first<0 : values Fin.zero ℚOrder.< 0ℚ
    first<0 =
      leftEndpointSampleNegativeWithValues
        {a = a}
        {b = b}
        {a≤b = a≤b}
        {f = f}
        {n = suc n}
        G
        values
        sample
        bound
        leftMargin
        (IVTErrorBudget.sample<bound budget)
        (IVTErrorBudget.bound<left budget)
        leftMarginData
        valuesClose

    0≤last : 0ℚ ℚOrder.≤ values (Fin.fromℕ (suc n))
    0≤last =
      rightEndpointSampleNonnegativeWithValues
        {a = a}
        {b = b}
        {a≤b = a≤b}
        {f = f}
        {n = suc n}
        G
        values
        sample
        bound
        rightMargin
        (IVTErrorBudget.sample<bound budget)
        (IVTErrorBudget.bound<right budget)
        rightMarginData
        valuesClose

    near :
      Σ[ i ∈ Fin (suc (suc n)) ]
        NonnegativeSmall values small i
    near =
      gridNearZeroRight
        n
        values
        small
        adjacentValues
        first<0
        0≤last

    nearIndex : Fin (suc (suc n))
    nearIndex =
      near .fst

    nearSmall :
      NonnegativeSmall values small nearIndex
    nearSmall =
      near .snd
