{-

Interval approximate IVT assembly lemmas

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.IVT.Approximation.Construction where

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
open import Constructive.Analysis.Reals.Interval.Order using (gapᶜ)
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

open import Constructive.Analysis.Reals.IVT.Approximation.Grid

approximate-IVTΣ-with-locators-and-gap-bound :
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
approximate-IVTΣ-with-locators-and-gap-bound {a = a} {b = b}
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
      (ivtData .snd)
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


approximate-IVTΣ-with-locators :
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
approximate-IVTΣ-with-locators {a = a} {b = b}
    loc-a loc-b a≤b f ivtData loc-left loc-right targetPrecision
    leftNegative rightPositive =
  approximate-IVTΣ-with-locators-and-gap-bound
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



approximate-IVT∥∥-with-gap-bound :
  {a b : ℝᶜ} →
  (a≤b : a ≤ᶜ b) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (gapᶜ a b) →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (uc : isUniformlyContinuousOnInterval a b f) →
  (targetPrecision : ℚ⁺) →
  f (leftEndpoint {a = a} {b = b} a≤b) <ᶜ 0ᶜ →
  0ᶜ <ᶜ f (rightEndpoint {a = a} {b = b} a≤b) →
  ∥ Σ[ x ∈ [ a , b ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
approximate-IVT∥∥-with-gap-bound {a = a} {b = b}
    a≤b κ gap-bound f uc targetPrecision leftNegative rightPositive =
  Prop.rec squash₁ combine
    (strictSignData∥∥ (f leftEndpointᶜ) (f rightEndpointᶜ)
      leftNegative rightPositive)
  where
  leftEndpointᶜ : [ a , b ]ᶜ
  leftEndpointᶜ =
    leftEndpoint {a = a} {b = b} a≤b

  rightEndpointᶜ : [ a , b ]ᶜ
  rightEndpointᶜ =
    rightEndpoint {a = a} {b = b} a≤b

  combine :
    SignData (f leftEndpointᶜ) (f rightEndpointᶜ) →
    ∥ Σ[ x ∈ [ a , b ]ᶜ ]
        absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
  combine ((leftMargin , leftMarginData) , (rightMargin , rightMarginData)) =
    approximate-IVT∥∥-grid-budget
      f
      uc
      G
      targetPrecision
      leftMargin
      rightMargin
      budget
      adjacent
      leftMarginData
      rightMarginData
    where
    budget : IVTErrorBudget leftMargin rightMargin targetPrecision
    budget =
      defaultIVTErrorBudget leftMargin rightMargin targetPrecision

    mesh : ℚ⁺
    mesh =
      uniformModulus {a = a} {b = b} {f = f}
        uc
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
