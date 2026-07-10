{-

Rational-endpoint approximate IVT lemmas

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.IVT.Approximate.RationalEndpoint where

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
open import Constructive.Analysis.Reals.Interval.Base
open import Constructive.Analysis.Reals.Interval.Grid.Base
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

open import Constructive.Analysis.Reals.IVT.Approximate.RationalStep

approximate-IVTΣ-rational-located-strict :
  (a b : ℚ) →
  (a<b : a ℚOrder.< b) →
  (f : [ rational a , rational b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : isUniformlyContinuousOnInterval (rational a) (rational b) f) →
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
    (locatedIVTFunctionData
      {a = rational a}
      {b = rational b}
      {f = f}
      located
      uc)
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
  (uc : isUniformlyContinuousOnInterval (rational a) (rational b) f) →
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
  (uc : isUniformlyContinuousOnInterval (rational a) (rational b) f) →
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
    (locatedIVTFunctionData
      {a = rational a}
      {b = rational b}
      {f = f}
      located
      uc)
