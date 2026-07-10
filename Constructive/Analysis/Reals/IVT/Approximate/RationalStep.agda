{-

Rational-step approximate IVT lemmas

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.IVT.Approximate.RationalStep where

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

open import Constructive.Analysis.Reals.IVT.Approximate.Grid

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
      (ivtData .snd)
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
        (ivtData .snd)
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
          (ivtData .snd)
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
      (ivtData .snd)
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
        (ivtData .snd)
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
          (ivtData .snd)
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
      (ivtData .snd))
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
      (ivtData .snd))
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
    isUniformlyContinuousOnInterval
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
    (locatedIVTFunctionData
      {a = rational a}
      {b = rational (Rational.grid a (radius step) (suc n))}
      {f = f}
      located
      uc)


approximate-IVTΣ-rational-step-with-right-located-budget :
  (a b : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid a (radius step) (suc n) ≡ b) →
  (f : [ rational a , rational b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : isUniformlyContinuousOnInterval (rational a) (rational b) f) →
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
    (locatedIVTFunctionData
      {a = rational a}
      {b = rational b}
      {f = f}
      located
      uc)



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
      (ivtData .snd)
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
        (ivtData .snd))
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
      (ivtData .snd)
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
        (ivtData .snd))
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
    isUniformlyContinuousOnInterval
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
    (locatedIVTFunctionData
      {a = rational a}
      {b = rational (Rational.grid a (radius step) (suc n))}
      {f = f}
      located
      uc)


approximate-IVTΣ-rational-step-with-right-located-default-budget :
  (a b : ℚ) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid a (radius step) (suc n) ≡ b) →
  (f : [ rational a , rational b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : isUniformlyContinuousOnInterval (rational a) (rational b) f) →
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
    (locatedIVTFunctionData
      {a = rational a}
      {b = rational b}
      {f = f}
      located
      uc)



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
        (ivtData .snd))
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
        (ivtData .snd))
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
        (ivtData .snd)
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
          (ivtData .snd)
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
    isUniformlyContinuousOnInterval
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
    (locatedIVTFunctionData
      {a = rational a}
      {b = rational (Rational.grid a (radius step) (suc n))}
      {f = f}
      located
      uc)


approximate-IVTΣ-rational-step-with-right-located-strict :
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
