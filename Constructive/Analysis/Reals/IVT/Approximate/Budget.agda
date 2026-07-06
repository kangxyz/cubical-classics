{-

Explicit error budgets for untruncated approximate IVT

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.IVT.Approximate.Budget where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


record IVTErrorBudget
    (leftMargin rightMargin targetPrecision : ℚ⁺) :
    Type₀ where
  no-eta-equality

  field
    samplePrecision : ℚ⁺
    movementPrecision : ℚ⁺
    boundPrecision : ℚ⁺

    sample<bound :
      samplePrecision <⁺ boundPrecision
    bound<left :
      boundPrecision <⁺ leftMargin
    bound<right :
      boundPrecision <⁺ rightMargin
    small+bound<target :
      (((samplePrecision +⁺ movementPrecision) +⁺ samplePrecision) +⁺
       boundPrecision)
        <⁺ targetPrecision


smallPrecision :
  {leftMargin rightMargin targetPrecision : ℚ⁺} →
  IVTErrorBudget leftMargin rightMargin targetPrecision →
  ℚ⁺
smallPrecision budget =
  (IVTErrorBudget.samplePrecision budget +⁺
   IVTErrorBudget.movementPrecision budget) +⁺
  IVTErrorBudget.samplePrecision budget


record RationalStepIVTBudget
    (step : ℚ⁺)
    (μ : PrecisionModulus)
    (leftMargin rightMargin targetPrecision : ℚ⁺) :
    Type₀ where
  no-eta-equality

  field
    errorBudget :
      IVTErrorBudget leftMargin rightMargin targetPrecision
    stepClose<modulus :
      step +⁺ step <⁺ μ (IVTErrorBudget.movementPrecision errorBudget)


private
  basePrecision : ℚ⁺ → ℚ⁺ → ℚ⁺ → ℚ⁺
  basePrecision leftMargin rightMargin targetPrecision =
    min⁺ targetPrecision (min⁺ leftMargin rightMargin)

  base≤target :
    (leftMargin rightMargin targetPrecision : ℚ⁺) →
    radius (basePrecision leftMargin rightMargin targetPrecision) ℚOrder.≤
    radius targetPrecision
  base≤target leftMargin rightMargin targetPrecision =
    min⁺≤left targetPrecision (min⁺ leftMargin rightMargin)

  base≤left :
    (leftMargin rightMargin targetPrecision : ℚ⁺) →
    radius (basePrecision leftMargin rightMargin targetPrecision) ℚOrder.≤
    radius leftMargin
  base≤left leftMargin rightMargin targetPrecision =
    Rational.≤-trans
      {p = radius (basePrecision leftMargin rightMargin targetPrecision)}
      {q = radius (min⁺ leftMargin rightMargin)}
      {r = radius leftMargin}
      (min⁺≤right targetPrecision (min⁺ leftMargin rightMargin))
      (min⁺≤left leftMargin rightMargin)

  base≤right :
    (leftMargin rightMargin targetPrecision : ℚ⁺) →
    radius (basePrecision leftMargin rightMargin targetPrecision) ℚOrder.≤
    radius rightMargin
  base≤right leftMargin rightMargin targetPrecision =
    Rational.≤-trans
      {p = radius (basePrecision leftMargin rightMargin targetPrecision)}
      {q = radius (min⁺ leftMargin rightMargin)}
      {r = radius rightMargin}
      (min⁺≤right targetPrecision (min⁺ leftMargin rightMargin))
      (min⁺≤right leftMargin rightMargin)

  budget-sum-path :
    (q : ℚ) →
    ((half q ℚ.+ q) ℚ.+ half q) ℚ.+ q ≡
    (q ℚ.+ q) ℚ.+ q
  budget-sum-path q =
    cong (λ r → r ℚ.+ q)
      (sym (ℚ.+Assoc (half q) q (half q)) ∙
       cong (half q ℚ.+_) (ℚ.+Comm q (half q)) ∙
       ℚ.+Assoc (half q) (half q) q ∙
       cong (λ r → r ℚ.+ q) (half+half≡ q))


defaultIVTErrorBudget :
  (leftMargin rightMargin targetPrecision : ℚ⁺) →
  IVTErrorBudget leftMargin rightMargin targetPrecision
defaultIVTErrorBudget leftMargin rightMargin targetPrecision
    .IVTErrorBudget.samplePrecision =
  half⁺ boundPrecision
  where
  boundPrecision : ℚ⁺
  boundPrecision =
    quarter⁺ (basePrecision leftMargin rightMargin targetPrecision)
defaultIVTErrorBudget leftMargin rightMargin targetPrecision
    .IVTErrorBudget.movementPrecision =
  quarter⁺ (basePrecision leftMargin rightMargin targetPrecision)
defaultIVTErrorBudget leftMargin rightMargin targetPrecision
    .IVTErrorBudget.boundPrecision =
  quarter⁺ (basePrecision leftMargin rightMargin targetPrecision)
defaultIVTErrorBudget leftMargin rightMargin targetPrecision
    .IVTErrorBudget.sample<bound =
  half< (quarter⁺ (basePrecision leftMargin rightMargin targetPrecision))
defaultIVTErrorBudget leftMargin rightMargin targetPrecision
    .IVTErrorBudget.bound<left =
  ℚOrder.isTrans<≤
    (radius boundPrecision)
    (radius base)
    (radius leftMargin)
    (quarter< base)
    (base≤left leftMargin rightMargin targetPrecision)
  where
  base : ℚ⁺
  base =
    basePrecision leftMargin rightMargin targetPrecision

  boundPrecision : ℚ⁺
  boundPrecision =
    quarter⁺ base
defaultIVTErrorBudget leftMargin rightMargin targetPrecision
    .IVTErrorBudget.bound<right =
  ℚOrder.isTrans<≤
    (radius boundPrecision)
    (radius base)
    (radius rightMargin)
    (quarter< base)
    (base≤right leftMargin rightMargin targetPrecision)
  where
  base : ℚ⁺
  base =
    basePrecision leftMargin rightMargin targetPrecision

  boundPrecision : ℚ⁺
  boundPrecision =
    quarter⁺ base
defaultIVTErrorBudget leftMargin rightMargin targetPrecision
    .IVTErrorBudget.small+bound<target =
  Rational.<≤-trans
    {p = radius (((samplePrecision +⁺ movementPrecision) +⁺ samplePrecision) +⁺
                 boundPrecision)}
    {q = radius base}
    {r = radius targetPrecision}
    small+bound<base
    (base≤target leftMargin rightMargin targetPrecision)
  where
  base : ℚ⁺
  base =
    basePrecision leftMargin rightMargin targetPrecision

  boundPrecision : ℚ⁺
  boundPrecision =
    quarter⁺ base

  samplePrecision : ℚ⁺
  samplePrecision =
    half⁺ boundPrecision

  movementPrecision : ℚ⁺
  movementPrecision =
    boundPrecision

  small+bound<base :
    (((samplePrecision +⁺ movementPrecision) +⁺ samplePrecision) +⁺
     boundPrecision)
      <⁺
    base
  small+bound<base =
    subst
      (λ ρ → ρ ℚOrder.< radius base)
      (sym (budget-sum-path (radius boundPrecision)))
      (three-quarter< base)


defaultRationalStepIVTBudget :
  (step : ℚ⁺) →
  (μ : PrecisionModulus) →
  (leftMargin rightMargin targetPrecision : ℚ⁺) →
  step +⁺ step <⁺
    μ (IVTErrorBudget.movementPrecision
      (defaultIVTErrorBudget leftMargin rightMargin targetPrecision)) →
  RationalStepIVTBudget step μ leftMargin rightMargin targetPrecision
defaultRationalStepIVTBudget step μ leftMargin rightMargin targetPrecision stepClose<modulus
    .RationalStepIVTBudget.errorBudget =
  defaultIVTErrorBudget leftMargin rightMargin targetPrecision
defaultRationalStepIVTBudget step μ leftMargin rightMargin targetPrecision stepClose<modulus
    .RationalStepIVTBudget.stepClose<modulus =
  stepClose<modulus
