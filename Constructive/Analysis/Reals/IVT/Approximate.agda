{-

Public approximate IVT interface

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.IVT.Approximate where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.Interval
open import Constructive.Analysis.Reals.IVT.Uniform
open import Constructive.Analysis.Reals.Locator.Base using (Locator)
open import Constructive.Analysis.Reals.Locator.Map using (LocatedMap)
open import Constructive.Data.PositiveRationals
import Constructive.Analysis.Reals.IVT.Approximate.Proofs as Proofs


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
  Proofs.approximate-IVTΣ
    {a = a}
    {b = b}
    loc-a
    loc-b
    a≤b
    f
    ivtData
    loc-left
    loc-right
    targetPrecision
    leftNegative
    rightPositive


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
    loc-a loc-b a≤b f located uc targetPrecision
    leftNegative rightPositive =
  Proofs.approximate-IVTΣ-located
    {a = a}
    {b = b}
    loc-a
    loc-b
    a≤b
    f
    located
    uc
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
approximate-IVT∥∥ {a = a} {b = b}
    loc-a loc-b a≤b f ivtData loc-left loc-right targetPrecision
    leftNegative rightPositive =
  Proofs.approximate-IVT∥∥
    {a = a}
    {b = b}
    loc-a
    loc-b
    a≤b
    f
    ivtData
    loc-left
    loc-right
    targetPrecision
    leftNegative
    rightPositive


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
    loc-a loc-b a≤b f located uc targetPrecision
    leftNegative rightPositive =
  Proofs.approximate-IVT∥∥-located
    {a = a}
    {b = b}
    loc-a
    loc-b
    a≤b
    f
    located
    uc
    targetPrecision
    leftNegative
    rightPositive
