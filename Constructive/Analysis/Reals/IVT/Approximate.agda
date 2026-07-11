{-

Public approximate IVT interface

The theorems in this module state the constructive, approximate form of the
intermediate value theorem used by the rest of the library.

The first theorem, approximate-IVT∥∥, is the usual uniformly-continuous
constructive approximate IVT: it proves only truncated existence, so its finite
grid sampling may use merely existing rational approximations of Cauchy reals.

The Σ variants are Bishop-style witness-producing forms.  They return an
explicit approximate zero, so the interval and function values must be
located/evaluable.

Frank proves a stronger ∥∥ theorem: pointwise continuity is enough.  That is
not a small variation of the grid proof below; it uses a different
interpolating construction.

https://arxiv.org/abs/1701.02227

The Frank version is not implemented here.

None of these theorems assert an exact zero of f.

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.IVT.Approximate where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; squash₁)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.Interval.Base
open import Constructive.Analysis.Reals.Interval.Order using (gapᶜ)
open import Constructive.Analysis.Reals.IVT.Uniform
open import Constructive.Analysis.Reals.Locator using (LocatedMap ; Locator)
open import Constructive.Data.PositiveRationals
import Constructive.Analysis.Reals.IVT.Approximation.Construction as Proofs


-- Standard uniformly-continuous constructive approximate IVT.  The conclusion
-- is propositionally truncated, so the proof may choose the finite grid
-- samples, endpoint margins, and interval-length bound under truncation.
-- Consequently this theorem needs no located/evaluable structure.
approximate-IVT∥∥ :
  {a b : ℝᶜ} →
  (a≤b : a ≤ᶜ b) →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  isUniformlyContinuousOnInterval a b f →
  (targetPrecision : ℚ⁺) →
  f (leftEndpoint {a = a} {b = b} a≤b) <ᶜ 0ᶜ →
  0ᶜ <ᶜ f (rightEndpoint {a = a} {b = b} a≤b) →
  ∥ Σ[ x ∈ [ a , b ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
approximate-IVT∥∥ {a = a} {b = b}
    a≤b f uc targetPrecision leftNegative rightPositive =
  Prop.rec squash₁ gapStep (merely-boundedᶜ (gapᶜ a b))
  where
  gapStep :
    Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ (gapᶜ a b) →
    ∥ Σ[ x ∈ [ a , b ]ᶜ ]
        absᶜ (f x) <ᶜ rational (radius targetPrecision) ∥₁
  gapStep (κ , gap-bound) =
    Proofs.approximate-IVT∥∥-with-gap-bound
      a≤b
      κ
      gap-bound
      f
      uc
      targetPrecision
      leftNegative
      rightPositive

-- Bishop-style explicit approximate IVT.  The result is a concrete x in
-- [ a , b ] with | f x | < targetPrecision, not merely truncated existence.
-- Producing such an x requires actual finite-grid sample values and actual
-- rational margins.  Therefore the endpoints are located and f is a LocatedMap,
-- so every sampled value and endpoint value has an untruncated locator.  The
-- separate uniform-continuity hypothesis controls the error transferred across
-- adjacent grid points.
approximate-IVTΣ :
  {a b : ℝᶜ} →
  Locator a →
  Locator b →
  (a≤b : a ≤ᶜ b) →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (located : LocatedMap f) →
  (uc : isUniformlyContinuousOnInterval a b f) →
  (targetPrecision : ℚ⁺) →
  f (leftEndpoint {a = a} {b = b} a≤b) <ᶜ 0ᶜ →
  0ᶜ <ᶜ f (rightEndpoint {a = a} {b = b} a≤b) →
  Σ[ x ∈ [ a , b ]ᶜ ] absᶜ (f x) <ᶜ rational (radius targetPrecision)
approximate-IVTΣ {a = a} {b = b}
    loc-a loc-b a≤b f located uc targetPrecision
    leftNegative rightPositive =
  Proofs.approximate-IVTΣ-with-locators
    {a = a}
    {b = b}
    loc-a
    loc-b
    a≤b
    f
    (locatedIVTFunctionData {a = a} {b = b} {f = f} located uc)
    (located (leftEndpoint {a = a} {b = b} a≤b))
    (located (rightEndpoint {a = a} {b = b} a≤b))
    targetPrecision
    leftNegative
    rightPositive
