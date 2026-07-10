{-

Bounded multiplication interface for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.CauchyReals.Arithmetic.Internal.BoundedMultiplication where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarOrder
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Extension
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Data.PositiveRationals
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace


private
  upperBoundℚ :
    (κ : ℚ⁺) (q : ℚ) →
    RationalBoundᶜ κ q →
    q ℚOrder.< radius κ
  upperBoundℚ κ q =
    upperℚ {κ = κ} {q = q}

  lowerBoundℚ :
    (κ : ℚ⁺) (q : ℚ) →
    RationalBoundᶜ κ q →
    ℚ.- q ℚOrder.< radius κ
  lowerBoundℚ κ q =
    lowerℚ {κ = κ} {q = q}

  upperClosedBoundℚ :
    (κ : ℚ⁺) (q : ℚ) →
    RationalClosedBoundᶜ κ q →
    q ℚOrder.≤ radius κ
  upperClosedBoundℚ κ q =
    upper≤ℚ {κ = κ} {q = q}

  lowerClosedBoundℚ :
    (κ : ℚ⁺) (q : ℚ) →
    RationalClosedBoundᶜ κ q →
    ℚ.- q ℚOrder.≤ radius κ
  lowerClosedBoundℚ κ q =
    lower≤ℚ {κ = κ} {q = q}

  diff-close-zero→close :
    {x y : ℝᶜ} {ε : ℚ⁺} →
    (x +ᶜ (-ᶜ y)) ∼[ ε ] 0ᶜ →
    x ∼[ ε ] y
  diff-close-zero→close {x = x} {y = y} {ε = ε} diff∼0 =
    subst2
      (λ u v → u ∼[ ε ] v)
      (minus-plus-cancel-right x y)
      (add-zero-left y)
      (add-close-left diff∼0 y)


boundedMul-rational-leftᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  RationalBoundᶜ κ q →
  ℝᶜ → ℝᶜ
boundedMul-rational-leftᶜ κ q bound =
  boundedScalarMulᶜ q κ (upperBoundℚ κ q bound) (lowerBoundℚ κ q bound)


boundedMul-rational-leftᶜ-rational :
  (κ : ℚ⁺) (q r : ℚ) →
  (bound : RationalBoundᶜ κ q) →
  boundedMul-rational-leftᶜ κ q bound (rational r) ≡
  rational (q ℚ.· r)
boundedMul-rational-leftᶜ-rational κ q r bound =
  boundedScalarMulᶜ-rational q κ (upperBoundℚ κ q bound) (lowerBoundℚ κ q bound) r


boundedMul-rational-leftᶜ-close :
  (κ : ℚ⁺) (q : ℚ) →
  (bound : RationalBoundᶜ κ q) →
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  boundedMul-rational-leftᶜ κ q bound x
    ∼[ κ *⁺ ε ]
  boundedMul-rational-leftᶜ κ q bound y
boundedMul-rational-leftᶜ-close κ q bound =
  boundedScalarMulᶜ-close q κ (upperBoundℚ κ q bound) (lowerBoundℚ κ q bound)


scalarMulᶜ-close-rational-bound :
  (q : ℚ) (κ : ℚ⁺) →
  RationalBoundᶜ κ q →
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  scalarMulᶜ q x ∼[ κ *⁺ ε ] scalarMulᶜ q y
scalarMulᶜ-close-rational-bound q κ bound {x = x} {y = y} x∼y =
  subst2
    (λ u v → u ∼[ _ ] v)
    (sym scalar≡bounded-x)
    (sym scalar≡bounded-y)
    (boundedMul-rational-leftᶜ-close κ q bound x∼y)
  where
  scalar≡bounded-x :
    scalarMulᶜ q x ≡ boundedMul-rational-leftᶜ κ q bound x
  scalar≡bounded-x =
    boundedScalarMulᶜ-bound-independent
      q
      (scalar-bound q)
      κ
      (scalar-bound-upper q)
      (scalar-bound-lower q)
      (upperBoundℚ κ q bound)
      (lowerBoundℚ κ q bound)
      x

  scalar≡bounded-y :
    scalarMulᶜ q y ≡ boundedMul-rational-leftᶜ κ q bound y
  scalar≡bounded-y =
    boundedScalarMulᶜ-bound-independent
      q
      (scalar-bound q)
      κ
      (scalar-bound-upper q)
      (scalar-bound-lower q)
      (upperBoundℚ κ q bound)
      (lowerBoundℚ κ q bound)
      y


boundedMul-rational-leftᶜ-lipschitz :
  (κ : ℚ⁺) (q : ℚ) →
  (bound : RationalBoundᶜ κ q) →
  IsLipschitz CauchyRealsMetricSpace CauchyRealsMetricSpace (boundedMul-rational-leftᶜ κ q bound)
boundedMul-rational-leftᶜ-lipschitz κ q bound =
  boundedScalarMulᶜ-lipschitz q κ (upperBoundℚ κ q bound) (lowerBoundℚ κ q bound)


boundedMul-rational-leftᶜ-continuous :
  (κ : ℚ⁺) (q : ℚ) →
  (bound : RationalBoundᶜ κ q) →
  IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (boundedMul-rational-leftᶜ κ q bound)
boundedMul-rational-leftᶜ-continuous κ q bound =
  boundedScalarMulᶜ-continuous q κ (upperBoundℚ κ q bound) (lowerBoundℚ κ q bound)


boundedMul-rational-leftᶜ-bound-independent :
  (κ μ : ℚ⁺) (q : ℚ)
  (κ-bound : RationalBoundᶜ κ q)
  (μ-bound : RationalBoundᶜ μ q)
  (x : ℝᶜ) →
  boundedMul-rational-leftᶜ κ q κ-bound x ≡
  boundedMul-rational-leftᶜ μ q μ-bound x
boundedMul-rational-leftᶜ-bound-independent κ μ q κ-bound μ-bound =
  boundedScalarMulᶜ-bound-independent
    q
    κ
    μ
    (upperBoundℚ κ q κ-bound)
    (lowerBoundℚ κ q κ-bound)
    (upperBoundℚ μ q μ-bound)
    (lowerBoundℚ μ q μ-bound)


boundedMul-rational-leftᶜ-distrib-real-add :
  (κ : ℚ⁺) (q : ℚ) (bound : RationalBoundᶜ κ q)
  (x y : ℝᶜ) →
  boundedMul-rational-leftᶜ κ q bound (x +ᶜ y) ≡
  boundedMul-rational-leftᶜ κ q bound x +ᶜ
  boundedMul-rational-leftᶜ κ q bound y
boundedMul-rational-leftᶜ-distrib-real-add κ q bound =
  boundedScalarMulᶜ-distrib-real-add
    q
    κ
    (upperBoundℚ κ q bound)
    (lowerBoundℚ κ q bound)


boundedMul-rational-leftᶜ-zero-right :
  (κ : ℚ⁺) (q : ℚ) (bound : RationalBoundᶜ κ q) →
  boundedMul-rational-leftᶜ κ q bound 0ᶜ ≡ 0ᶜ
boundedMul-rational-leftᶜ-zero-right κ q bound =
  boundedScalarMulᶜ-zero-right
    q
    κ
    (upperBoundℚ κ q bound)
    (lowerBoundℚ κ q bound)


boundedMul-rational-leftᶜ-zero-left :
  (κ : ℚ⁺) (bound : RationalBoundᶜ κ 0ℚ) (x : ℝᶜ) →
  boundedMul-rational-leftᶜ κ 0ℚ bound x ≡ 0ᶜ
boundedMul-rational-leftᶜ-zero-left κ bound =
  boundedScalarMulᶜ-zero-scalar
    κ
    (upperBoundℚ κ 0ℚ bound)
    (lowerBoundℚ κ 0ℚ bound)


boundedMul-rational-leftᶜ-neg-real :
  (κ : ℚ⁺) (q : ℚ) (bound : RationalBoundᶜ κ q)
  (x : ℝᶜ) →
  boundedMul-rational-leftᶜ κ q bound (-ᶜ x) ≡
  -ᶜ (boundedMul-rational-leftᶜ κ q bound x)
boundedMul-rational-leftᶜ-neg-real κ q bound =
  boundedScalarMulᶜ-neg-real
    q
    κ
    (upperBoundℚ κ q bound)
    (lowerBoundℚ κ q bound)


boundedMul-rational-leftᶜ-neg-left :
  (κ : ℚ⁺) (q : ℚ) (bound : RationalBoundᶜ κ q)
  (x : ℝᶜ) →
  boundedMul-rational-leftᶜ κ (ℚ.- q) (rational-boundᶜ-neg κ q bound) x ≡
  -ᶜ (boundedMul-rational-leftᶜ κ q bound x)
boundedMul-rational-leftᶜ-neg-left κ q bound =
  boundedScalarMulᶜ-neg-scalar
    q
    κ
    (upperBoundℚ κ q bound)
    (lowerBoundℚ κ q bound)
    (lowerBoundℚ κ (ℚ.- q) (rational-boundᶜ-neg κ q bound))


RationalRightMultiplierᶜ :
  ℚ⁺ →
  ℝᶜ →
  Type₀
RationalRightMultiplierᶜ κ x =
  IsRationalLipschitzWithᶜ κ (λ q → scalarMulᶜ q x)


scalarMulᶜ-diff :
  (q r : ℚ) (x : ℝᶜ) →
  scalarMulᶜ (q ℚ.- r) x ≡
  scalarMulᶜ q x +ᶜ (-ᶜ (scalarMulᶜ r x))
scalarMulᶜ-diff q r x =
  scalarMulᶜ-distrib-scalar-add q (ℚ.- r) x ∙
  cong (scalarMulᶜ q x +ᶜ_) (scalarMulᶜ-neg-scalar r x)


bounded-real-right-multiplierᶜ :
  (κ : ℚ⁺) (x : ℝᶜ) →
  BoundedByᶜ κ x →
  RationalRightMultiplierᶜ κ x
bounded-real-right-multiplierᶜ κ x x-bound q r ε q∼r =
  diff-close-zero→close
    (subst
      (λ y → y ∼[ κ *⁺ ε ] 0ᶜ)
      (scalarMulᶜ-diff q r x)
      (bounded-small-scalar-close-zeroᶜ
        κ
        x
        x-bound
        (q ℚ.- r)
        ε
        (rational-diff-boundᶜ q r ε q∼r)))


boundedMul-leftᶜ :
  (κ : ℚ⁺) (x : ℝᶜ) →
  BoundedByᶜ κ x →
  RationalRightMultiplierᶜ κ x →
  ℝᶜ → ℝᶜ
boundedMul-leftᶜ κ x x-bound x-lip =
  extendRationalLipschitzWithᶜ κ (λ q → scalarMulᶜ q x) x-lip


boundedMul-leftᶜ-rational :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x)
  (q : ℚ) →
  boundedMul-leftᶜ κ x x-bound x-lip (rational q) ≡
  scalarMulᶜ q x
boundedMul-leftᶜ-rational κ x x-bound x-lip q =
  refl


boundedMul-leftᶜ-close :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x) →
  {y z : ℝᶜ} {ε : ℚ⁺} →
  y ∼[ ε ] z →
  boundedMul-leftᶜ κ x x-bound x-lip y
    ∼[ κ *⁺ ε ]
  boundedMul-leftᶜ κ x x-bound x-lip z
boundedMul-leftᶜ-close κ x x-bound x-lip =
  extendRationalLipschitzWithᶜ-close
    κ
    (λ q → scalarMulᶜ q x)
    x-lip


boundedMul-leftᶜ-lipschitz :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x) →
  IsLipschitz CauchyRealsMetricSpace CauchyRealsMetricSpace (boundedMul-leftᶜ κ x x-bound x-lip)
boundedMul-leftᶜ-lipschitz κ x x-bound x-lip =
  extendRationalLipschitzWithᶜ-lipschitz
    κ
    (λ q → scalarMulᶜ q x)
    x-lip


boundedMul-leftᶜ-continuous :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x) →
  IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (boundedMul-leftᶜ κ x x-bound x-lip)
boundedMul-leftᶜ-continuous κ x x-bound x-lip =
  extendRationalLipschitzWithᶜ-continuous
    κ
    (λ q → scalarMulᶜ q x)
    x-lip


boundedMul-leftᶜ-bound-independent :
  (κ μ : ℚ⁺) (x : ℝᶜ)
  (κ-bound : BoundedByᶜ κ x)
  (μ-bound : BoundedByᶜ μ x)
  (κ-lip : RationalRightMultiplierᶜ κ x)
  (μ-lip : RationalRightMultiplierᶜ μ x)
  (y : ℝᶜ) →
  boundedMul-leftᶜ κ x κ-bound κ-lip y ≡
  boundedMul-leftᶜ μ x μ-bound μ-lip y
boundedMul-leftᶜ-bound-independent κ μ x κ-bound μ-bound κ-lip μ-lip =
  continuous-equal
    (boundedMul-leftᶜ κ x κ-bound κ-lip)
    (boundedMul-leftᶜ μ x μ-bound μ-lip)
    (boundedMul-leftᶜ-continuous κ x κ-bound κ-lip)
    (boundedMul-leftᶜ-continuous μ x μ-bound μ-lip)
    (λ _ → refl)


boundedMul-leftᶜ-zero-right :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x) →
  boundedMul-leftᶜ κ x x-bound x-lip 0ᶜ ≡ 0ᶜ
boundedMul-leftᶜ-zero-right κ x x-bound x-lip =
  scalarMulᶜ-zero x


boundedMul-leftᶜ-zero-left :
  (κ : ℚ⁺)
  (0-bound : BoundedByᶜ κ 0ᶜ)
  (0-lip : RationalRightMultiplierᶜ κ 0ᶜ)
  (y : ℝᶜ) →
  boundedMul-leftᶜ κ 0ᶜ 0-bound 0-lip y ≡ 0ᶜ
boundedMul-leftᶜ-zero-left κ 0-bound 0-lip =
  continuous-constant-equal
    (boundedMul-leftᶜ κ 0ᶜ 0-bound 0-lip)
    0ᶜ
    (boundedMul-leftᶜ-continuous κ 0ᶜ 0-bound 0-lip)
    (λ q → scalarMulᶜ-zero-right q)


boundedMul-leftᶜ-neg-right :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x)
  (y : ℝᶜ) →
  boundedMul-leftᶜ κ x x-bound x-lip (-ᶜ y) ≡
  -ᶜ (boundedMul-leftᶜ κ x x-bound x-lip y)
boundedMul-leftᶜ-neg-right κ x x-bound x-lip =
  continuous-equal
    (λ y → boundedMul-leftᶜ κ x x-bound x-lip (-ᶜ y))
    (λ y → -ᶜ (boundedMul-leftᶜ κ x x-bound x-lip y))
    (comp-uniformlyContinuous {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
      (boundedMul-leftᶜ-continuous κ x x-bound x-lip)
      neg-continuous)
    (comp-uniformlyContinuous {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
      neg-continuous
      (boundedMul-leftᶜ-continuous κ x x-bound x-lip))
    (λ q → scalarMulᶜ-neg-scalar q x)


boundedMul-leftᶜ-distrib-real-add-rational-left :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x)
  (q : ℚ) (y : ℝᶜ) →
  boundedMul-leftᶜ κ x x-bound x-lip (rational q +ᶜ y) ≡
  scalarMulᶜ q x +ᶜ boundedMul-leftᶜ κ x x-bound x-lip y
boundedMul-leftᶜ-distrib-real-add-rational-left κ x x-bound x-lip q =
  continuous-equal
    (λ y → boundedMul-leftᶜ κ x x-bound x-lip (rational q +ᶜ y))
    (λ y → scalarMulᶜ q x +ᶜ boundedMul-leftᶜ κ x x-bound x-lip y)
    (comp-uniformlyContinuous {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
      (boundedMul-leftᶜ-continuous κ x x-bound x-lip)
      (add-continuous-right (rational q)))
    (comp-uniformlyContinuous {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
      (add-continuous-right (scalarMulᶜ q x))
      (boundedMul-leftᶜ-continuous κ x x-bound x-lip))
    (λ r → scalarMulᶜ-distrib-scalar-add q r x)


boundedMul-leftᶜ-distrib-real-add :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x)
  (y z : ℝᶜ) →
  boundedMul-leftᶜ κ x x-bound x-lip (y +ᶜ z) ≡
  boundedMul-leftᶜ κ x x-bound x-lip y +ᶜ
  boundedMul-leftᶜ κ x x-bound x-lip z
boundedMul-leftᶜ-distrib-real-add κ x x-bound x-lip y z =
  continuous-equal
    (λ w → boundedMul-leftᶜ κ x x-bound x-lip (w +ᶜ z))
    (λ w →
      boundedMul-leftᶜ κ x x-bound x-lip w +ᶜ
      boundedMul-leftᶜ κ x x-bound x-lip z)
    (comp-uniformlyContinuous {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
      (boundedMul-leftᶜ-continuous κ x x-bound x-lip)
      (add-continuous-left z))
    (comp-uniformlyContinuous {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
      (add-continuous-left (boundedMul-leftᶜ κ x x-bound x-lip z))
      (boundedMul-leftᶜ-continuous κ x x-bound x-lip))
    (λ q → boundedMul-leftᶜ-distrib-real-add-rational-left κ x x-bound x-lip q z)
    y


boundedMulᶜ :
  (κ : ℚ⁺) (x : ℝᶜ) →
  BoundedByᶜ κ x →
  ℝᶜ → ℝᶜ
boundedMulᶜ κ x x-bound =
  boundedMul-leftᶜ
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


boundedMulᶜ-rational :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (q : ℚ) →
  boundedMulᶜ κ x x-bound (rational q) ≡
  scalarMulᶜ q x
boundedMulᶜ-rational κ x x-bound =
  boundedMul-leftᶜ-rational
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


boundedMulᶜ-close :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x) →
  {y z : ℝᶜ} {ε : ℚ⁺} →
  y ∼[ ε ] z →
  boundedMulᶜ κ x x-bound y
    ∼[ κ *⁺ ε ]
  boundedMulᶜ κ x x-bound z
boundedMulᶜ-close κ x x-bound =
  boundedMul-leftᶜ-close
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


boundedMulᶜ-lipschitz :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x) →
  IsLipschitz CauchyRealsMetricSpace CauchyRealsMetricSpace (boundedMulᶜ κ x x-bound)
boundedMulᶜ-lipschitz κ x x-bound =
  boundedMul-leftᶜ-lipschitz
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


boundedMulᶜ-continuous :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x) →
  IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (boundedMulᶜ κ x x-bound)
boundedMulᶜ-continuous κ x x-bound =
  boundedMul-leftᶜ-continuous
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


boundedMulᶜ-bound-independent :
  (κ μ : ℚ⁺) (x : ℝᶜ)
  (κ-bound : BoundedByᶜ κ x)
  (μ-bound : BoundedByᶜ μ x)
  (y : ℝᶜ) →
  boundedMulᶜ κ x κ-bound y ≡
  boundedMulᶜ μ x μ-bound y
boundedMulᶜ-bound-independent κ μ x κ-bound μ-bound =
  boundedMul-leftᶜ-bound-independent
    κ
    μ
    x
    κ-bound
    μ-bound
    (bounded-real-right-multiplierᶜ κ x κ-bound)
    (bounded-real-right-multiplierᶜ μ x μ-bound)


boundedMulᶜ-zero-right :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x) →
  boundedMulᶜ κ x x-bound 0ᶜ ≡ 0ᶜ
boundedMulᶜ-zero-right κ x x-bound =
  boundedMul-leftᶜ-zero-right
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


boundedMulᶜ-zero-left :
  (κ : ℚ⁺)
  (0-bound : BoundedByᶜ κ 0ᶜ)
  (y : ℝᶜ) →
  boundedMulᶜ κ 0ᶜ 0-bound y ≡ 0ᶜ
boundedMulᶜ-zero-left κ 0-bound =
  boundedMul-leftᶜ-zero-left
    κ
    0-bound
    (bounded-real-right-multiplierᶜ κ 0ᶜ 0-bound)


boundedMulᶜ-neg-right :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (y : ℝᶜ) →
  boundedMulᶜ κ x x-bound (-ᶜ y) ≡
  -ᶜ (boundedMulᶜ κ x x-bound y)
boundedMulᶜ-neg-right κ x x-bound =
  boundedMul-leftᶜ-neg-right
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


boundedMulᶜ-distrib-real-add :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (y z : ℝᶜ) →
  boundedMulᶜ κ x x-bound (y +ᶜ z) ≡
  boundedMulᶜ κ x x-bound y +ᶜ
  boundedMulᶜ κ x x-bound z
boundedMulᶜ-distrib-real-add κ x x-bound =
  boundedMul-leftᶜ-distrib-real-add
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


rational-right-multiplier-closedᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  RationalClosedBoundᶜ κ q →
  RationalRightMultiplierᶜ κ (rational q)
rational-right-multiplier-closedᶜ κ q bound r s ε r∼s =
  subst2
    (λ a b → rational a ∼[ κ *⁺ ε ] rational b)
    (ℚ.·Comm q r)
    (ℚ.·Comm q s)
    (point-point-close
      (q ℚ.· r)
      (q ℚ.· s)
      (κ *⁺ ε)
      (scale-close-closed-bound
        q
        κ
        (upperClosedBoundℚ κ q bound)
        (lowerClosedBoundℚ κ q bound)
        r
        s
        ε
        r∼s))


rational-right-multiplierᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  RationalBoundᶜ κ q →
  RationalRightMultiplierᶜ κ (rational q)
rational-right-multiplierᶜ κ q bound =
  rational-right-multiplier-closedᶜ
    κ
    q
    (rational-bound→closedᶜ κ q bound)


rational-right-multiplier-from-boundedᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  (bound : BoundedByᶜ κ (rational q)) →
  RationalRightMultiplierᶜ κ (rational q)
rational-right-multiplier-from-boundedᶜ κ q bound =
  rational-right-multiplier-closedᶜ
    κ
    q
    (bounded-rational→closed-boundᶜ κ q bound)


boundedMul-leftᶜ-rational-left-from-bounded :
  (κ : ℚ⁺) (q : ℚ)
  (bound : BoundedByᶜ κ (rational q))
  (q-lip : RationalRightMultiplierᶜ κ (rational q))
  (y : ℝᶜ) →
  boundedMul-leftᶜ κ (rational q) bound q-lip y ≡
  scalarMulᶜ q y
boundedMul-leftᶜ-rational-left-from-bounded κ q bound q-lip =
  continuous-equal
    (boundedMul-leftᶜ κ (rational q) bound q-lip)
    (scalarMulᶜ q)
    (boundedMul-leftᶜ-continuous κ (rational q) bound q-lip)
    (scalarMulᶜ-continuous q)
    rational-path
  where
  rational-path :
    (r : ℚ) →
    boundedMul-leftᶜ κ (rational q) bound q-lip (rational r) ≡
    scalarMulᶜ q (rational r)
  rational-path r =
    boundedMul-leftᶜ-rational κ (rational q) bound q-lip r ∙
    scalarMulᶜ-rational r q ∙
    cong rational (ℚ.·Comm r q) ∙
    sym (scalarMulᶜ-rational q r)


boundedMulᶜ-rational-left-from-bounded :
  (κ : ℚ⁺) (q : ℚ)
  (bound : BoundedByᶜ κ (rational q))
  (y : ℝᶜ) →
  boundedMulᶜ κ (rational q) bound y ≡
  scalarMulᶜ q y
boundedMulᶜ-rational-left-from-bounded κ q bound =
  boundedMul-leftᶜ-rational-left-from-bounded
    κ
    q
    bound
    (bounded-real-right-multiplierᶜ κ (rational q) bound)


boundedMul-leftᶜ-rational-left :
  (κ : ℚ⁺) (q : ℚ) (bound : RationalBoundᶜ κ q)
  (y : ℝᶜ) →
  boundedMul-leftᶜ
    κ
    (rational q)
    (rational-bound→boundedᶜ κ q bound)
    (rational-right-multiplierᶜ κ q bound)
    y ≡
  boundedMul-rational-leftᶜ κ q bound y
boundedMul-leftᶜ-rational-left κ q bound =
  continuous-equal
    (boundedMul-leftᶜ
      κ
      (rational q)
      (rational-bound→boundedᶜ κ q bound)
      (rational-right-multiplierᶜ κ q bound))
    (boundedMul-rational-leftᶜ κ q bound)
    (boundedMul-leftᶜ-continuous
      κ
      (rational q)
      (rational-bound→boundedᶜ κ q bound)
      (rational-right-multiplierᶜ κ q bound))
    (boundedMul-rational-leftᶜ-continuous κ q bound)
    (λ r → cong rational (ℚ.·Comm r q))
