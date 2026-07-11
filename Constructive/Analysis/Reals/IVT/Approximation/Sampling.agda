{-

Sampling functions on finite interval grids

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.IVT.Approximation.Sampling where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Completions.CauchyCompletion.Metric
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Density
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.Interval.Base
open import Constructive.Analysis.Reals.Interval.Grid.Base
open import Constructive.Analysis.Reals.IVT.Approximation.GridSearch
open import Constructive.Analysis.Reals.IVT.Uniform
open import Constructive.Data.PositiveRationals
open import Constructive.Data.Rationals.Closeness
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open MetricSpaceOf RationalsMetricSpace using (pointReflecting)


private
  neg-nonpositiveℚ :
    {q : ℚ} →
    0ℚ ℚOrder.≤ q →
    ℚ.- q ℚOrder.≤ 0ℚ
  neg-nonpositiveℚ {q = q} 0≤q =
    subst2
      ℚOrder._≤_
      (ℚ.+IdL (ℚ.- q))
      (ℚ.+InvR q)
      (ℚOrder.≤-+o 0ℚ q (ℚ.- q) 0≤q)

  bounded-byᶜ→abs≤ :
    (κ : ℚ⁺) →
    (x : ℝᶜ) →
    BoundedByᶜ κ x →
    absᶜ x ≤ᶜ rational (radius κ)
  bounded-byᶜ→abs≤ κ x bound =
    absᶜ-least
      x
      (rational (radius κ))
      (≤ℚ→rational≤ᶜ
        {q = 0ℚ}
        {r = radius κ}
        (Rational.<→≤
          {p = 0ℚ}
          {q = radius κ}
          (κ .snd)))
      (upperᶜ {κ = κ} {x = x} bound)
      (lowerᶜ {κ = κ} {x = x} bound)


nonnegativeSmallCloseBounded :
  (x : ℝᶜ) →
  (q : ℚ) →
  (samplePrecision boundPrecision smallPrecision : ℚ⁺) →
  samplePrecision <⁺ boundPrecision →
  0ℚ ℚOrder.≤ q →
  q ℚOrder.< radius smallPrecision →
  x ∼[ samplePrecision ] rational q →
  BoundedByᶜ (smallPrecision +⁺ boundPrecision) x
nonnegativeSmallCloseBounded x q samplePrecision boundPrecision smallPrecision
    sample<bound 0≤q q<small x∼q =
  bounded-byᶜ
    {κ = smallPrecision +⁺ boundPrecision}
    {x = x}
    upperBounded
    lowerBounded
  where
  x≤q+bound : x ≤ᶜ rational (q ℚ.+ radius boundPrecision)
  x≤q+bound =
    close-rational-upper-bound
      x
      q
      samplePrecision
      boundPrecision
      sample<bound
      x∼q

  q+bound≤small+bound :
    q ℚ.+ radius boundPrecision ℚOrder.≤
    radius (smallPrecision +⁺ boundPrecision)
  q+bound≤small+bound =
    ℚOrder.≤-+o
      q
      (radius smallPrecision)
      (radius boundPrecision)
      (Rational.<→≤
        {p = q}
        {q = radius smallPrecision}
        q<small)

  upperBounded : x ≤ᶜ rational (radius (smallPrecision +⁺ boundPrecision))
  upperBounded =
    ≤ᶜ-trans
      {x = x}
      {y = rational (q ℚ.+ radius boundPrecision)}
      {z = rational (radius (smallPrecision +⁺ boundPrecision))}
      x≤q+bound
      (≤ℚ→rational≤ᶜ q+bound≤small+bound)

  -x≤-q+bound :
    (-ᶜ x) ≤ᶜ rational ((ℚ.- q) ℚ.+ radius boundPrecision)
  -x≤-q+bound =
    close-rational-upper-bound
      (-ᶜ x)
      (ℚ.- q)
      samplePrecision
      boundPrecision
      sample<bound
      (neg-close x∼q)

  -q≤small : ℚ.- q ℚOrder.≤ radius smallPrecision
  -q≤small =
    Rational.≤-trans
      {p = ℚ.- q}
      {q = 0ℚ}
      {r = radius smallPrecision}
      (neg-nonpositiveℚ {q = q} 0≤q)
      (Rational.<→≤
        {p = 0ℚ}
        {q = radius smallPrecision}
        (smallPrecision .snd))

  -q+bound≤small+bound :
    (ℚ.- q) ℚ.+ radius boundPrecision ℚOrder.≤
    radius (smallPrecision +⁺ boundPrecision)
  -q+bound≤small+bound =
    ℚOrder.≤-+o
      (ℚ.- q)
      (radius smallPrecision)
      (radius boundPrecision)
      -q≤small

  lowerBounded : (-ᶜ x) ≤ᶜ rational (radius (smallPrecision +⁺ boundPrecision))
  lowerBounded =
    ≤ᶜ-trans
      {x = -ᶜ x}
      {y = rational ((ℚ.- q) ℚ.+ radius boundPrecision)}
      {z = rational (radius (smallPrecision +⁺ boundPrecision))}
      -x≤-q+bound
      (≤ℚ→rational≤ᶜ -q+bound≤small+bound)


sampleValue :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
  IVTFunctionData a b f →
  (x : [ a , b ]ᶜ) →
  ℚ⁺ →
  ℚ
sampleValue {a = a} {b = b} {f = f} ivtData x ε =
  approximateValue {a = a} {b = b} {f = f} ivtData x ε .fst


sampleValueClose :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
  (ivtData : IVTFunctionData a b f) →
  (x : [ a , b ]ᶜ) →
  (ε : ℚ⁺) →
  f x ∼[ ε ] rational
    (sampleValue {a = a} {b = b} {f = f} ivtData x ε)
sampleValueClose {a = a} {b = b} {f = f} ivtData x ε =
  approximateValue {a = a} {b = b} {f = f} ivtData x ε .snd


gridSampleValues :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  IVTFunctionData a b f →
  {n : ℕ} →
  Grid a b a≤b n →
  ℚ⁺ →
  Fin (suc n) →
  ℚ
gridSampleValues {a = a} {b = b} {f = f} ivtData G ε i =
  sampleValue {a = a} {b = b} {f = f} ivtData (Grid.point G i) ε


gridSampleClose :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b n) →
  (ε : ℚ⁺) →
  (i : Fin (suc n)) →
  f (Grid.point G i) ∼[ ε ] rational
    (gridSampleValues {a = a} {b = b} {f = f} ivtData G ε i)
gridSampleClose {a = a} {b = b} {f = f} ivtData G ε i =
  sampleValueClose {a = a} {b = b} {f = f}
    ivtData
    (Grid.point G i)
    ε


ApproxValues :
  {n : ℕ} →
  (Fin n → ℝᶜ) →
  ℚ⁺ →
  Type₀
ApproxValues {n = n} points ε =
  Σ[ values ∈ (Fin n → ℚ) ]
    ((i : Fin n) → points i ∼[ ε ] rational (values i))


approxValues∥∥ :
  {n : ℕ} →
  (points : Fin n → ℝᶜ) →
  (ε : ℚ⁺) →
  ∥ ApproxValues points ε ∥₁
approxValues∥∥ {n = zero} points ε =
  ∣ (λ ()) , (λ ()) ∣₁
approxValues∥∥ {n = suc n} points ε =
  Prop.rec2 squash₁ combine
    (rational-approximation (points Fin.zero) ε)
    (approxValues∥∥ (λ i → points (Fin.suc i)) ε)
  where
  combine :
    Σ[ q ∈ ℚ ] points Fin.zero ∼[ ε ] rational q →
    ApproxValues (λ i → points (Fin.suc i)) ε →
    ∥ ApproxValues points ε ∥₁
  combine (q , point∼q) (tailValues , tailClose) =
    ∣ values , valuesClose ∣₁
    where
    values : Fin (suc n) → ℚ
    values Fin.zero =
      q
    values (Fin.suc i) =
      tailValues i

    valuesClose :
      (i : Fin (suc n)) →
      points i ∼[ ε ] rational (values i)
    valuesClose Fin.zero =
      point∼q
    valuesClose (Fin.suc i) =
      tailClose i


gridApproxValues∥∥ :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  {n : ℕ} →
  (G : Grid a b a≤b n) →
  (ε : ℚ⁺) →
  ∥ ApproxValues (λ i → f (Grid.point G i)) ε ∥₁
gridApproxValues∥∥ {f = f} G ε =
  approxValues∥∥ (λ i → f (Grid.point G i)) ε


sampleNonnegativeSmallBounded :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b n) →
  (samplePrecision boundPrecision smallPrecision : ℚ⁺) →
  samplePrecision <⁺ boundPrecision →
  (i : Fin (suc n)) →
  NonnegativeSmall
    (gridSampleValues {a = a} {b = b} {f = f} ivtData G samplePrecision)
    smallPrecision
    i →
  BoundedByᶜ
    (smallPrecision +⁺ boundPrecision)
    (f (Grid.point G i))
sampleNonnegativeSmallBounded {a = a} {b = b} {f = f} ivtData G
    samplePrecision boundPrecision smallPrecision sample<bound i (0≤q , q<small) =
  nonnegativeSmallCloseBounded
    (f (Grid.point G i))
    (gridSampleValues {a = a} {b = b} {f = f} ivtData G samplePrecision i)
    samplePrecision
    boundPrecision
    smallPrecision
    sample<bound
    0≤q
    q<small
    (gridSampleClose {a = a} {b = b} {f = f} ivtData G samplePrecision i)


sampleNonnegativeSmallAbs< :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b n) →
  (samplePrecision boundPrecision smallPrecision targetPrecision : ℚ⁺) →
  samplePrecision <⁺ boundPrecision →
  smallPrecision +⁺ boundPrecision <⁺ targetPrecision →
  (i : Fin (suc n)) →
  NonnegativeSmall
    (gridSampleValues {a = a} {b = b} {f = f} ivtData G samplePrecision)
    smallPrecision
    i →
  absᶜ (f (Grid.point G i)) <ᶜ rational (radius targetPrecision)
sampleNonnegativeSmallAbs< {a = a} {b = b} {f = f} ivtData G samplePrecision
    boundPrecision smallPrecision targetPrecision sample<bound small+bound<target
    i smallAt =
  ≤ᶜ-<ᶜ-trans
    (absᶜ (f (Grid.point G i)))
    (rational (radius (smallPrecision +⁺ boundPrecision)))
    (rational (radius targetPrecision))
    (bounded-byᶜ→abs≤
      (smallPrecision +⁺ boundPrecision)
      (f (Grid.point G i))
      (sampleNonnegativeSmallBounded
        {a = a}
        {b = b}
        {f = f}
        ivtData
        G
        samplePrecision
        boundPrecision
        smallPrecision
        sample<bound
        i
        smallAt))
    (<ℚ→<ᶜ
      {q = radius (smallPrecision +⁺ boundPrecision)}
      {r = radius targetPrecision}
      small+bound<target)


sampleNonnegativeSmallBoundedWithValues :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  {n : ℕ} →
  (G : Grid a b a≤b n) →
  (values : Fin (suc n) → ℚ) →
  (samplePrecision boundPrecision smallPrecision : ℚ⁺) →
  samplePrecision <⁺ boundPrecision →
  ((i : Fin (suc n)) →
    f (Grid.point G i) ∼[ samplePrecision ] rational (values i)) →
  (i : Fin (suc n)) →
  NonnegativeSmall values smallPrecision i →
  BoundedByᶜ
    (smallPrecision +⁺ boundPrecision)
    (f (Grid.point G i))
sampleNonnegativeSmallBoundedWithValues {f = f} G values
    samplePrecision boundPrecision smallPrecision sample<bound valuesClose
    i (0≤q , q<small) =
  nonnegativeSmallCloseBounded
    (f (Grid.point G i))
    (values i)
    samplePrecision
    boundPrecision
    smallPrecision
    sample<bound
    0≤q
    q<small
    (valuesClose i)


sampleNonnegativeSmallAbsWithValues< :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  {n : ℕ} →
  (G : Grid a b a≤b n) →
  (values : Fin (suc n) → ℚ) →
  (samplePrecision boundPrecision smallPrecision targetPrecision : ℚ⁺) →
  samplePrecision <⁺ boundPrecision →
  smallPrecision +⁺ boundPrecision <⁺ targetPrecision →
  ((i : Fin (suc n)) →
    f (Grid.point G i) ∼[ samplePrecision ] rational (values i)) →
  (i : Fin (suc n)) →
  NonnegativeSmall values smallPrecision i →
  absᶜ (f (Grid.point G i)) <ᶜ rational (radius targetPrecision)
sampleNonnegativeSmallAbsWithValues< {f = f} G values
    samplePrecision boundPrecision smallPrecision targetPrecision
    sample<bound small+bound<target valuesClose i smallAt =
  ≤ᶜ-<ᶜ-trans
    (absᶜ (f (Grid.point G i)))
    (rational (radius (smallPrecision +⁺ boundPrecision)))
    (rational (radius targetPrecision))
    (bounded-byᶜ→abs≤
      (smallPrecision +⁺ boundPrecision)
      (f (Grid.point G i))
      (sampleNonnegativeSmallBoundedWithValues
        {f = f}
        G
        values
        samplePrecision
        boundPrecision
        smallPrecision
        sample<bound
        valuesClose
        i
        smallAt))
    (<ℚ→<ᶜ
      {q = radius (smallPrecision +⁺ boundPrecision)}
      {r = radius targetPrecision}
      small+bound<target)


adjacentSampleValuesClose :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (samplePrecision movementPrecision : ℚ⁺) →
  AdjacentClose G
    (uniformModulus {a = a} {b = b} {f = f}
      (IVTFunctionData.uniformlyContinuous {a = a} {b = b} {f = f} ivtData)
      movementPrecision) →
  (i : Fin (suc n)) →
  AdjacentValuesClose
    (gridSampleValues {a = a} {b = b} {f = f} ivtData G samplePrecision)
    ((samplePrecision +⁺ movementPrecision) +⁺ samplePrecision)
    i
adjacentSampleValuesClose {a = a} {b = b} {a≤b = a≤b} {f = f} ivtData {n = n}
    G samplePrecision movementPrecision adjacentClose i =
  pointReflecting cauchy-close
  where
  left : Fin (suc (suc n))
  left =
    Fin.weakenFin i

  right : Fin (suc (suc n))
  right =
    Fin.suc i

  left-sample-close :
    f (Grid.point G left) ∼[ samplePrecision ]
    rational (gridSampleValues {a = a} {b = b} {f = f}
      ivtData G samplePrecision left)
  left-sample-close =
    gridSampleClose {a = a} {b = b} {f = f} ivtData G samplePrecision left

  right-sample-close :
    f (Grid.point G right) ∼[ samplePrecision ]
    rational (gridSampleValues {a = a} {b = b} {f = f}
      ivtData G samplePrecision right)
  right-sample-close =
    gridSampleClose {a = a} {b = b} {f = f} ivtData G samplePrecision right

  movement-close :
    f (Grid.point G left) ∼[ movementPrecision ] f (Grid.point G right)
  movement-close =
    uniformClose
      {a = a}
      {b = b}
      {f = f}
      (IVTFunctionData.uniformlyContinuous {a = a} {b = b} {f = f} ivtData)
      movementPrecision
      (adjacentClose i)

  cauchy-close :
    rational (gridSampleValues {a = a} {b = b} {f = f}
      ivtData G samplePrecision left)
      ∼[ (samplePrecision +⁺ movementPrecision) +⁺ samplePrecision ]
    rational (gridSampleValues {a = a} {b = b} {f = f}
      ivtData G samplePrecision right)
  cauchy-close =
    close-triangle
      (close-triangle (close-sym left-sample-close) movement-close)
      right-sample-close

adjacentSampleValuesCloseWithValues :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  (uc : isUniformlyContinuousOnInterval a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (samplePrecision movementPrecision : ℚ⁺) →
  AdjacentClose G
    (uniformModulus {a = a} {b = b} {f = f}
      uc
      movementPrecision) →
  (values : Fin (suc (suc n)) → ℚ) →
  ((i : Fin (suc (suc n))) →
    f (Grid.point G i) ∼[ samplePrecision ] rational (values i)) →
  (i : Fin (suc n)) →
  AdjacentValuesClose
    values
    ((samplePrecision +⁺ movementPrecision) +⁺ samplePrecision)
    i
adjacentSampleValuesCloseWithValues {a = a} {b = b} {a≤b = a≤b} {f = f}
    uc {n = n} G samplePrecision movementPrecision adjacentClose values
    valuesClose i =
  pointReflecting cauchy-close
  where
  left : Fin (suc (suc n))
  left =
    Fin.weakenFin i

  right : Fin (suc (suc n))
  right =
    Fin.suc i

  left-sample-close :
    f (Grid.point G left) ∼[ samplePrecision ]
    rational (values left)
  left-sample-close =
    valuesClose left

  right-sample-close :
    f (Grid.point G right) ∼[ samplePrecision ]
    rational (values right)
  right-sample-close =
    valuesClose right

  movement-close :
    f (Grid.point G left) ∼[ movementPrecision ] f (Grid.point G right)
  movement-close =
    uniformClose
      {a = a}
      {b = b}
      {f = f}
      uc
      movementPrecision
      (adjacentClose i)

  cauchy-close :
    rational (values left)
      ∼[ (samplePrecision +⁺ movementPrecision) +⁺ samplePrecision ]
    rational (values right)
  cauchy-close =
    close-triangle
      (close-triangle (close-sym left-sample-close) movement-close)
      right-sample-close
