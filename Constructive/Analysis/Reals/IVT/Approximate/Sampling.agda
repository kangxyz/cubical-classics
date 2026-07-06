{-

Sampling located functions on finite interval grids

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.IVT.Approximate.Sampling where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Completions.CauchyCompletion.MetricSpace
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.Interval
open import Constructive.Analysis.Reals.Interval.Grid
open import Constructive.Analysis.Reals.IVT.GridSearch
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
      (upperᶜ bound)
      (lowerᶜ bound)


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
  bounded-byᶜ upperBounded lowerBounded
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
sampleValue ivtData x ε =
  approximateValue ivtData x ε .fst


sampleValueClose :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
  (ivtData : IVTFunctionData a b f) →
  (x : [ a , b ]ᶜ) →
  (ε : ℚ⁺) →
  f x ∼[ ε ] rational (sampleValue ivtData x ε)
sampleValueClose ivtData x ε =
  approximateValue ivtData x ε .snd


gridSampleValues :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  IVTFunctionData a b f →
  {n : ℕ} →
  Grid a b a≤b n →
  ℚ⁺ →
  Fin (suc n) →
  ℚ
gridSampleValues ivtData G ε i =
  sampleValue ivtData (Grid.point G i) ε


gridSampleClose :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b n) →
  (ε : ℚ⁺) →
  (i : Fin (suc n)) →
  f (Grid.point G i) ∼[ ε ] rational (gridSampleValues ivtData G ε i)
gridSampleClose ivtData G ε i =
  sampleValueClose ivtData (Grid.point G i) ε


sampleNonnegativeSmallBounded :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b n) →
  (samplePrecision boundPrecision smallPrecision : ℚ⁺) →
  samplePrecision <⁺ boundPrecision →
  (i : Fin (suc n)) →
  NonnegativeSmall
    (gridSampleValues ivtData G samplePrecision)
    smallPrecision
    i →
  BoundedByᶜ
    (smallPrecision +⁺ boundPrecision)
    (f (Grid.point G i))
sampleNonnegativeSmallBounded {f = f} ivtData G samplePrecision boundPrecision smallPrecision
    sample<bound i (0≤q , q<small) =
  nonnegativeSmallCloseBounded
    (f (Grid.point G i))
    (gridSampleValues ivtData G samplePrecision i)
    samplePrecision
    boundPrecision
    smallPrecision
    sample<bound
    0≤q
    q<small
    (gridSampleClose ivtData G samplePrecision i)


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
    (gridSampleValues ivtData G samplePrecision)
    smallPrecision
    i →
  absᶜ (f (Grid.point G i)) <ᶜ rational (radius targetPrecision)
sampleNonnegativeSmallAbs< {f = f} ivtData G samplePrecision boundPrecision smallPrecision
    targetPrecision sample<bound small+bound<target i smallAt =
  ≤ᶜ-<ᶜ-trans
    (absᶜ (f (Grid.point G i)))
    (rational (radius (smallPrecision +⁺ boundPrecision)))
    (rational (radius targetPrecision))
    (bounded-byᶜ→abs≤
      (smallPrecision +⁺ boundPrecision)
      (f (Grid.point G i))
      (sampleNonnegativeSmallBounded
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


adjacentSampleValuesClose :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (samplePrecision movementPrecision : ℚ⁺) →
  AdjacentClose G
    (uniformModulus {a = a} {b = b} {f = f}
      (IVTFunctionData.uniformlyContinuous ivtData)
      movementPrecision) →
  (i : Fin (suc n)) →
  AdjacentValuesClose
    (gridSampleValues ivtData G samplePrecision)
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
    rational (gridSampleValues ivtData G samplePrecision left)
  left-sample-close =
    gridSampleClose ivtData G samplePrecision left

  right-sample-close :
    f (Grid.point G right) ∼[ samplePrecision ]
    rational (gridSampleValues ivtData G samplePrecision right)
  right-sample-close =
    gridSampleClose ivtData G samplePrecision right

  movement-close :
    f (Grid.point G left) ∼[ movementPrecision ] f (Grid.point G right)
  movement-close =
    uniformClose
      {a = a}
      {b = b}
      {f = f}
      (IVTFunctionData.uniformlyContinuous ivtData)
      movementPrecision
      (adjacentClose i)

  cauchy-close :
    rational (gridSampleValues ivtData G samplePrecision left)
      ∼[ (samplePrecision +⁺ movementPrecision) +⁺ samplePrecision ]
    rational (gridSampleValues ivtData G samplePrecision right)
  cauchy-close =
    close-triangle
      (close-triangle (close-sym left-sample-close) movement-close)
      right-sample-close


sampleNearZeroCandidate :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b (suc n)) →
  (samplePrecision movementPrecision : ℚ⁺) →
  AdjacentClose G
    (uniformModulus {a = a} {b = b} {f = f}
      (IVTFunctionData.uniformlyContinuous ivtData)
      movementPrecision) →
  gridSampleValues ivtData G samplePrecision Fin.zero ℚOrder.< 0ℚ →
  0ℚ ℚOrder.≤
    gridSampleValues ivtData G samplePrecision (Fin.fromℕ (suc n)) →
  Σ[ i ∈ Fin (suc n) ]
    NearZeroCandidate
      (gridSampleValues ivtData G samplePrecision)
      ((samplePrecision +⁺ movementPrecision) +⁺ samplePrecision)
      i
sampleNearZeroCandidate ivtData G samplePrecision movementPrecision adjacentClose =
  gridNearZeroCandidate
    _
    (gridSampleValues ivtData G samplePrecision)
    ((samplePrecision +⁺ movementPrecision) +⁺ samplePrecision)
    (adjacentSampleValuesClose ivtData G samplePrecision movementPrecision adjacentClose)
