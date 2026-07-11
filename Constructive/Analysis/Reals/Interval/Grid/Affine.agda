{-

Affine images of rational unit interval grids

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Interval.Grid.Affine where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; _×_)

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Quantitative
  using (bounded-real-right-multiplierᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (scalarMulᶜ-nonnegative ; scalarMulᶜ-pres≤ᶜ-scalar)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Properties
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.Interval.Base
open import Constructive.Analysis.Reals.Interval.Order using (gapᶜ)
open import Constructive.Analysis.Reals.Interval.Grid.Base
open import Constructive.Analysis.Reals.Interval.Grid.Rational
open import Constructive.Analysis.Reals.Locator
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


unit≤ᶜ : 0ᶜ ≤ᶜ 1ᶜ
unit≤ᶜ =
  ≤ℚ→rational≤ᶜ (Rational.<→≤ Rational.0<1)


locatedGapBound :
  (a b : ℝᶜ) →
  Locator a →
  Locator b →
  Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ (gapᶜ a b)
locatedGapBound a b loc-a loc-b =
  scalar-bound gapApprox ,
  rational-approximation-boundᶜ (gapᶜ a b) gapApprox gap∼gapApprox
  where
  precision : ℚ⁺
  precision =
    quarter⁺ 1⁺

  aApprox : Σ[ q ∈ ℚ ] a ∼[ precision ] rational q
  aApprox =
    Locator.approximate loc-a precision

  bApprox : Σ[ q ∈ ℚ ] b ∼[ precision ] rational q
  bApprox =
    Locator.approximate loc-b precision

  qa qb : ℚ
  qa =
    aApprox .fst
  qb =
    bApprox .fst

  gapApprox : ℚ
  gapApprox =
    qb ℚ.- qa

  raw-gap∼ :
    gapᶜ a b ∼[ precision +⁺ precision ]
    (rational qb +ᶜ (-ᶜ rational qa))
  raw-gap∼ =
    add-close
      (bApprox .snd)
      (neg-close (aApprox .snd))

  target-path :
    rational qb +ᶜ (-ᶜ rational qa) ≡ rational gapApprox
  target-path =
    cong (rational qb +ᶜ_) (neg-rational qa) ∙
    add-rational qb (ℚ.- qa)

  target-gap∼ :
    gapᶜ a b ∼[ precision +⁺ precision ] rational gapApprox
  target-gap∼ =
    subst
      (λ y → gapᶜ a b ∼[ precision +⁺ precision ] y)
      target-path
      raw-gap∼

  gap∼gapApprox :
    gapᶜ a b ∼[ half⁺ 1⁺ ] rational gapApprox
  gap∼gapApprox =
    subst
      (λ ρ → gapᶜ a b ∼[ ρ ] rational gapApprox)
      (ℚ⁺Path (quarter-sum≡half 1⁺))
      target-gap∼


affineRationalPointᶜ :
  (a b : ℝᶜ) →
  ℚ →
  ℝᶜ
affineRationalPointᶜ a b q =
  a +ᶜ scalarMulᶜ q (gapᶜ a b)


private
  a+gap≡b :
    (a b : ℝᶜ) →
    a +ᶜ gapᶜ a b ≡ b
  a+gap≡b a b =
    add-comm a (gapᶜ a b) ∙
    minus-plus-cancel-right b a

  affine-rational-lower :
    (a b : ℝᶜ) →
    (a≤b : a ≤ᶜ b) →
    (q : ℚ) →
    Rational.0ℚ ℚOrder.≤ q →
    a ≤ᶜ affineRationalPointᶜ a b q
  affine-rational-lower a b a≤b q 0≤q =
    subst
      (λ x → x ≤ᶜ affineRationalPointᶜ a b q)
      (add-zero-right a)
      (addᶜ-pres≤ᶜ-left a scaled-nonnegative)
    where
    g : ℝᶜ
    g =
      gapᶜ a b

    0≤g : 0ᶜ ≤ᶜ g
    0≤g =
      ≤ᶜ→diffᶜ-nonnegative {x = a} {y = b} a≤b

    scaled-nonnegative : 0ᶜ ≤ᶜ scalarMulᶜ q g
    scaled-nonnegative =
      scalarMulᶜ-nonnegative q 0≤q 0≤g

  affine-rational-upper :
    (a b : ℝᶜ) →
    (a≤b : a ≤ᶜ b) →
    (q : ℚ) →
    q ℚOrder.≤ Rational.1ℚ →
    affineRationalPointᶜ a b q ≤ᶜ b
  affine-rational-upper a b a≤b q q≤1 =
    subst
      (affineRationalPointᶜ a b q ≤ᶜ_)
      (a+gap≡b a b)
      (addᶜ-pres≤ᶜ-left a scaled≤gap)
    where
    g : ℝᶜ
    g =
      gapᶜ a b

    0≤g : 0ᶜ ≤ᶜ g
    0≤g =
      ≤ᶜ→diffᶜ-nonnegative {x = a} {y = b} a≤b

    scaled≤gap : scalarMulᶜ q g ≤ᶜ g
    scaled≤gap =
      subst
        (scalarMulᶜ q g ≤ᶜ_)
        (scalarMulᶜ-one g)
        (scalarMulᶜ-pres≤ᶜ-scalar q≤1 0≤g)

  affine-rational-zero :
    (a b : ℝᶜ) →
    (q : ℚ) →
    q ≡ Rational.0ℚ →
    affineRationalPointᶜ a b q ≡ a
  affine-rational-zero a b q q≡0 =
    cong (λ r → a +ᶜ scalarMulᶜ r (gapᶜ a b)) q≡0 ∙
    cong (a +ᶜ_) (scalarMulᶜ-zero (gapᶜ a b)) ∙
    add-zero-right a

  affine-rational-one :
    (a b : ℝᶜ) →
    (q : ℚ) →
    q ≡ Rational.1ℚ →
    affineRationalPointᶜ a b q ≡ b
  affine-rational-one a b q q≡1 =
    cong (λ r → a +ᶜ scalarMulᶜ r (gapᶜ a b)) q≡1 ∙
    cong (a +ᶜ_) (scalarMulᶜ-one (gapᶜ a b)) ∙
    a+gap≡b a b

  finToℕ≤Last :
    {n : ℕ} →
    (i : Fin (suc n)) →
    NatOrder._≤_ (Fin.toℕ i) n
  finToℕ≤Last {n = zero} Fin.zero =
    NatOrder.≤-refl
  finToℕ≤Last {n = suc n} Fin.zero =
    NatOrder.zero-≤
  finToℕ≤Last {n = suc n} (Fin.suc i) =
    NatOrder.suc-≤-suc (finToℕ≤Last i)

  coeff-lower :
    (step : ℚ⁺) →
    (n : ℕ) →
    (i : Fin (suc n)) →
    Rational.0ℚ ℚOrder.≤ Rational.grid Rational.0ℚ (radius step) (Fin.toℕ i)
  coeff-lower step n i =
    Rational.q≤q+nonnegative
      Rational.0ℚ
      (Rational.natMul (Fin.toℕ i) (radius step))
      (Rational.natMul-nonnegative (Fin.toℕ i) (step .snd))

  grid-zero-index-mono-≤ :
    (step : ℚ⁺) →
    (k n : ℕ) →
    NatOrder._≤_ k n →
    Rational.grid Rational.0ℚ (radius step) k ℚOrder.≤
    Rational.grid Rational.0ℚ (radius step) n
  grid-zero-index-mono-≤ step k n k≤n =
    ℚOrder.≤Monotone+
      Rational.0ℚ
      Rational.0ℚ
      (Rational.natMul k (radius step))
      (Rational.natMul n (radius step))
      (Rational.≤-refl Rational.0ℚ)
      (Rational.natMul-mono-≤ k n (step .snd) k≤n)

  coeff-upper :
    (step : ℚ⁺) →
    (n : ℕ) →
    (right-path : Rational.grid Rational.0ℚ (radius step) n ≡ Rational.1ℚ) →
    (i : Fin (suc n)) →
    Rational.grid Rational.0ℚ (radius step) (Fin.toℕ i) ℚOrder.≤ Rational.1ℚ
  coeff-upper step n right-path i =
    subst
      (Rational.grid Rational.0ℚ (radius step) (Fin.toℕ i) ℚOrder.≤_)
      right-path
      (grid-zero-index-mono-≤
        step
        (Fin.toℕ i)
        n
        (finToℕ≤Last i))


affineRationalGridWithRight :
  (a b : ℝᶜ) →
  (a≤b : a ≤ᶜ b) →
  (step : ℚ⁺) →
  (n : ℕ) →
  Rational.grid Rational.0ℚ (radius step) n ≡ Rational.1ℚ →
  Grid a b a≤b n
affineRationalGridWithRight a b a≤b step n right-path =
  make-grid point left-path right-pathᶜ
  where
  coeff : Fin (suc n) → ℚ
  coeff i =
    Rational.grid Rational.0ℚ (radius step) (Fin.toℕ i)

  point : Fin (suc n) → [ a , b ]ᶜ
  point i =
    affineRationalPointᶜ a b (coeff i) ,
    affine-rational-lower a b a≤b (coeff i)
      (coeff-lower step n i) ,
    affine-rational-upper a b a≤b (coeff i)
      (coeff-upper step n right-path i)

  left-path :
    pointᶜ {a = a} {b = b} (point Fin.zero) ≡ a
  left-path =
    affine-rational-zero
      a
      b
      (coeff Fin.zero)
      (Rational.grid-zero Rational.0ℚ (radius step))

  right-pathᶜ :
    pointᶜ {a = a} {b = b} (point (Fin.fromℕ n)) ≡ b
  right-pathᶜ =
    affine-rational-one
      a
      b
      (coeff (Fin.fromℕ n))
      (subst
        (λ k → Rational.grid Rational.0ℚ (radius step) k ≡ Rational.1ℚ)
        (sym (Fin.toFromId n))
        right-path)


affineRationalGridWithRightAdjacentClose :
  (a b : ℝᶜ) →
  (a≤b : a ≤ᶜ b) →
  (κ : ℚ⁺) →
  (gap-bound : BoundedByᶜ κ (gapᶜ a b)) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid Rational.0ℚ (radius step) n ≡ Rational.1ℚ) →
  AdjacentClose
    (affineRationalGridWithRight a b a≤b step n right-path)
    (κ *⁺ (step +⁺ step))
affineRationalGridWithRightAdjacentClose
    a b a≤b κ gap-bound step n right-path i =
  add-close-right a
    (bounded-real-right-multiplierᶜ
      κ
      (gapᶜ a b)
      gap-bound
      leftCoeff
      rightCoeff
      (step +⁺ step)
      coeffClose)
  where
  leftCoeff rightCoeff : ℚ
  leftCoeff =
    Rational.grid Rational.0ℚ (radius step) (Fin.toℕ (Fin.weakenFin i))
  rightCoeff =
    Rational.grid Rational.0ℚ (radius step) (Fin.toℕ (Fin.suc i))

  coeffClose =
    rationalStepGridWithRightAdjacentCloseℚ
      Rational.0ℚ
      Rational.1ℚ
      step
      n
      right-path
      i


scalePrecision :
  (mesh κ : ℚ⁺) →
  ℚ⁺
scalePrecision mesh κ =
  Rational.scaleByPositive (radius mesh) (radius κ) (κ .snd) ,
  Rational.scaleByPositive-positive
    {ε = radius mesh}
    {M = radius κ}
    (mesh .snd)
    (κ .snd)


scaledPrecision< :
  (mesh κ δ : ℚ⁺) →
  δ <⁺ scalePrecision mesh κ →
  κ *⁺ δ <⁺ mesh
scaledPrecision< mesh κ δ δ<scale =
  κδ<mesh
  where
  κδ<κscale :
    radius κ ℚ.· radius δ ℚOrder.<
    radius κ ℚ.· radius (scalePrecision mesh κ)
  κδ<κscale =
    Rational.mul-left-positive-<
      {a = radius κ}
      {b = radius δ}
      {c = radius (scalePrecision mesh κ)}
      (κ .snd)
      δ<scale

  κδ<mesh :
    radius κ ℚ.· radius δ ℚOrder.< radius mesh
  κδ<mesh =
    subst
      (radius κ ℚ.· radius δ ℚOrder.<_)
      (Rational.scaleByPositive-cancelL (radius mesh) (radius κ) (κ .snd))
      κδ<κscale


locatedAffineGridData :
  (a b : ℝᶜ) →
  (a≤b : a ≤ᶜ b) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (gapᶜ a b) →
  (mesh : ℚ⁺) →
  Σ[ n ∈ ℕ ]
    Σ[ G ∈ Grid a b a≤b (suc n) ]
      AdjacentClose G mesh
locatedAffineGridData a b a≤b κ gap-bound mesh =
  n , affineGrid , adjacent
  where
  coeffMesh : ℚ⁺
  coeffMesh =
    scalePrecision mesh κ

  stepData :
    Σ[ k ∈ ℕ ]
      (Rational.grid Rational.0ℚ
        (radius (rationalExactStep Rational.0ℚ Rational.1ℚ Rational.0<1 k))
        (suc k) ≡ Rational.1ℚ) ×
      (rationalExactStep Rational.0ℚ Rational.1ℚ Rational.0<1 k +⁺
       rationalExactStep Rational.0ℚ Rational.1ℚ Rational.0<1 k <⁺
       coeffMesh)
  stepData =
    rationalExactStepGridData Rational.0ℚ Rational.1ℚ Rational.0<1 coeffMesh

  n : ℕ
  n =
    stepData .fst

  step : ℚ⁺
  step =
    rationalExactStep Rational.0ℚ Rational.1ℚ Rational.0<1 n

  right-path :
    Rational.grid Rational.0ℚ (radius step) (suc n) ≡ Rational.1ℚ
  right-path =
    stepData .snd .fst

  affineGrid : Grid a b a≤b (suc n)
  affineGrid =
    affineRationalGridWithRight a b a≤b step (suc n) right-path

  δ : ℚ⁺
  δ =
    step +⁺ step

  δ<coeffMesh : δ <⁺ coeffMesh
  δ<coeffMesh =
    stepData .snd .snd

  affineAdjacent :
    AdjacentClose affineGrid (κ *⁺ δ)
  affineAdjacent =
    affineRationalGridWithRightAdjacentClose
      a
      b
      a≤b
      κ
      gap-bound
      step
      (suc n)
      right-path

  adjacent : AdjacentClose affineGrid mesh
  adjacent i =
    MetricSpace.close-mono
      (IntervalMetric a b)
      {x = Grid.point affineGrid (Fin.weakenFin i)}
      {y = Grid.point affineGrid (Fin.suc i)}
      {ε = κ *⁺ δ}
      {δ = mesh}
      (scaledPrecision< mesh κ δ δ<coeffMesh)
      (affineAdjacent i)
