{-

Ordered commutative ring structure for HoTT Cauchy reals

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax; _,_)
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Nullary
open import Cubical.Tactics.CommRingSolver.Reflection

import Constructive.Algebra.OrderedCommRing.Properties as OrderedProperties
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Internal.BoundedMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Lattice
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarOrder
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Reals.CauchyReals.Extension
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.Properties
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.CauchyReals.Order.Tightness
open import Constructive.Analysis.Reals.CauchyReals.Order.WeakLinear
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    product-upper-double :
      (u x v y : 𝓡 .fst) →
      ((u + (- x)) · (v + y)) +
      ((u + x) · (v + (- y))) ≡
      (u · v + (- (x · y))) +
      (u · v + (- (x · y)))
    product-upper-double _ _ _ _ =
      solve! 𝓡

    product-lower-double :
      (u x v y : 𝓡 .fst) →
      ((u + x) · (v + y)) +
      ((u + (- x)) · (v + (- y))) ≡
      (u · v + x · y) +
      (u · v + x · y)
    product-lower-double _ _ _ _ =
      solve! 𝓡

  diff-nonnegativeℚ :
    {a b : ℚ} →
    a ℚOrder.≤ b →
    0ℚ ℚOrder.≤ b ℚ.- a
  diff-nonnegativeℚ {a = a} {b = b} a≤b =
    subst
      (λ q → q ℚOrder.≤ b ℚ.- a)
      (ℚ.+InvR a)
      (ℚOrder.≤-+o a b (ℚ.- a) a≤b)

  add-nonnegative-rightᶜ :
    {x y : ℝᶜ} →
    0ᶜ ≤ᶜ y →
    x ≤ᶜ (x +ᶜ y)
  add-nonnegative-rightᶜ {x = x} {y = y} 0≤y =
    subst2 _≤ᶜ_
      (add-zero-left x)
      (add-comm y x)
      (addᶜ-pres≤ᶜ-right {x = 0ᶜ} {y = y} x 0≤y)

  add-positive-rightᶜ :
    {x y : ℝᶜ} →
    PositiveSepᶜ y →
    x <ᶜ (x +ᶜ y)
  add-positive-rightᶜ {x = x} {y = y} pos-y =
    subst PositiveSepᶜ (sym (sum-minus-left x y)) pos-y

  positiveSepᶜ-mono :
    {x y : ℝᶜ} →
    x ≤ᶜ y →
    PositiveSepᶜ x →
    PositiveSepᶜ y
  positiveSepᶜ-mono {x = x} {y = y} x≤y =
    Prop.rec squash₁ step
    where
    step :
      Σ[ ε ∈ ℚ⁺ ] rational (radius ε) ≤ᶜ x →
      PositiveSepᶜ y
    step (ε , ε≤x) =
      ∣ ε , ≤ᶜ-trans ε≤x x≤y ∣₁

  negative-zeroᶜ : -ᶜ 0ᶜ ≡ 0ᶜ
  negative-zeroᶜ =
    inverse-unique-right 0ᶜ 0ᶜ (add-zero-right 0ᶜ)

  zero<ᶜ→positiveSepᶜ :
    {x : ℝᶜ} →
    0ᶜ <ᶜ x →
    PositiveSepᶜ x
  zero<ᶜ→positiveSepᶜ {x = x} =
    subst PositiveSepᶜ
      (cong (x +ᶜ_) negative-zeroᶜ ∙ add-zero-right x)

  min≤rightℚ :
    (q r : ℚ) →
    ℚ.min q r ℚOrder.≤ r
  min≤rightℚ q r =
    subst
      (λ s → s ℚOrder.≤ r)
      (sym (ℚ.minComm q r))
      (ℚOrder.min≤ r q)

  left≤minℚ :
    {q r : ℚ} →
    q ℚOrder.≤ r →
    q ℚOrder.≤ ℚ.min q r
  left≤minℚ {q = q} {r = r} q≤r =
    subst
      (λ s → s ℚOrder.≤ ℚ.min q r)
      (ℚ.minIdem q)
      (ℚOrder.≤MonotoneMin
        q
        q
        q
        r
        (Rational.≤-refl q)
        q≤r)

  right≤minℚ :
    {q r : ℚ} →
    r ℚOrder.≤ q →
    r ℚOrder.≤ ℚ.min q r
  right≤minℚ {q = q} {r = r} r≤q =
    subst
      (λ s → s ℚOrder.≤ ℚ.min q r)
      (ℚ.minIdem r)
      (ℚOrder.≤MonotoneMin
        r
        q
        r
        r
        r≤q
        (Rational.≤-refl r))

  product-upper-double :
    (u x v y : ℝᶜ) →
    ((u +ᶜ (-ᶜ x)) ·ᶜ (v +ᶜ y)) +ᶜ
    ((u +ᶜ x) ·ᶜ (v +ᶜ (-ᶜ y))) ≡
    (u ·ᶜ v +ᶜ (-ᶜ (x ·ᶜ y))) +ᶜ
    (u ·ᶜ v +ᶜ (-ᶜ (x ·ᶜ y)))
  product-upper-double =
    SolverHelpers.product-upper-double CauchyRealsCommRing

  product-lower-double :
    (u x v y : ℝᶜ) →
    ((u +ᶜ x) ·ᶜ (v +ᶜ y)) +ᶜ
    ((u +ᶜ (-ᶜ x)) ·ᶜ (v +ᶜ (-ᶜ y))) ≡
    (u ·ᶜ v +ᶜ x ·ᶜ y) +ᶜ
    (u ·ᶜ v +ᶜ x ·ᶜ y)
  product-lower-double =
    SolverHelpers.product-lower-double CauchyRealsCommRing


scalarMulᶜ-nonnegative :
  (a : ℚ) →
  0ℚ ℚOrder.≤ a →
  {x : ℝᶜ} →
  0ᶜ ≤ᶜ x →
  0ᶜ ≤ᶜ scalarMulᶜ a x
scalarMulᶜ-nonnegative a 0≤a {x = x} 0≤x =
  subst2 _≤ᶜ_
    (scalarMulᶜ-zero-right a)
    refl
    (scalarMulᶜ-pres≤ᶜ-nonnegative
      a
      0≤a
      {x = 0ᶜ}
      {y = x}
      0≤x)


scalarMulᶜ-positive :
  (a : ℚ) →
  0ℚ ℚOrder.< a →
  {x : ℝᶜ} →
  PositiveSepᶜ x →
  PositiveSepᶜ (scalarMulᶜ a x)
scalarMulᶜ-positive a 0<a {x = x} =
  Prop.rec squash₁ step
  where
  0≤a : 0ℚ ℚOrder.≤ a
  0≤a =
    ℚOrder.<Weaken≤ 0ℚ a 0<a

  step :
    Σ[ ε ∈ ℚ⁺ ] rational (radius ε) ≤ᶜ x →
    PositiveSepᶜ (scalarMulᶜ a x)
  step (ε , ε≤x) =
    ∣ (a ℚ.· radius ε , Rational.mul-positive 0<a (ε .snd)) ,
      subst
        (λ y → y ≤ᶜ scalarMulᶜ a x)
        (scalarMulᶜ-rational a (radius ε))
        (scalarMulᶜ-pres≤ᶜ-nonnegative
          a
          0≤a
          {x = rational (radius ε)}
          {y = x}
          ε≤x)
    ∣₁


scalarMulᶜ-pres≤ᶜ-scalar :
  {a b : ℚ} →
  a ℚOrder.≤ b →
  {x : ℝᶜ} →
  0ᶜ ≤ᶜ x →
  scalarMulᶜ a x ≤ᶜ scalarMulᶜ b x
scalarMulᶜ-pres≤ᶜ-scalar {a = a} {b = b} a≤b {x = x} 0≤x =
  subst
    (scalarMulᶜ a x ≤ᶜ_)
    (sym b-path)
    (add-nonnegative-rightᶜ d*x-nonnegative)
  where
  d : ℚ
  d = b ℚ.- a

  d-nonnegative : 0ℚ ℚOrder.≤ d
  d-nonnegative =
    diff-nonnegativeℚ a≤b

  d*x-nonnegative : 0ᶜ ≤ᶜ scalarMulᶜ d x
  d*x-nonnegative =
    scalarMulᶜ-nonnegative d d-nonnegative 0≤x

  b-path : scalarMulᶜ b x ≡ scalarMulᶜ a x +ᶜ scalarMulᶜ d x
  b-path =
    cong (λ q → scalarMulᶜ q x) (sym (Rational.p+[q-p]≡q a b)) ∙
    scalarMulᶜ-distrib-scalar-add a d x


scalarMulᶜ-pres<ᶜ-scalar :
  {a b : ℚ} →
  a ℚOrder.< b →
  {x : ℝᶜ} →
  PositiveSepᶜ x →
  scalarMulᶜ a x <ᶜ scalarMulᶜ b x
scalarMulᶜ-pres<ᶜ-scalar {a = a} {b = b} a<b {x = x} pos-x =
  subst
    (scalarMulᶜ a x <ᶜ_)
    (sym b-path)
    (add-positive-rightᶜ d*x-positive)
  where
  d : ℚ
  d = b ℚ.- a

  0<d : 0ℚ ℚOrder.< d
  0<d =
    Rational.diff-positive {p = a} {q = b} a<b

  d*x-positive : PositiveSepᶜ (scalarMulᶜ d x)
  d*x-positive =
    scalarMulᶜ-positive d 0<d pos-x

  b-path : scalarMulᶜ b x ≡ scalarMulᶜ a x +ᶜ scalarMulᶜ d x
  b-path =
    cong (λ q → scalarMulᶜ q x) (sym (Rational.p+[q-p]≡q a b)) ∙
    scalarMulᶜ-distrib-scalar-add a d x


scalarMulᶜ-min-scalar-left :
  {x : ℝᶜ} →
  0ᶜ ≤ᶜ x →
  (q r : ℚ) →
  q ℚOrder.≤ r →
  scalarMulᶜ (ℚ.min q r) x ≡
  scalarMulᶜ q x ⊓ᶜ scalarMulᶜ r x
scalarMulᶜ-min-scalar-left {x = x} 0≤x q r q≤r =
  ≤ᶜ-antisym min≤scalar-min scalar-min≤min
  where
  min≤scalar-min :
    scalarMulᶜ (ℚ.min q r) x ≤ᶜ
    (scalarMulᶜ q x ⊓ᶜ scalarMulᶜ r x)
  min≤scalar-min =
    ≤ᶜ⊓ᶜ
      (scalarMulᶜ-pres≤ᶜ-scalar (ℚOrder.min≤ q r) 0≤x)
      (scalarMulᶜ-pres≤ᶜ-scalar (min≤rightℚ q r) 0≤x)

  scalar-min≤min :
    (scalarMulᶜ q x ⊓ᶜ scalarMulᶜ r x) ≤ᶜ
    scalarMulᶜ (ℚ.min q r) x
  scalar-min≤min =
    ≤ᶜ-trans
      (⊓ᶜ≤left (scalarMulᶜ q x) (scalarMulᶜ r x))
      (scalarMulᶜ-pres≤ᶜ-scalar (left≤minℚ q≤r) 0≤x)


scalarMulᶜ-min-scalar-right :
  {x : ℝᶜ} →
  0ᶜ ≤ᶜ x →
  (q r : ℚ) →
  r ℚOrder.≤ q →
  scalarMulᶜ (ℚ.min q r) x ≡
  scalarMulᶜ q x ⊓ᶜ scalarMulᶜ r x
scalarMulᶜ-min-scalar-right {x = x} 0≤x q r r≤q =
  ≤ᶜ-antisym min≤scalar-min scalar-min≤min
  where
  min≤scalar-min :
    scalarMulᶜ (ℚ.min q r) x ≤ᶜ
    (scalarMulᶜ q x ⊓ᶜ scalarMulᶜ r x)
  min≤scalar-min =
    ≤ᶜ⊓ᶜ
      (scalarMulᶜ-pres≤ᶜ-scalar (ℚOrder.min≤ q r) 0≤x)
      (scalarMulᶜ-pres≤ᶜ-scalar (min≤rightℚ q r) 0≤x)

  scalar-min≤min :
    (scalarMulᶜ q x ⊓ᶜ scalarMulᶜ r x) ≤ᶜ
    scalarMulᶜ (ℚ.min q r) x
  scalar-min≤min =
    ≤ᶜ-trans
      (⊓ᶜ≤right (scalarMulᶜ q x) (scalarMulᶜ r x))
      (scalarMulᶜ-pres≤ᶜ-scalar (right≤minℚ r≤q) 0≤x)


scalarMulᶜ-min-scalar-nonnegative :
  {x : ℝᶜ} →
  0ᶜ ≤ᶜ x →
  (q r : ℚ) →
  scalarMulᶜ (ℚ.min q r) x ≡
  scalarMulᶜ q x ⊓ᶜ scalarMulᶜ r x
scalarMulᶜ-min-scalar-nonnegative 0≤x q r =
  Sum.rec
    (scalarMulᶜ-min-scalar-left 0≤x q r)
    (scalarMulᶜ-min-scalar-right 0≤x q r)
    (Rational.≤-total q r)


boundedMulᶜ-min-nonnegative-rational-rational :
  (κ : ℚ⁺) (x : ℝᶜ) →
  (x-bound : BoundedByᶜ κ x) →
  0ᶜ ≤ᶜ x →
  (q r : ℚ) →
  boundedMulᶜ κ x x-bound (rational q ⊓ᶜ rational r) ≡
  boundedMulᶜ κ x x-bound (rational q) ⊓ᶜ
  boundedMulᶜ κ x x-bound (rational r)
boundedMulᶜ-min-nonnegative-rational-rational κ x x-bound 0≤x q r =
  scalarMulᶜ-min-scalar-nonnegative 0≤x q r


boundedMulᶜ-min-nonnegative-rational-left :
  (κ : ℚ⁺) (x : ℝᶜ) →
  (x-bound : BoundedByᶜ κ x) →
  0ᶜ ≤ᶜ x →
  (q : ℚ) (y : ℝᶜ) →
  boundedMulᶜ κ x x-bound (rational q ⊓ᶜ y) ≡
  boundedMulᶜ κ x x-bound (rational q) ⊓ᶜ
  boundedMulᶜ κ x x-bound y
boundedMulᶜ-min-nonnegative-rational-left κ x x-bound 0≤x q =
  continuous-equal
    (λ y → boundedMulᶜ κ x x-bound (rational q ⊓ᶜ y))
    (λ y →
      boundedMulᶜ κ x x-bound (rational q) ⊓ᶜ
      boundedMulᶜ κ x x-bound y)
    (comp-uniformlyContinuous {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
      (boundedMulᶜ-continuous κ x x-bound)
      (min-continuous-right (rational q)))
    (comp-uniformlyContinuous {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
      (min-continuous-right (boundedMulᶜ κ x x-bound (rational q)))
      (boundedMulᶜ-continuous κ x x-bound))
    (boundedMulᶜ-min-nonnegative-rational-rational κ x x-bound 0≤x q)


boundedMulᶜ-min-nonnegative :
  (κ : ℚ⁺) (x : ℝᶜ) →
  (x-bound : BoundedByᶜ κ x) →
  0ᶜ ≤ᶜ x →
  (y z : ℝᶜ) →
  boundedMulᶜ κ x x-bound (y ⊓ᶜ z) ≡
  boundedMulᶜ κ x x-bound y ⊓ᶜ
  boundedMulᶜ κ x x-bound z
boundedMulᶜ-min-nonnegative κ x x-bound 0≤x y z =
  continuous-equal
    (λ w → boundedMulᶜ κ x x-bound (w ⊓ᶜ z))
    (λ w →
      boundedMulᶜ κ x x-bound w ⊓ᶜ
      boundedMulᶜ κ x x-bound z)
    (comp-uniformlyContinuous {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
      (boundedMulᶜ-continuous κ x x-bound)
      (min-continuous-left z))
    (comp-uniformlyContinuous {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
      (min-continuous-left (boundedMulᶜ κ x x-bound z))
      (boundedMulᶜ-continuous κ x x-bound))
    (λ q →
      boundedMulᶜ-min-nonnegative-rational-left κ x x-bound 0≤x q z)
    y


boundedMulᶜ-pres≤ᶜ-nonnegative :
  (κ : ℚ⁺) (x : ℝᶜ) →
  (x-bound : BoundedByᶜ κ x) →
  0ᶜ ≤ᶜ x →
  {y z : ℝᶜ} →
  y ≤ᶜ z →
  boundedMulᶜ κ x x-bound y ≤ᶜ
  boundedMulᶜ κ x x-bound z
boundedMulᶜ-pres≤ᶜ-nonnegative κ x x-bound 0≤x {y = y} {z = z} y≤z =
  sym (boundedMulᶜ-min-nonnegative κ x x-bound 0≤x y z) ∙
  cong (boundedMulᶜ κ x x-bound) y≤z


boundedMulᶜ-presPositiveSepᶜ-positive :
  (κ : ℚ⁺) (x : ℝᶜ) →
  (x-bound : BoundedByᶜ κ x) →
  PositiveSepᶜ x →
  {y : ℝᶜ} →
  PositiveSepᶜ y →
  PositiveSepᶜ (boundedMulᶜ κ x x-bound y)
boundedMulᶜ-presPositiveSepᶜ-positive κ x x-bound pos-x {y = y} =
  Prop.rec squash₁ step
  where
  0≤x : 0ᶜ ≤ᶜ x
  0≤x =
    positiveSepᶜ→nonnegative pos-x

  step :
    Σ[ ε ∈ ℚ⁺ ] rational (radius ε) ≤ᶜ y →
    PositiveSepᶜ (boundedMulᶜ κ x x-bound y)
  step (ε , ε≤y) =
    positiveSepᶜ-mono scalar≤bounded scalar-positive
    where
    bounded≤ :
      boundedMulᶜ κ x x-bound (rational (radius ε)) ≤ᶜ
      boundedMulᶜ κ x x-bound y
    bounded≤ =
      boundedMulᶜ-pres≤ᶜ-nonnegative κ x x-bound 0≤x ε≤y

    scalar≤bounded :
      scalarMulᶜ (radius ε) x ≤ᶜ
      boundedMulᶜ κ x x-bound y
    scalar≤bounded =
      subst2 _≤ᶜ_
        (boundedMulᶜ-rational κ x x-bound (radius ε))
        refl
        bounded≤

    scalar-positive : PositiveSepᶜ (scalarMulᶜ (radius ε) x)
    scalar-positive =
      scalarMulᶜ-positive (radius ε) (ε .snd) pos-x


boundedMulᶜ-pres<ᶜ-positive :
  (κ : ℚ⁺) (x : ℝᶜ) →
  (x-bound : BoundedByᶜ κ x) →
  0ᶜ <ᶜ x →
  {y z : ℝᶜ} →
  y <ᶜ z →
  boundedMulᶜ κ x x-bound y <ᶜ
  boundedMulᶜ κ x x-bound z
boundedMulᶜ-pres<ᶜ-positive κ x x-bound 0<x {y = y} {z = z} y<z =
  subst PositiveSepᶜ diff-path
    (boundedMulᶜ-presPositiveSepᶜ-positive
      κ
      x
      x-bound
      (zero<ᶜ→positiveSepᶜ 0<x)
      y<z)
  where
  diff-path :
    boundedMulᶜ κ x x-bound (z +ᶜ (-ᶜ y)) ≡
    boundedMulᶜ κ x x-bound z +ᶜ
    (-ᶜ boundedMulᶜ κ x x-bound y)
  diff-path =
    boundedMulᶜ-distrib-real-add κ x x-bound z (-ᶜ y) ∙
    cong
      (boundedMulᶜ κ x x-bound z +ᶜ_)
      (boundedMulᶜ-neg-right κ x x-bound y)


mulᶜ-pres≤ᶜ-right :
  (x y z : ℝᶜ) →
  0ᶜ ≤ᶜ z →
  x ≤ᶜ y →
  (x ·ᶜ z) ≤ᶜ (y ·ᶜ z)
mulᶜ-pres≤ᶜ-right x y z 0≤z x≤y =
  Prop.rec (isProp≤ᶜ (x ·ᶜ z) (y ·ᶜ z)) step (merely-boundedᶜ z)
  where
  step :
    Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ z →
    (x ·ᶜ z) ≤ᶜ (y ·ᶜ z)
  step (κ , z-bound) =
    subst2 _≤ᶜ_
      (sym left-path)
      (sym right-path)
      bounded≤
    where
    bounded≤ :
      boundedMulᶜ κ z z-bound x ≤ᶜ
      boundedMulᶜ κ z z-bound y
    bounded≤ =
      boundedMulᶜ-pres≤ᶜ-nonnegative κ z z-bound 0≤z x≤y

    left-path : x ·ᶜ z ≡ boundedMulᶜ κ z z-bound x
    left-path =
      mulᶜ-comm x z ∙ mulᶜ-bound κ z z-bound x

    right-path : y ·ᶜ z ≡ boundedMulᶜ κ z z-bound y
    right-path =
      mulᶜ-comm y z ∙ mulᶜ-bound κ z z-bound y


mulᶜ-pres<ᶜ-right :
  (x y z : ℝᶜ) →
  0ᶜ <ᶜ z →
  x <ᶜ y →
  (x ·ᶜ z) <ᶜ (y ·ᶜ z)
mulᶜ-pres<ᶜ-right x y z 0<z x<y =
  Prop.rec (isProp<ᶜ (x ·ᶜ z) (y ·ᶜ z)) step (merely-boundedᶜ z)
  where
  step :
    Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ z →
    (x ·ᶜ z) <ᶜ (y ·ᶜ z)
  step (κ , z-bound) =
    subst2 _<ᶜ_
      (sym left-path)
      (sym right-path)
      bounded<
    where
    bounded< :
      boundedMulᶜ κ z z-bound x <ᶜ
      boundedMulᶜ κ z z-bound y
    bounded< =
      boundedMulᶜ-pres<ᶜ-positive κ z z-bound 0<z x<y

    left-path : x ·ᶜ z ≡ boundedMulᶜ κ z z-bound x
    left-path =
      mulᶜ-comm x z ∙ mulᶜ-bound κ z z-bound x

    right-path : y ·ᶜ z ≡ boundedMulᶜ κ z z-bound y
    right-path =
      mulᶜ-comm y z ∙ mulᶜ-bound κ z z-bound y


CauchyRealsIsOrderedCommRing :
  IsOrderedCommRing 0ᶜ 1ᶜ _+ᶜ_ _·ᶜ_ -ᶜ_ _<ᶜ_ _≤ᶜ_
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.isCommRing =
  CauchyRealsCommRing .snd .CommRingStr.isCommRing
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.isPseudolattice =
  CauchyReals≤Pseudolattice .snd .PseudolatticeStr.is-pseudolattice
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.isStrictOrder =
  CauchyReals<StrictOrder
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.<-≤-weaken =
  λ x y → <ᶜ→≤ᶜ {x = x} {y = y}
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.≤≃¬> =
  ≤ᶜ≃¬>ᶜ
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.+MonoR≤ =
  λ x y z → addᶜ-pres≤ᶜ-right {x = x} {y = y} z
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.+MonoR< =
  λ x y z → addᶜ-pres<ᶜ-right {x = x} {y = y} z
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.posSum→pos∨pos =
  positive-sum-splitᶜ
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.<-≤-trans =
  <ᶜ-≤ᶜ-trans
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.≤-<-trans =
  ≤ᶜ-<ᶜ-trans
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.·MonoR≤ =
  mulᶜ-pres≤ᶜ-right
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.·MonoR< =
  mulᶜ-pres<ᶜ-right
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.0<1 =
  0ᶜ<1ᶜ


CauchyRealsOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
CauchyRealsOrderedCommRing .fst =
  ℝᶜ
CauchyRealsOrderedCommRing .snd =
  orderedcommringstr
    0ᶜ
    1ᶜ
    _+ᶜ_
    _·ᶜ_
    -ᶜ_
    _<ᶜ_
    _≤ᶜ_
    CauchyRealsIsOrderedCommRing


module CauchyRealsOrdered =
  OrderedProperties.OrderedCommRingTheory CauchyRealsOrderedCommRing


scalarMulᶜ-half-double :
  (x : ℝᶜ) →
  scalarMulᶜ Rational.1/2 (x +ᶜ x) ≡ x
scalarMulᶜ-half-double x =
  scalarMulᶜ-distrib-real-add Rational.1/2 x x ∙
  sym (scalarMulᶜ-distrib-scalar-add Rational.1/2 Rational.1/2 x) ∙
  cong (λ q → scalarMulᶜ q x) Rational.1/2+1/2≡1 ∙
  scalarMulᶜ-one x


double-nonnegativeᶜ→nonnegative :
  (x : ℝᶜ) →
  0ᶜ ≤ᶜ (x +ᶜ x) →
  0ᶜ ≤ᶜ x
double-nonnegativeᶜ→nonnegative x double-nonnegative =
  subst
    (λ y → 0ᶜ ≤ᶜ y)
    (scalarMulᶜ-half-double x)
    (scalarMulᶜ-nonnegative
      Rational.1/2
      (Rational.<→≤
        {p = Rational.0ℚ}
        {q = Rational.1/2}
        Rational.0<1/2)
      double-nonnegative)


abs-minus-nonnegativeᶜ :
  (x : ℝᶜ) →
  0ᶜ ≤ᶜ (absᶜ x +ᶜ (-ᶜ x))
abs-minus-nonnegativeᶜ x =
  CauchyRealsOrdered.≥→Diff≥0
    {x = absᶜ x}
    {y = x}
    (≤ᶜabsᶜ-left x)


abs-plus-nonnegativeᶜ :
  (x : ℝᶜ) →
  0ᶜ ≤ᶜ (absᶜ x +ᶜ x)
abs-plus-nonnegativeᶜ x =
  subst
    (λ y → 0ᶜ ≤ᶜ (absᶜ x +ᶜ y))
    (neg-involutive x)
    (CauchyRealsOrdered.≥→Diff≥0
      {x = absᶜ x}
      {y = -ᶜ x}
      (≤ᶜabsᶜ-right x))


mulᶜ≤abs-product :
  (x y : ℝᶜ) →
  x ·ᶜ y ≤ᶜ absᶜ x ·ᶜ absᶜ y
mulᶜ≤abs-product x y =
  CauchyRealsOrdered.Diff≥0→≥
    {x = absᶜ x ·ᶜ absᶜ y}
    {y = x ·ᶜ y}
    productDiffNonnegative
  where
  productDiff : ℝᶜ
  productDiff =
    absᶜ x ·ᶜ absᶜ y +ᶜ (-ᶜ (x ·ᶜ y))

  leftProductNonnegative :
    0ᶜ ≤ᶜ
    ((absᶜ x +ᶜ (-ᶜ x)) ·ᶜ (absᶜ y +ᶜ y))
  leftProductNonnegative =
    CauchyRealsOrdered.·-Pres≥0
      (abs-minus-nonnegativeᶜ x)
      (abs-plus-nonnegativeᶜ y)

  rightProductNonnegative :
    0ᶜ ≤ᶜ
    ((absᶜ x +ᶜ x) ·ᶜ (absᶜ y +ᶜ (-ᶜ y)))
  rightProductNonnegative =
    CauchyRealsOrdered.·-Pres≥0
      (abs-plus-nonnegativeᶜ x)
      (abs-minus-nonnegativeᶜ y)

  doubleProductDiffNonnegative :
    0ᶜ ≤ᶜ (productDiff +ᶜ productDiff)
  doubleProductDiffNonnegative =
    subst
      (λ z → 0ᶜ ≤ᶜ z)
      (product-upper-double (absᶜ x) x (absᶜ y) y)
      (nonnegativeᶜ-add
        leftProductNonnegative
        rightProductNonnegative)

  productDiffNonnegative :
    0ᶜ ≤ᶜ productDiff
  productDiffNonnegative =
    double-nonnegativeᶜ→nonnegative
      productDiff
      doubleProductDiffNonnegative


neg-mulᶜ≤abs-product :
  (x y : ℝᶜ) →
  -ᶜ (x ·ᶜ y) ≤ᶜ absᶜ x ·ᶜ absᶜ y
neg-mulᶜ≤abs-product x y =
  CauchyRealsOrdered.Diff≥0→≥
    {x = absᶜ x ·ᶜ absᶜ y}
    {y = -ᶜ (x ·ᶜ y)}
    (subst
      (λ z → 0ᶜ ≤ᶜ (absᶜ x ·ᶜ absᶜ y +ᶜ z))
      (sym (neg-involutive (x ·ᶜ y)))
      productDiffNonnegative)
  where
  productDiff : ℝᶜ
  productDiff =
    absᶜ x ·ᶜ absᶜ y +ᶜ x ·ᶜ y

  leftProductNonnegative :
    0ᶜ ≤ᶜ
    ((absᶜ x +ᶜ x) ·ᶜ (absᶜ y +ᶜ y))
  leftProductNonnegative =
    CauchyRealsOrdered.·-Pres≥0
      (abs-plus-nonnegativeᶜ x)
      (abs-plus-nonnegativeᶜ y)

  rightProductNonnegative :
    0ᶜ ≤ᶜ
    ((absᶜ x +ᶜ (-ᶜ x)) ·ᶜ (absᶜ y +ᶜ (-ᶜ y)))
  rightProductNonnegative =
    CauchyRealsOrdered.·-Pres≥0
      (abs-minus-nonnegativeᶜ x)
      (abs-minus-nonnegativeᶜ y)

  doubleProductDiffNonnegative :
    0ᶜ ≤ᶜ (productDiff +ᶜ productDiff)
  doubleProductDiffNonnegative =
    subst
      (λ z → 0ᶜ ≤ᶜ z)
      (product-lower-double (absᶜ x) x (absᶜ y) y)
      (nonnegativeᶜ-add
        leftProductNonnegative
        rightProductNonnegative)

  productDiffNonnegative :
    0ᶜ ≤ᶜ productDiff
  productDiffNonnegative =
    double-nonnegativeᶜ→nonnegative
      productDiff
      doubleProductDiffNonnegative


bounded-byᶜ-abs≤rational :
  (κ : ℚ⁺) (x : ℝᶜ) →
  BoundedByᶜ κ x →
  absᶜ x ≤ᶜ rational (radius κ)
bounded-byᶜ-abs≤rational κ x x-bound =
  absᶜ-least
    x
    (rational (radius κ))
    (≤ℚ→rational≤ᶜ
      {q = Rational.0ℚ}
      {r = radius κ}
      (ℚOrder.<Weaken≤ Rational.0ℚ (radius κ) (κ .snd)))
    (upperᶜ x-bound)
    (lowerᶜ x-bound)


bounded-byᶜ-mul :
  (κ μ : ℚ⁺) (x y : ℝᶜ) →
  BoundedByᶜ κ x →
  BoundedByᶜ μ y →
  BoundedByᶜ (κ *⁺ μ) (x ·ᶜ y)
bounded-byᶜ-mul κ μ x y x-bound y-bound =
  bounded-byᶜ
    (≤ᶜ-trans
      {x = x ·ᶜ y}
      {y = absᶜ x ·ᶜ absᶜ y}
      {z = rational (radius (κ *⁺ μ))}
      (mulᶜ≤abs-product x y)
      absProduct≤bound)
    (≤ᶜ-trans
      {x = -ᶜ (x ·ᶜ y)}
      {y = absᶜ x ·ᶜ absᶜ y}
      {z = rational (radius (κ *⁺ μ))}
      (neg-mulᶜ≤abs-product x y)
      absProduct≤bound)
  where
  absProduct≤rationalProduct :
    absᶜ x ·ᶜ absᶜ y ≤ᶜ
    rational (radius κ) ·ᶜ rational (radius μ)
  absProduct≤rationalProduct =
    CauchyRealsOrdered.·-PosPres≥
      (absᶜ-nonnegative x)
      (absᶜ-nonnegative y)
      (bounded-byᶜ-abs≤rational κ x x-bound)
      (bounded-byᶜ-abs≤rational μ y y-bound)

  absProduct≤bound :
    absᶜ x ·ᶜ absᶜ y ≤ᶜ rational (radius (κ *⁺ μ))
  absProduct≤bound =
    subst
      (λ z → absᶜ x ·ᶜ absᶜ y ≤ᶜ z)
      (mulᶜ-rational-rational (radius κ) (radius μ))
      absProduct≤rationalProduct
