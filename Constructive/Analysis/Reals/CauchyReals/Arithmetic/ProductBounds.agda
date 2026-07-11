{-

Absolute-value and bound estimates for Cauchy-real products

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.CauchyReals.Arithmetic.ProductBounds where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax; _,_)
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Lattice
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.MultiplicationOrder
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarOrder
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Structures
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Reals.CauchyReals.Extension
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
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

  module ScalarSolverHelpers {ℓ : Level} (R : CommRing ℓ) where
    open CommRingStr (R .snd)

    scalar-product-form :
      (N i r : R .fst) →
      N · (i · r) ≡ (N · i) · r
    scalar-product-form _ _ _ =
      solve! R

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


mulᶜ-nonnegative :
  (x y : ℝᶜ) →
  0ᶜ ≤ᶜ x →
  0ᶜ ≤ᶜ y →
  0ᶜ ≤ᶜ x ·ᶜ y
mulᶜ-nonnegative x y 0≤x 0≤y =
  subst
    (λ z → z ≤ᶜ x ·ᶜ y)
    (mulᶜ-zero-left y)
    (mulᶜ-pres≤ᶜ-right 0ᶜ x y 0≤y 0≤x)


absᶜ-mul≤product :
  (x y X Y : ℝᶜ) →
  0ᶜ ≤ᶜ X →
  0ᶜ ≤ᶜ Y →
  absᶜ x ≤ᶜ X →
  absᶜ y ≤ᶜ Y →
  absᶜ (x ·ᶜ y) ≤ᶜ X ·ᶜ Y
absᶜ-mul≤product x y X Y 0≤X 0≤Y absx≤X absy≤Y =
  absᶜ-least
    (x ·ᶜ y)
    (X ·ᶜ Y)
    (mulᶜ-nonnegative X Y 0≤X 0≤Y)
    (≤ᶜ-trans
      (mulᶜ≤abs-product x y)
      absProduct≤majorantProduct)
    (≤ᶜ-trans
      (neg-mulᶜ≤abs-product x y)
      absProduct≤majorantProduct)
  where
  absProduct≤majorantProduct :
    absᶜ x ·ᶜ absᶜ y ≤ᶜ X ·ᶜ Y
  absProduct≤majorantProduct =
    ≤ᶜ-trans
      (mulᶜ-pres≤ᶜ-right
        (absᶜ x)
        X
        (absᶜ y)
        (absᶜ-nonnegative y)
        absx≤X)
      (subst2
        _≤ᶜ_
        (mulᶜ-comm (absᶜ y) X)
        (mulᶜ-comm Y X)
        (mulᶜ-pres≤ᶜ-right
          (absᶜ y)
          Y
          X
          0≤X
          absy≤Y))


absᶜ-scalarMul≤ :
  (q : ℚ) →
  Rational.0ℚ ℚOrder.≤ q →
  {x X : ℝᶜ} →
  0ᶜ ≤ᶜ X →
  absᶜ x ≤ᶜ X →
  absᶜ (scalarMulᶜ q x) ≤ᶜ scalarMulᶜ q X
absᶜ-scalarMul≤ q 0≤q {x = x} {X = X} 0≤X absx≤X =
  absᶜ-least
    (scalarMulᶜ q x)
    (scalarMulᶜ q X)
    (scalarMulᶜ-nonnegative q 0≤q 0≤X)
    (scalarMulᶜ-pres≤ᶜ-nonnegative
      q
      0≤q
      (≤ᶜ-trans (≤ᶜabsᶜ-left x) absx≤X))
    (subst
      (λ y → y ≤ᶜ scalarMulᶜ q X)
      (scalarMulᶜ-neg-real q x)
      (scalarMulᶜ-pres≤ᶜ-nonnegative
        q
        0≤q
        (≤ᶜ-trans (≤ᶜabsᶜ-right x) absx≤X)))


absᶜ-rational-nonnegative :
  (q : ℚ) →
  Rational.0ℚ ℚOrder.≤ q →
  absᶜ (rational q) ≤ᶜ rational q
absᶜ-rational-nonnegative q 0≤q =
  absᶜ-least
    (rational q)
    (rational q)
    (≤ℚ→rational≤ᶜ 0≤q)
    (≤ᶜ-refl (rational q))
    (subst
      (λ x → x ≤ᶜ rational q)
      (sym (neg-rational q))
      (≤ℚ→rational≤ᶜ
        (Rational.≤-trans
          (Rational.neg-nonpositive 0≤q)
          0≤q)))


tripleScalarProductPath :
  (N i r : ℚ) →
  (x : ℝᶜ) →
  rational N ·ᶜ (scalarMulᶜ i x ·ᶜ rational r) ≡
  scalarMulᶜ ((N ℚ.· i) ℚ.· r) x
tripleScalarProductPath N i r x =
  cong
    (λ y → rational N ·ᶜ (y ·ᶜ rational r))
    (sym (mulᶜ-rational-left i x)) ∙
  cong
    (λ y → rational N ·ᶜ (y ·ᶜ rational r))
    (mulᶜ-comm (rational i) x) ∙
  cong
    (rational N ·ᶜ_)
    (mulᶜ-rational-right-assoc x i r) ∙
  cong
    (rational N ·ᶜ_)
    (mulᶜ-comm-rational-right x (i ℚ.· r)) ∙
  mulᶜ-rational-left-assoc N (i ℚ.· r) x ∙
  cong
    (λ q → rational q ·ᶜ x)
    (ScalarSolverHelpers.scalar-product-form ℚCommRing N i r) ∙
  mulᶜ-rational-left ((N ℚ.· i) ℚ.· r) x


bounded-byᶜ-abs≤rational :
  {κ : ℚ⁺} {x : ℝᶜ} →
  BoundedByᶜ κ x →
  absᶜ x ≤ᶜ rational (radius κ)
bounded-byᶜ-abs≤rational {κ = κ} {x = x} x-bound =
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
      (bounded-byᶜ-abs≤rational x-bound)
      (bounded-byᶜ-abs≤rational y-bound)

  absProduct≤bound :
    absᶜ x ·ᶜ absᶜ y ≤ᶜ rational (radius (κ *⁺ μ))
  absProduct≤bound =
    subst
      (λ z → absᶜ x ·ᶜ absᶜ y ≤ᶜ z)
      (mulᶜ-rational-rational (radius κ) (radius μ))
      absProduct≤rationalProduct
