{-# OPTIONS --safe #-}

module Constructive.Analysis.Reals.CauchyReals.Order.WeakLinear where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ; Σ-syntax; _,_)
open import Cubical.Data.Sum as Sum using (_⊎_; inl; inr)
import Cubical.Functions.Logic as Logic
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∣_∣₁ ; squash₁)
import Cubical.Relation.Binary.Order.StrictOrder as StrictOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Approximation
open import Constructive.Analysis.Reals.CauchyReals.Order.Density
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Data.PositiveRationals


≤∨<ℚ :
  (q a : ℚ) →
  (a ℚOrder.< q) ⊎ (q ℚOrder.≤ a)
≤∨<ℚ q a with q ℚOrder.≟ a
... | ℚOrder.lt q<a =
  inr (ℚOrder.<Weaken≤ q a q<a)
... | ℚOrder.eq q≡a =
  inr (ℚOrder.≡Weaken≤ q a q≡a)
... | ℚOrder.gt a<q =
  inl a<q


weak-linear-from-gap :
  (x y z : ℝᶜ) (ε : ℚ⁺) →
  rational (radius ε) ≤ᶜ (y +ᶜ (-ᶜ x)) →
  (x <ᶜ z) Logic.⊔′ (z <ᶜ y)
weak-linear-from-gap x y z ε ε≤y-x =
  Prop.rec squash₁ approxStep (rational-approximation d δ)
  where
  d : ℝᶜ
  d = z +ᶜ (-ᶜ x)

  quarterε δ : ℚ⁺
  quarterε = quarter⁺ ε
  δ = half⁺ quarterε

  δ<quarter : δ <⁺ quarterε
  δ<quarter =
    half< quarterε

  rightCase :
    (q : ℚ) →
    d ∼[ δ ] rational q →
    q ℚOrder.≤ radius quarterε →
    z <ᶜ y
  rightCase q d∼q q≤quarter =
    diff≤half-gap→<ᶜ x y z ε ε≤y-x d≤half
    where
    q+quarter≤half : q ℚ.+ radius quarterε ℚOrder.≤ radius (half⁺ ε)
    q+quarter≤half =
      subst
        (q ℚ.+ radius quarterε ℚOrder.≤_)
        (quarter-sum≡half ε)
        (ℚOrder.≤-+o q (radius quarterε) (radius quarterε) q≤quarter)

    d≤half : d ≤ᶜ rational (radius (half⁺ ε))
    d≤half =
      ≤ᶜ-trans
        {x = d}
        {y = rational (q ℚ.+ radius quarterε)}
        {z = rational (radius (half⁺ ε))}
        (close-rational-upper-bound d q δ quarterε δ<quarter d∼q)
        (≤ℚ→rational≤ᶜ q+quarter≤half)

  approxStep :
    Σ[ q ∈ ℚ ] d ∼[ δ ] rational q →
    (x <ᶜ z) Logic.⊔′ (z <ᶜ y)
  approxStep (q , d∼q) =
    Sum.rec left right (≤∨<ℚ q (radius quarterε))
    where
    left :
      radius quarterε ℚOrder.< q →
      (x <ᶜ z) Logic.⊔′ (z <ᶜ y)
    left quarter<q =
      ∣ Sum.inl (close-rational-positive d q δ quarterε δ<quarter quarter<q d∼q) ∣₁

    right :
      q ℚOrder.≤ radius quarterε →
      (x <ᶜ z) Logic.⊔′ (z <ᶜ y)
    right q≤quarter =
      ∣ Sum.inr (rightCase q d∼q q≤quarter) ∣₁


<ᶜ-weakly-linear :
  (x y z : ℝᶜ) →
  x <ᶜ y →
  (x <ᶜ z) Logic.⊔′ (z <ᶜ y)
<ᶜ-weakly-linear x y z =
  Prop.rec squash₁ λ (ε , ε≤y-x) →
    weak-linear-from-gap x y z ε ε≤y-x


CauchyReals<StrictOrder :
  StrictOrder.IsStrictOrder _<ᶜ_
CauchyReals<StrictOrder =
  StrictOrder.isstrictorder
    isSetCompletion
    isProp<ᶜ
    <ᶜ-irrefl
    (λ x y z → <ᶜ-trans {x = x} {y = y} {z = z})
    <ᶜ-asym
    <ᶜ-weakly-linear


sum-minus-left :
  (x y : ℝᶜ) →
  (x +ᶜ y) +ᶜ (-ᶜ x) ≡ y
sum-minus-left x y =
  cong (_+ᶜ (-ᶜ x)) (add-comm x y) ∙
  plus-minus-cancel-right y x


right-summand-positiveᶜ :
  (x y : ℝᶜ) →
  x <ᶜ (x +ᶜ y) →
  0ᶜ <ᶜ y
right-summand-positiveᶜ x y x<x+y =
  subst2 _<ᶜ_
    (add-inverse-right x)
    (sum-minus-left x y)
    (addᶜ-pres<ᶜ-right
      {x = x}
      {y = x +ᶜ y}
      (-ᶜ x)
      x<x+y)


positive-sum-splitᶜ :
  (x y : ℝᶜ) →
  0ᶜ <ᶜ (x +ᶜ y) →
  (0ᶜ <ᶜ x) Logic.⊔′ (0ᶜ <ᶜ y)
positive-sum-splitᶜ x y 0<x+y =
  Prop.rec squash₁ split (<ᶜ-weakly-linear 0ᶜ (x +ᶜ y) x 0<x+y)
  where
  split :
    (0ᶜ <ᶜ x) ⊎ (x <ᶜ (x +ᶜ y)) →
    (0ᶜ <ᶜ x) Logic.⊔′ (0ᶜ <ᶜ y)
  split (inl 0<x) =
    ∣ inl 0<x ∣₁
  split (inr x<x+y) =
    ∣ inr (right-summand-positiveᶜ x y x<x+y) ∣₁
