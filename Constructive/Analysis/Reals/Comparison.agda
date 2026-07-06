{-

Comparison maps between constructive real-number presentations

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

import Constructive.Data.Rationals as Rational
open import Constructive.Data.PositiveRationals
import Constructive.Analysis.Reals.DedekindReals as Dedekind
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.CauchyReals.Order.WeakLinear

module D = Dedekind.Base


private
  lower-inhabitedᶜ :
    (x : ℝᶜ) →
    ∥ Σ[ q ∈ ℚ ] rational q <ᶜ x ∥₁
  lower-inhabitedᶜ x =
    Prop.rec squash₁ step (merely-boundedᶜ x)
    where
    step :
      Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ x →
      ∥ Σ[ q ∈ ℚ ] rational q <ᶜ x ∥₁
    step (κ , bound) =
      ∣ q , q<x ∣₁
      where
      q : ℚ
      q = (ℚ.- radius κ) ℚ.- Rational.1ℚ

      -κ≤x : rational (ℚ.- radius κ) ≤ᶜ x
      -κ≤x =
        subst2 _≤ᶜ_
          (neg-rational (radius κ))
          (neg-involutive x)
          (negᶜ-pres≤ᶜ
            {x = -ᶜ x}
            {y = rational (radius κ)}
            (lowerᶜ bound))

      q<-κ : q ℚOrder.< ℚ.- radius κ
      q<-κ =
        Rational.q-1<q (ℚ.- radius κ)

      q<x : rational q <ᶜ x
      q<x =
        <ᶜ-≤ᶜ-trans
          (rational q)
          (rational (ℚ.- radius κ))
          x
          (<ℚ→<ᶜ {q = q} {r = ℚ.- radius κ} q<-κ)
          -κ≤x


  upper-inhabitedᶜ :
    (x : ℝᶜ) →
    ∥ Σ[ q ∈ ℚ ] x <ᶜ rational q ∥₁
  upper-inhabitedᶜ x =
    Prop.rec squash₁ step (merely-boundedᶜ x)
    where
    step :
      Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ x →
      ∥ Σ[ q ∈ ℚ ] x <ᶜ rational q ∥₁
    step (κ , bound) =
      ∣ q , x<q ∣₁
      where
      q : ℚ
      q = radius κ ℚ.+ Rational.1ℚ

      κ<q : radius κ ℚOrder.< q
      κ<q =
        Rational.q<q+1 (radius κ)

      x<q : x <ᶜ rational q
      x<q =
        ≤ᶜ-<ᶜ-trans
          x
          (rational (radius κ))
          (rational q)
          (upperᶜ bound)
          (<ℚ→<ᶜ {q = radius κ} {r = q} κ<q)


  lower-roundedᶜ :
    (x : ℝᶜ) (q : ℚ) →
    rational q <ᶜ x →
    ∥ Σ[ r ∈ ℚ ] (q ℚOrder.< r) × (rational r <ᶜ x) ∥₁
  lower-roundedᶜ x q =
    Prop.rec squash₁ step
    where
    step :
      Σ[ ε ∈ ℚ⁺ ]
        rational (radius ε) ≤ᶜ (x +ᶜ (-ᶜ rational q)) →
      ∥ Σ[ r ∈ ℚ ] (q ℚOrder.< r) × (rational r <ᶜ x) ∥₁
    step (ε , ε≤x-q) =
      ∣ r , q<r , r<x ∣₁
      where
      η : ℚ⁺
      η = half⁺ ε

      r : ℚ
      r = q ℚ.+ radius η

      η<x-q : rational (radius η) <ᶜ (x +ᶜ (-ᶜ rational q))
      η<x-q =
        <ᶜ-≤ᶜ-trans
          (rational (radius η))
          (rational (radius ε))
          (x +ᶜ (-ᶜ rational q))
          (<ℚ→<ᶜ {q = radius η} {r = radius ε} (half< ε))
          ε≤x-q

      η+q<x :
        (rational (radius η) +ᶜ rational q) <ᶜ
        ((x +ᶜ (-ᶜ rational q)) +ᶜ rational q)
      η+q<x =
        addᶜ-pres<ᶜ-right
          {x = rational (radius η)}
          {y = x +ᶜ (-ᶜ rational q)}
          (rational q)
          η<x-q

      q<r : q ℚOrder.< r
      q<r =
        Rational.q<q+positive q (radius η) (η .snd)

      r<x : rational r <ᶜ x
      r<x =
        subst2 _<ᶜ_
          (add-rational (radius η) q ∙
           cong rational (ℚ.+Comm (radius η) q))
          (minus-plus-cancel-right x (rational q))
          η+q<x


  upper-roundedᶜ :
    (x : ℝᶜ) (q : ℚ) →
    x <ᶜ rational q →
    ∥ Σ[ r ∈ ℚ ] (r ℚOrder.< q) × (x <ᶜ rational r) ∥₁
  upper-roundedᶜ x q =
    Prop.rec squash₁ step
    where
    step :
      Σ[ ε ∈ ℚ⁺ ]
        rational (radius ε) ≤ᶜ (rational q +ᶜ (-ᶜ x)) →
      ∥ Σ[ r ∈ ℚ ] (r ℚOrder.< q) × (x <ᶜ rational r) ∥₁
    step (ε , ε≤q-x) =
      ∣ r , r<q , x<r ∣₁
      where
      η : ℚ⁺
      η = half⁺ ε

      r : ℚ
      r = q ℚ.- radius η

      η<q-x : rational (radius η) <ᶜ (rational q +ᶜ (-ᶜ x))
      η<q-x =
        <ᶜ-≤ᶜ-trans
          (rational (radius η))
          (rational (radius ε))
          (rational q +ᶜ (-ᶜ x))
          (<ℚ→<ᶜ {q = radius η} {r = radius ε} (half< ε))
          ε≤q-x

      x+η<q : (x +ᶜ rational (radius η)) <ᶜ rational q
      x+η<q =
        subst2 _<ᶜ_
          (add-comm (rational (radius η)) x)
          (minus-plus-cancel-right (rational q) x)
          (addᶜ-pres<ᶜ-right
            {x = rational (radius η)}
            {y = rational q +ᶜ (-ᶜ x)}
            x
            η<q-x)

      x+η-η<q-η :
        ((x +ᶜ rational (radius η)) +ᶜ (-ᶜ rational (radius η))) <ᶜ
        (rational q +ᶜ (-ᶜ rational (radius η)))
      x+η-η<q-η =
        addᶜ-pres<ᶜ-right
          {x = x +ᶜ rational (radius η)}
          {y = rational q}
          (-ᶜ rational (radius η))
          x+η<q

      r<q : r ℚOrder.< q
      r<q =
        Rational.<+→diff< q q (radius η)
          (Rational.q<q+positive q (radius η) (η .snd))

      x<r : x <ᶜ rational r
      x<r =
        subst2 _<ᶜ_
          (plus-minus-cancel-right x (rational (radius η)))
          (cong (rational q +ᶜ_) (neg-rational (radius η)) ∙
           add-rational q (ℚ.- radius η))
          x+η-η<q-η


ℝᶜ→ℝᴰ : (ℓ : Level) → ℝᶜ → Dedekind.ℝᴰ ℓ
ℝᶜ→ℝᴰ ℓ x .D.lower q =
  Lift ℓ (rational q <ᶜ x) ,
  isOfHLevelLift 1 (isProp<ᶜ (rational q) x)
ℝᶜ→ℝᴰ ℓ x .D.upper q =
  Lift ℓ (x <ᶜ rational q) ,
  isOfHLevelLift 1 (isProp<ᶜ x (rational q))
ℝᶜ→ℝᴰ ℓ x .D.isDedekindCut .D.IsDedekindCut.lower-inhabited =
  Prop.rec squash₁
    (λ (q , q<x) → ∣ q , lift q<x ∣₁)
    (lower-inhabitedᶜ x)
ℝᶜ→ℝᴰ ℓ x .D.isDedekindCut .D.IsDedekindCut.upper-inhabited =
  Prop.rec squash₁
    (λ (q , x<q) → ∣ q , lift x<q ∣₁)
    (upper-inhabitedᶜ x)
ℝᶜ→ℝᴰ ℓ x .D.isDedekindCut .D.IsDedekindCut.lower-closed =
  λ p q p<q q∈L →
    lift
      (<ᶜ-trans
        {x = rational p}
        {y = rational q}
        {z = x}
        (<ℚ→<ᶜ {q = p} {r = q} p<q)
        (Lift.lower q∈L))
ℝᶜ→ℝᴰ ℓ x .D.isDedekindCut .D.IsDedekindCut.upper-closed =
  λ p q p<q p∈U →
    lift
      (<ᶜ-trans
        {x = x}
        {y = rational p}
        {z = rational q}
        (Lift.lower p∈U)
        (<ℚ→<ᶜ {q = p} {r = q} p<q))
ℝᶜ→ℝᴰ ℓ x .D.isDedekindCut .D.IsDedekindCut.lower-rounded =
  λ q q∈L →
    Prop.rec squash₁
      (λ (r , q<r , r<x) → ∣ r , q<r , lift r<x ∣₁)
      (lower-roundedᶜ x q (Lift.lower q∈L))
ℝᶜ→ℝᴰ ℓ x .D.isDedekindCut .D.IsDedekindCut.upper-rounded =
  λ q q∈U →
    Prop.rec squash₁
      (λ (r , r<q , x<r) → ∣ r , r<q , lift x<r ∣₁)
      (upper-roundedᶜ x q (Lift.lower q∈U))
ℝᶜ→ℝᴰ ℓ x .D.isDedekindCut .D.IsDedekindCut.disjoint =
  λ q q∈L q∈U →
    <ᶜ-asym (rational q) x (Lift.lower q∈L) (Lift.lower q∈U)
ℝᶜ→ℝᴰ ℓ x .D.isDedekindCut .D.IsDedekindCut.located =
  λ p q p<q →
    Prop.rec squash₁
      (λ where
        (Sum.inl p<x) → ∣ Sum.inl (lift p<x) ∣₁
        (Sum.inr x<q) → ∣ Sum.inr (lift x<q) ∣₁)
      (<ᶜ-weakly-linear
        (rational p)
        (rational q)
        x
        (<ℚ→<ᶜ {q = p} {r = q} p<q))


ℝᶜ→ℝᴰ-rational :
  (ℓ : Level) (q : ℚ) →
  ℝᶜ→ℝᴰ ℓ (rational q) ≡ Dedekind.ℚ→ℝᴰ ℓ q
ℝᶜ→ℝᴰ-rational ℓ q =
  D.completionExt
    (ℝᶜ→ℝᴰ ℓ (rational q))
    (Dedekind.ℚ→ℝᴰ ℓ q)
    (λ p p<qᶜ →
      lift (<ᶜ-rational→<ℚ {q = p} {r = q} (Lift.lower p<qᶜ)))
    (λ p p<q → lift (<ℚ→<ᶜ {q = p} {r = q} (Lift.lower p<q)))
    (λ p q<ᶜp →
      lift (<ᶜ-rational→<ℚ {q = q} {r = p} (Lift.lower q<ᶜp)))
    (λ p q<p → lift (<ℚ→<ᶜ {q = q} {r = p} (Lift.lower q<p)))
