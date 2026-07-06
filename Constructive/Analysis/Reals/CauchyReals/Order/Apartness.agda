{-# OPTIONS --safe #-}

module Constructive.Analysis.Reals.CauchyReals.Order.Apartness where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum as Sum using (_⊎_; inl; inr)
import Cubical.Functions.Logic as Logic
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Nullary

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.CauchyReals.Order.Tightness
open import Constructive.Analysis.Reals.CauchyReals.Order.WeakLinear


#ᶜ-irrefl : (x : ℝᶜ) → ¬ (x #ᶜ x)
#ᶜ-irrefl x (inl x<x) =
  <ᶜ-irrefl x x<x
#ᶜ-irrefl x (inr x<x) =
  <ᶜ-irrefl x x<x


0#1ᶜ : 0ᶜ #ᶜ 1ᶜ
0#1ᶜ =
  inl 0ᶜ<1ᶜ


addᶜ-pres#ᶜ-right :
  {x y : ℝᶜ} →
  (z : ℝᶜ) →
  x #ᶜ y →
  (x +ᶜ z) #ᶜ (y +ᶜ z)
addᶜ-pres#ᶜ-right {x = x} {y = y} z (inl x<y) =
  inl (addᶜ-pres<ᶜ-right {x = x} {y = y} z x<y)
addᶜ-pres#ᶜ-right {x = x} {y = y} z (inr y<x) =
  inr (addᶜ-pres<ᶜ-right {x = y} {y = x} z y<x)


addᶜ-pres#ᶜ-left :
  {x y : ℝᶜ} →
  (z : ℝᶜ) →
  x #ᶜ y →
  (z +ᶜ x) #ᶜ (z +ᶜ y)
addᶜ-pres#ᶜ-left {x = x} {y = y} z x#y =
  subst2 _#ᶜ_
    (add-comm x z)
    (add-comm y z)
    (addᶜ-pres#ᶜ-right {x = x} {y = y} z x#y)


addᶜ-reflect#ᶜ-right :
  {x y : ℝᶜ} →
  (z : ℝᶜ) →
  (x +ᶜ z) #ᶜ (y +ᶜ z) →
  x #ᶜ y
addᶜ-reflect#ᶜ-right {x = x} {y = y} z (inl x+z<y+z) =
  inl (addᶜ-reflect<ᶜ-right {x = x} {y = y} z x+z<y+z)
addᶜ-reflect#ᶜ-right {x = x} {y = y} z (inr y+z<x+z) =
  inr (addᶜ-reflect<ᶜ-right {x = y} {y = x} z y+z<x+z)


addᶜ-reflect#ᶜ-left :
  {x y : ℝᶜ} →
  (z : ℝᶜ) →
  (z +ᶜ x) #ᶜ (z +ᶜ y) →
  x #ᶜ y
addᶜ-reflect#ᶜ-left {x = x} {y = y} z z+x#z+y =
  addᶜ-reflect#ᶜ-right {x = x} {y = y} z
    (subst2 _#ᶜ_
      (add-comm z x)
      (add-comm z y)
      z+x#z+y)


#ᶜ→≢ :
  (x y : ℝᶜ) →
  x #ᶜ y →
  ¬ x ≡ y
#ᶜ→≢ x y (inl x<y) x≡y =
  <ᶜ-irrefl x
    (subst (λ z → x <ᶜ z) (sym x≡y) x<y)
#ᶜ→≢ x y (inr y<x) x≡y =
  <ᶜ-irrefl y
    (subst (λ z → y <ᶜ z) x≡y y<x)


#ᶜ→≢0 :
  (x : ℝᶜ) →
  x #ᶜ 0ᶜ →
  ¬ x ≡ 0ᶜ
#ᶜ→≢0 x =
  #ᶜ→≢ x 0ᶜ


≡→¬#ᶜ :
  {x y : ℝᶜ} →
  x ≡ y →
  ¬ x #ᶜ y
≡→¬#ᶜ {x = x} {y = y} x≡y x#y =
  #ᶜ→≢ x y x#y x≡y


#ᶜ-tight :
  (x y : ℝᶜ) →
  ¬ x #ᶜ y →
  x ≡ y
#ᶜ-tight x y ¬x#y =
  ≤ᶜ-antisym
    (¬>ᶜ→≤ᶜ x y (λ y<x → ¬x#y (inr y<x)))
    (¬>ᶜ→≤ᶜ y x (λ x<y → ¬x#y (inl x<y)))


#ᶜ-cotrans :
  (x y z : ℝᶜ) →
  x #ᶜ y →
  ∥ (x #ᶜ z) ⊎ (z #ᶜ y) ∥₁
#ᶜ-cotrans x y z (inl x<y) =
  Prop.rec squash₁ split (<ᶜ-weakly-linear x y z x<y)
  where
  split :
    (x <ᶜ z) ⊎ (z <ᶜ y) →
    ∥ (x #ᶜ z) ⊎ (z #ᶜ y) ∥₁
  split (inl x<z) =
    ∣ inl (inl x<z) ∣₁
  split (inr z<y) =
    ∣ inr (inl z<y) ∣₁
#ᶜ-cotrans x y z (inr y<x) =
  Prop.rec squash₁ split (<ᶜ-weakly-linear y x z y<x)
  where
  split :
    (y <ᶜ z) ⊎ (z <ᶜ x) →
    ∥ (x #ᶜ z) ⊎ (z #ᶜ y) ∥₁
  split (inl y<z) =
    ∣ inr (inr y<z) ∣₁
  split (inr z<x) =
    ∣ inl (inr z<x) ∣₁


negative-sum-splitᶜ :
  (x y : ℝᶜ) →
  (x +ᶜ y) <ᶜ 0ᶜ →
  (x <ᶜ 0ᶜ) Logic.⊔′ (y <ᶜ 0ᶜ)
negative-sum-splitᶜ x y x+y<0 =
  Prop.rec squash₁ split
    (positive-sum-splitᶜ (-ᶜ x) (-ᶜ y) 0<neg-sum)
  where
  0<neg-sum : 0ᶜ <ᶜ ((-ᶜ x) +ᶜ (-ᶜ y))
  0<neg-sum =
    subst
      (0ᶜ <ᶜ_)
      (neg-add x y)
      (negativeᶜ→positive-negᶜ (x +ᶜ y) x+y<0)

  split :
    (0ᶜ <ᶜ (-ᶜ x)) ⊎ (0ᶜ <ᶜ (-ᶜ y)) →
    (x <ᶜ 0ᶜ) Logic.⊔′ (y <ᶜ 0ᶜ)
  split (inl 0<-x) =
    ∣ inl (positive-negᶜ→negativeᶜ x 0<-x) ∣₁
  split (inr 0<-y) =
    ∣ inr (positive-negᶜ→negativeᶜ y 0<-y) ∣₁


addᶜ-reflects#0 :
  (x y : ℝᶜ) →
  (x +ᶜ y) #ᶜ 0ᶜ →
  ∥ (x #ᶜ 0ᶜ) ⊎ (y #ᶜ 0ᶜ) ∥₁
addᶜ-reflects#0 x y (inl x+y<0) =
  Prop.rec squash₁ split (negative-sum-splitᶜ x y x+y<0)
  where
  split :
    (x <ᶜ 0ᶜ) ⊎ (y <ᶜ 0ᶜ) →
    ∥ (x #ᶜ 0ᶜ) ⊎ (y #ᶜ 0ᶜ) ∥₁
  split (inl x<0) =
    ∣ inl (inl x<0) ∣₁
  split (inr y<0) =
    ∣ inr (inl y<0) ∣₁
addᶜ-reflects#0 x y (inr 0<x+y) =
  Prop.rec squash₁ split (positive-sum-splitᶜ x y 0<x+y)
  where
  split :
    (0ᶜ <ᶜ x) ⊎ (0ᶜ <ᶜ y) →
    ∥ (x #ᶜ 0ᶜ) ⊎ (y #ᶜ 0ᶜ) ∥₁
  split (inl 0<x) =
    ∣ inl (inr 0<x) ∣₁
  split (inr 0<y) =
    ∣ inr (inr 0<y) ∣₁
