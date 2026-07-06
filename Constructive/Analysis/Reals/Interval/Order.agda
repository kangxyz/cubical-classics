{-

Order and inclusion lemmas for closed intervals of HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Interval.Order where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma using (Σ≡Prop)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.Interval


gapᶜ : ℝᶜ → ℝᶜ → ℝᶜ
gapᶜ a b =
  b +ᶜ (-ᶜ a)


leftPlusGapᶜ :
  (a b : ℝᶜ) →
  a +ᶜ gapᶜ a b ≡ b
leftPlusGapᶜ a b =
  add-comm a (gapᶜ a b) ∙
  minus-plus-cancel-right b a


intervalInclusion :
  {a b a' b' : ℝᶜ} →
  a' ≤ᶜ a →
  b ≤ᶜ b' →
  [ a , b ]ᶜ →
  [ a' , b' ]ᶜ
intervalInclusion {a = a} {b = b} {a' = a'} {b' = b'} a'≤a b≤b' x =
  pointᶜ {a = a} {b = b} x ,
  ≤ᶜ-trans {x = a'} {y = a} {z = pointᶜ {a = a} {b = b} x}
    a'≤a
    (lowerBoundᶜ {a = a} {b = b} x) ,
  ≤ᶜ-trans {x = pointᶜ {a = a} {b = b} x} {y = b} {z = b'}
    (upperBoundᶜ {a = a} {b = b} x)
    b≤b'


intervalPointPath :
  {a b : ℝᶜ} →
  {x y : [ a , b ]ᶜ} →
  pointᶜ {a = a} {b = b} x ≡ pointᶜ {a = a} {b = b} y →
  x ≡ y
intervalPointPath {a = a} {b = b} =
  Σ≡Prop (isPropIntervalBounds a b)
