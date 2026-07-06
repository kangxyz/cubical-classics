{-

Additive group of HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace


CauchyRealsAbGroup : AbGroup ℓ-zero
CauchyRealsAbGroup =
  makeAbGroup 0ᶜ _+ᶜ_ -ᶜ_ isSetCompletion
    add-assoc add-zero-right add-inverse-right add-comm


module CauchyRealsAbGroupTheory =
  AbGroupTheory CauchyRealsAbGroup


module CauchyRealsGroupTheory =
  GroupTheory (AbGroup→Group CauchyRealsAbGroup)


add-interchange :
  (a b c d : ℝᶜ) →
  (a +ᶜ b) +ᶜ (c +ᶜ d) ≡ (a +ᶜ c) +ᶜ (b +ᶜ d)
add-interchange =
  CauchyRealsAbGroupTheory.comm-4


add-cancel-right :
  (x y z : ℝᶜ) →
  x +ᶜ z ≡ y +ᶜ z →
  x ≡ y
add-cancel-right x y z =
  CauchyRealsGroupTheory.·CancelR z


add-cancel-left :
  (x y z : ℝᶜ) →
  z +ᶜ x ≡ z +ᶜ y →
  x ≡ y
add-cancel-left x y z =
  CauchyRealsGroupTheory.·CancelL z


inverse-unique-right :
  (x y : ℝᶜ) →
  x +ᶜ y ≡ 0ᶜ →
  -ᶜ x ≡ y
inverse-unique-right x y x+y≡0 =
  sym (CauchyRealsGroupTheory.invUniqueR {g = x} {h = y} x+y≡0)


inverse-unique-left :
  (x y : ℝᶜ) →
  y +ᶜ x ≡ 0ᶜ →
  -ᶜ x ≡ y
inverse-unique-left x y y+x≡0 =
  sym (CauchyRealsGroupTheory.invUniqueL {g = y} {h = x} y+x≡0)


neg-add :
  (a b : ℝᶜ) →
  -ᶜ (a +ᶜ b) ≡ (-ᶜ a) +ᶜ (-ᶜ b)
neg-add a b =
  CauchyRealsGroupTheory.invDistr a b ∙
  add-comm (-ᶜ b) (-ᶜ a)


plus-minus-cancel-right :
  (x y : ℝᶜ) →
  (x +ᶜ y) +ᶜ (-ᶜ y) ≡ x
plus-minus-cancel-right x y =
  sym (add-assoc x y (-ᶜ y)) ∙
  cong (x +ᶜ_) (add-inverse-right y) ∙
  add-zero-right x


minus-plus-cancel-right :
  (x y : ℝᶜ) →
  (x +ᶜ (-ᶜ y)) +ᶜ y ≡ x
minus-plus-cancel-right x y =
  sym (add-assoc x (-ᶜ y) y) ∙
  cong (x +ᶜ_) (add-inverse-left y) ∙
  add-zero-right x
