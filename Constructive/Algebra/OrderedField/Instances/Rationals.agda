{-

Rational numbers as a constructive ordered field.

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.OrderedField.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Algebra.Field
open import Cubical.Algebra.Field.Instances.Rationals
  using (ℚField)
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Relation.Nullary using (¬_)

open import Constructive.Algebra.OrderedField
open import Constructive.Algebra.StrictlyOrderedCommRing.Instances.Rationals
  using (ℚOrderedCommRing)


private
  module OCR = OrderedCommRingStr (ℚOrderedCommRing .snd)
  module F = FieldStr (ℚField .snd)

  #→≠0 : (q : ℚ) → OrderedCommRingApartness._#_ ℚOrderedCommRing q OCR.0r → ¬ q ≡ OCR.0r
  #→≠0 q (Sum.inl q<0) q≡0 =
    ℚOrder.isIrrefl< OCR.0r
      (subst (λ r → r ℚOrder.< OCR.0r) q≡0 q<0)
  #→≠0 q (Sum.inr 0<q) q≡0 =
    ℚOrder.isIrrefl< OCR.0r
      (subst (λ r → OCR.0r ℚOrder.< r) q≡0 0<q)


ℚIsOrderedField : IsOrderedField ℚOrderedCommRing
ℚIsOrderedField .IsOrderedField.inverse# q q#0 =
  F._[_]⁻¹ q (#→≠0 q q#0) ,
  F.·⁻¹≡1 q (#→≠0 q q#0)
ℚIsOrderedField .IsOrderedField.0#1 =
  Sum.inl OCR.0<1


ℚOrderedField : OrderedField ℓ-zero ℓ-zero
ℚOrderedField = ℚOrderedCommRing , ℚIsOrderedField
