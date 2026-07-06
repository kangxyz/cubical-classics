{-

Ordered-Heyting-field packaging for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedHeytingField where

open import Cubical.Foundations.Prelude

open import Constructive.Algebra.OrderedHeytingField.Base
  using (IsHeytingFieldOnOrderedCommRing; OrderedHeytingField)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Inverse
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing


CauchyRealsIsHeytingFieldOnOrderedCommRing-from-positive :
  PositiveRightInverseProviderᶜ →
  IsHeytingFieldOnOrderedCommRing CauchyRealsOrderedCommRing
CauchyRealsIsHeytingFieldOnOrderedCommRing-from-positive inv₊
  .IsHeytingFieldOnOrderedCommRing.inv# =
    inv#ᶜ-from-positive inv₊


CauchyRealsOrderedHeytingField-from-positive :
  PositiveRightInverseProviderᶜ →
  OrderedHeytingField ℓ-zero ℓ-zero
CauchyRealsOrderedHeytingField-from-positive inv₊ =
  CauchyRealsOrderedCommRing ,
  CauchyRealsIsHeytingFieldOnOrderedCommRing-from-positive inv₊


CauchyRealsIsHeytingFieldOnOrderedCommRing :
  IsHeytingFieldOnOrderedCommRing CauchyRealsOrderedCommRing
CauchyRealsIsHeytingFieldOnOrderedCommRing =
  CauchyRealsIsHeytingFieldOnOrderedCommRing-from-positive
    positive-right-inverseᶜ


CauchyRealsOrderedHeytingField :
  OrderedHeytingField ℓ-zero ℓ-zero
CauchyRealsOrderedHeytingField =
  CauchyRealsOrderedHeytingField-from-positive positive-right-inverseᶜ
