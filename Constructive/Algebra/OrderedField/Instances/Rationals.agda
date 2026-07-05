{-

Rational numbers as an ordered field

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.OrderedField.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Field.Instances.Rationals
  using (ℚField)
import Cubical.Algebra.Field as CubicalField

open import Constructive.Algebra.OrderedField
open import Constructive.Algebra.LinearlyOrderedCommRing.Instances.Rationals
  using (ℚOrderedCommRing)


ℚOrderedField : OrderedField ℓ-zero ℓ-zero
ℚOrderedField =
  ℚOrderedCommRing , CubicalField.FieldStr.isField (ℚField .snd)
