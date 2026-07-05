{-

The rational base field as an Archimedean linearly ordered field

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindCompletion.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Constructive.Algebra.LinearlyOrderedField.Instances.Rationals
open import Constructive.DedekindCompletion.Archimedean


ℚArchimedeanLinearlyOrderedField : ArchimedeanLinearlyOrderedField ℓ-zero ℓ-zero
ℚArchimedeanLinearlyOrderedField =
  ℚLinearlyOrderedField , isArchimedeanℚ


module ℚCompletion =
  ArchimedeanCompletion ℚArchimedeanLinearlyOrderedField
