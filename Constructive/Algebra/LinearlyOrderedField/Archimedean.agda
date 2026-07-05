{-

Archimedean linearly ordered fields

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.LinearlyOrderedField.Archimedean where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField.Base

private
  variable
    ℓ ℓ' : Level


ArchimedeanLinearlyOrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
ArchimedeanLinearlyOrderedField ℓ ℓ' =
  Σ[ 𝒦 ∈ LinearlyOrderedField ℓ ℓ' ] isArchimedean (𝒦 .fst)
