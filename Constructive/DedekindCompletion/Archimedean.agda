{-

Archimedean linearly ordered fields and their Dedekind completions

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindCompletion.Archimedean where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedes
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.DedekindCompletion.Base
open import Constructive.DedekindCompletion.Order

private
  variable
    ℓ ℓ' : Level


ArchimedeanLinearlyOrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
ArchimedeanLinearlyOrderedField ℓ ℓ' =
  Σ[ 𝒦 ∈ LinearlyOrderedField ℓ ℓ' ] isArchimedean (𝒦 .fst)


module ArchimedeanCompletion (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') where

  𝒦 : LinearlyOrderedField ℓ ℓ'
  𝒦 = 𝒜 .fst

  archimedes : isArchimedean (𝒦 .fst)
  archimedes = 𝒜 .snd

  open CompletionBase 𝒦 public
  open CompletionOrder 𝒦 public
