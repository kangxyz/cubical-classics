{-

Linearly ordered fields

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.LinearlyOrderedField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Field
open import Constructive.Algebra.LinearlyOrderedCommRing

private
  variable
    ℓ ℓ' : Level


IsFieldOnLinearlyOrderedCommRing : LinearlyOrderedCommRing ℓ ℓ' → Type ℓ
IsFieldOnLinearlyOrderedCommRing 𝓡 = IsField 0r 1r _+_ _·_ (-_)
  where
  open CommRingStr ((LinearlyOrderedCommRing→CommRing 𝓡) .snd)

LinearlyOrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
LinearlyOrderedField ℓ ℓ' =
  Σ[ 𝒦 ∈ LinearlyOrderedCommRing ℓ ℓ' ] IsFieldOnLinearlyOrderedCommRing 𝒦


LinearlyOrderedField→Field : LinearlyOrderedField ℓ ℓ' → Field ℓ
LinearlyOrderedField→Field 𝒦 .fst = 𝒦 .fst .fst .fst
LinearlyOrderedField→Field 𝒦 .snd = fieldstr _ _ _ _ _ (𝒦 .snd)


OrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedField = LinearlyOrderedField


OrderedField→Field : OrderedField ℓ ℓ' → Field ℓ
OrderedField→Field = LinearlyOrderedField→Field

isPropIsFieldOnLinearlyOrderedCommRing : (𝓡 : LinearlyOrderedCommRing ℓ ℓ') → isProp (IsFieldOnLinearlyOrderedCommRing 𝓡)
isPropIsFieldOnLinearlyOrderedCommRing 𝓡 = isPropIsField 0r 1r _+_ _·_ (-_)
  where
  open CommRingStr ((LinearlyOrderedCommRing→CommRing 𝓡) .snd)

liftPathIsFieldOnLinearlyOrderedCommRing :
  {𝓡 𝓡' : LinearlyOrderedCommRing ℓ ℓ'}(p : 𝓡 ≡ 𝓡')
  (h : IsFieldOnLinearlyOrderedCommRing 𝓡)(h' : IsFieldOnLinearlyOrderedCommRing 𝓡')
  → PathP (λ i → IsFieldOnLinearlyOrderedCommRing (p i)) h h'
liftPathIsFieldOnLinearlyOrderedCommRing p = isProp→PathP (λ i → isPropIsFieldOnLinearlyOrderedCommRing (p i))
