{-

Strictly ordered fields

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.StrictlyOrderedField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Field
open import Constructive.Algebra.StrictlyOrderedCommRing

private
  variable
    ℓ ℓ' : Level


IsFieldOnStrictlyOrderedCommRing : StrictlyOrderedCommRing ℓ ℓ' → Type ℓ
IsFieldOnStrictlyOrderedCommRing 𝓡 = IsField 0r 1r _+_ _·_ (-_)
  where
  open CommRingStr ((StrictlyOrderedCommRing→CommRing 𝓡) .snd)

StrictlyOrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
StrictlyOrderedField ℓ ℓ' =
  Σ[ 𝒦 ∈ StrictlyOrderedCommRing ℓ ℓ' ] IsFieldOnStrictlyOrderedCommRing 𝒦


StrictlyOrderedField→Field : StrictlyOrderedField ℓ ℓ' → Field ℓ
StrictlyOrderedField→Field 𝒦 .fst = 𝒦 .fst .fst .fst
StrictlyOrderedField→Field 𝒦 .snd = fieldstr _ _ _ _ _ (𝒦 .snd)


OrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedField = StrictlyOrderedField


OrderedField→Field : OrderedField ℓ ℓ' → Field ℓ
OrderedField→Field = StrictlyOrderedField→Field

isPropIsFieldOnStrictlyOrderedCommRing : (𝓡 : StrictlyOrderedCommRing ℓ ℓ') → isProp (IsFieldOnStrictlyOrderedCommRing 𝓡)
isPropIsFieldOnStrictlyOrderedCommRing 𝓡 = isPropIsField 0r 1r _+_ _·_ (-_)
  where
  open CommRingStr ((StrictlyOrderedCommRing→CommRing 𝓡) .snd)

liftPathIsFieldOnStrictlyOrderedCommRing :
  {𝓡 𝓡' : StrictlyOrderedCommRing ℓ ℓ'}(p : 𝓡 ≡ 𝓡')
  (h : IsFieldOnStrictlyOrderedCommRing 𝓡)(h' : IsFieldOnStrictlyOrderedCommRing 𝓡')
  → PathP (λ i → IsFieldOnStrictlyOrderedCommRing (p i)) h h'
liftPathIsFieldOnStrictlyOrderedCommRing p = isProp→PathP (λ i → isPropIsFieldOnStrictlyOrderedCommRing (p i))
