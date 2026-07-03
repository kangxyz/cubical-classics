{-

Totally Ordered Field

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Classical.Algebra.Field
open import Classical.Algebra.OrderedRing

private
  variable
    ℓ ℓ' : Level


IsFieldOnOrderedRing : OrderedRing ℓ ℓ' → Type ℓ
IsFieldOnOrderedRing 𝓡 = IsField 0r 1r _+_ _·_ (-_)
  where
  open CommRingStr (𝓡 .fst .snd)

OrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedField ℓ ℓ' = Σ[ 𝒦 ∈ OrderedRing ℓ ℓ' ] IsFieldOnOrderedRing 𝒦

OrderedField→Field : OrderedField ℓ ℓ' → Field ℓ
OrderedField→Field 𝒦 .fst = 𝒦 .fst .fst .fst
OrderedField→Field 𝒦 .snd = fieldstr _ _ _ _ _ (𝒦 .snd)

isPropIsFieldOnOrderedRing : (𝓡 : OrderedRing ℓ ℓ') → isProp (IsFieldOnOrderedRing 𝓡)
isPropIsFieldOnOrderedRing 𝓡 = isPropIsField 0r 1r _+_ _·_ (-_)
  where
  open CommRingStr (𝓡 .fst .snd)

liftPathIsFieldOnOrderedRing :
  {𝓡 𝓡' : OrderedRing ℓ ℓ'}(p : 𝓡 ≡ 𝓡')
  (h : IsFieldOnOrderedRing 𝓡)(h' : IsFieldOnOrderedRing 𝓡')
  → PathP (λ i → IsFieldOnOrderedRing (p i)) h h'
liftPathIsFieldOnOrderedRing p = isProp→PathP (λ i → isPropIsFieldOnOrderedRing (p i))
