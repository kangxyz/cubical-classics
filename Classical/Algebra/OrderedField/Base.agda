{-

Totally Ordered Field

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Field
open import Classical.Algebra.StrictlyOrderedCommRing

private
  variable
    ℓ ℓ' : Level


IsFieldOnStrictlyOrderedCommRing : StrictlyOrderedCommRing ℓ ℓ' → Type ℓ
IsFieldOnStrictlyOrderedCommRing 𝓡 = IsField 0r 1r _+_ _·_ (-_)
  where
  open CommRingStr ((StrictlyOrderedCommRing→CommRing 𝓡) .snd)

OrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedField ℓ ℓ' = Σ[ 𝒦 ∈ StrictlyOrderedCommRing ℓ ℓ' ] IsFieldOnStrictlyOrderedCommRing 𝒦

OrderedField→Field : OrderedField ℓ ℓ' → Field ℓ
OrderedField→Field 𝒦 .fst = 𝒦 .fst .fst .fst
OrderedField→Field 𝒦 .snd = fieldstr _ _ _ _ _ (𝒦 .snd)

isPropIsFieldOnStrictlyOrderedCommRing : (𝓡 : StrictlyOrderedCommRing ℓ ℓ') → isProp (IsFieldOnStrictlyOrderedCommRing 𝓡)
isPropIsFieldOnStrictlyOrderedCommRing 𝓡 = isPropIsField 0r 1r _+_ _·_ (-_)
  where
  open CommRingStr ((StrictlyOrderedCommRing→CommRing 𝓡) .snd)

liftPathIsFieldOnStrictlyOrderedCommRing :
  {𝓡 𝓡' : StrictlyOrderedCommRing ℓ ℓ'}(p : 𝓡 ≡ 𝓡')
  (h : IsFieldOnStrictlyOrderedCommRing 𝓡)(h' : IsFieldOnStrictlyOrderedCommRing 𝓡')
  → PathP (λ i → IsFieldOnStrictlyOrderedCommRing (p i)) h h'
liftPathIsFieldOnStrictlyOrderedCommRing p = isProp→PathP (λ i → isPropIsFieldOnStrictlyOrderedCommRing (p i))
