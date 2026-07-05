{-

Linearly ordered fields

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.LinearlyOrderedField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.Field
open import Cubical.Algebra.OrderedCommRing
  using (OrderedCommRing)
open import Constructive.Algebra.OrderedField.Base
open import Constructive.Algebra.LinearlyOrderedCommRing

private
  variable
    ℓ ℓ' : Level


IsFieldOnLinearlyOrderedCommRing : LinearlyOrderedCommRing ℓ ℓ' → Type ℓ
IsFieldOnLinearlyOrderedCommRing 𝓡 =
  IsFieldOnOrderedCommRing (LinearlyOrderedCommRing→OrderedCommRing 𝓡)

LinearlyOrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
LinearlyOrderedField ℓ ℓ' =
  Σ[ 𝒦 ∈ LinearlyOrderedCommRing ℓ ℓ' ] IsFieldOnLinearlyOrderedCommRing 𝒦


LinearlyOrderedField→OrderedField : LinearlyOrderedField ℓ ℓ' → OrderedField ℓ ℓ'
LinearlyOrderedField→OrderedField 𝒦 =
  LinearlyOrderedCommRing→OrderedCommRing (𝒦 .fst) , 𝒦 .snd


LinearlyOrderedField→Field : LinearlyOrderedField ℓ ℓ' → Field ℓ
LinearlyOrderedField→Field 𝒦 =
  OrderedField→Field (LinearlyOrderedField→OrderedField 𝒦)

isPropIsFieldOnLinearlyOrderedCommRing : (𝓡 : LinearlyOrderedCommRing ℓ ℓ') → isProp (IsFieldOnLinearlyOrderedCommRing 𝓡)
isPropIsFieldOnLinearlyOrderedCommRing 𝓡 =
  isPropIsFieldOnOrderedCommRing (LinearlyOrderedCommRing→OrderedCommRing 𝓡)

liftPathIsFieldOnLinearlyOrderedCommRing :
  {𝓡 𝓡' : LinearlyOrderedCommRing ℓ ℓ'}(p : 𝓡 ≡ 𝓡')
  (h : IsFieldOnLinearlyOrderedCommRing 𝓡)(h' : IsFieldOnLinearlyOrderedCommRing 𝓡')
  → PathP (λ i → IsFieldOnLinearlyOrderedCommRing (p i)) h h'
liftPathIsFieldOnLinearlyOrderedCommRing p = isProp→PathP (λ i → isPropIsFieldOnLinearlyOrderedCommRing (p i))
