{-

Morphisms between constructive ordered fields

These are homomorphisms of the underlying ordered commutative rings.

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.OrderedField.Morphism where

open import Cubical.Foundations.Prelude

open import Constructive.Algebra.OrderedCommRing.Morphism
open import Constructive.Algebra.OrderedField.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


OrderedFieldHom : OrderedField ℓ ℓ' → OrderedField ℓ'' ℓ''' → Type _
OrderedFieldHom 𝒦 𝒦' =
  OrderedCommRingHom
    (OrderedField→OrderedCommRing 𝒦)
    (OrderedField→OrderedCommRing 𝒦')
