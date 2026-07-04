{-

Constructive ordered fields.

This is the LEM-free ordered-field interface: the order is the weak ordered
commutative-ring structure from Cubical, and multiplicative inverses are
required only for elements apart from zero.  The trichotomous/inequality-based
field interface lives in `Constructive.Algebra.StrictlyOrderedField`.

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.OrderedField.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing

private
  variable
    ℓ ℓ' : Level


module OrderedCommRingApartness (𝓡 : OrderedCommRing ℓ ℓ') where
  open OrderedCommRingStr (𝓡 .snd)

  _#_ : 𝓡 .fst → 𝓡 .fst → Type ℓ'
  x # y = (x < y) ⊎ (y < x)

  infix 4 _#_


record IsOrderedField (𝓡 : OrderedCommRing ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality

  open OrderedCommRingStr (𝓡 .snd)
  open OrderedCommRingApartness 𝓡

  field
    inverse# :
      (x : 𝓡 .fst) →
      x # 0r →
      Σ[ y ∈ 𝓡 .fst ] x · y ≡ 1r

    0#1 : 0r # 1r

  inverse#-left :
    (x : 𝓡 .fst) →
    x # 0r →
    Σ[ y ∈ 𝓡 .fst ] y · x ≡ 1r
  inverse#-left x x#0 =
    y , ·Comm y x ∙ y-right
    where
    y : 𝓡 .fst
    y = inverse# x x#0 .fst

    y-right : x · y ≡ 1r
    y-right = inverse# x x#0 .snd


OrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedField ℓ ℓ' = Σ[ 𝓡 ∈ OrderedCommRing ℓ ℓ' ] IsOrderedField 𝓡


OrderedField→OrderedCommRing : OrderedField ℓ ℓ' → OrderedCommRing ℓ ℓ'
OrderedField→OrderedCommRing = fst


OrderedField→CommRing : OrderedField ℓ ℓ' → CommRing ℓ
OrderedField→CommRing 𝒦 = OrderedCommRing→CommRing (OrderedField→OrderedCommRing 𝒦)


module OrderedFieldStr (𝒦 : OrderedField ℓ ℓ') where
  open OrderedCommRingStr (𝒦 .fst .snd) public
  open OrderedCommRingApartness (𝒦 .fst) public
  open IsOrderedField (𝒦 .snd) public
