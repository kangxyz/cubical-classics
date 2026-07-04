{-

Constructive ordered fields

The order is Cubical's weak ordered commutative-ring structure.  Multiplicative
inverses are required only for elements apart from zero.

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


module Apartness (𝓡 : OrderedCommRing ℓ ℓ') where
  open OrderedCommRingStr (𝓡 .snd)

  _#_ : 𝓡 .fst → 𝓡 .fst → Type ℓ'
  x # y = (x < y) ⊎ (y < x)

  infix 4 _#_


record IsOrderedField (𝓡 : OrderedCommRing ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality

  open OrderedCommRingStr (𝓡 .snd)
  open Apartness 𝓡

  field
    inv# :
      (x : 𝓡 .fst) →
      x # 0r →
      Σ[ y ∈ 𝓡 .fst ] x · y ≡ 1r

    0#1 : 0r # 1r

  ·-lInv# :
    (x : 𝓡 .fst) →
    x # 0r →
    Σ[ y ∈ 𝓡 .fst ] y · x ≡ 1r
  ·-lInv# x x#0 =
    y , ·Comm y x ∙ y-right
    where
    y : 𝓡 .fst
    y = inv# x x#0 .fst

    y-right : x · y ≡ 1r
    y-right = inv# x x#0 .snd


OrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedField ℓ ℓ' = Σ[ 𝓡 ∈ OrderedCommRing ℓ ℓ' ] IsOrderedField 𝓡


OrderedField→OrderedCommRing : OrderedField ℓ ℓ' → OrderedCommRing ℓ ℓ'
OrderedField→OrderedCommRing = fst


OrderedField→CommRing : OrderedField ℓ ℓ' → CommRing ℓ
OrderedField→CommRing 𝒦 = OrderedCommRing→CommRing (OrderedField→OrderedCommRing 𝒦)


module OrderedFieldStr (𝒦 : OrderedField ℓ ℓ') where
  open OrderedCommRingStr (𝒦 .fst .snd) public
  open Apartness (𝒦 .fst) public
  open IsOrderedField (𝒦 .snd) public
