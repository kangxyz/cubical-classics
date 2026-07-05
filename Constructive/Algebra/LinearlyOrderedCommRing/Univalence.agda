{-

SIP for linearly ordered commutative rings

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Algebra.LinearlyOrderedCommRing.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing

open import Constructive.Algebra.OrderedCommRing.Morphism
open import Constructive.Algebra.OrderedCommRing.Univalence
open import Constructive.Algebra.LinearlyOrderedCommRing
import Constructive.Algebra.LinearlyOrderedCommRing.Base as LinearBase
import Constructive.Algebra.LinearlyOrderedCommRing.Morphism as LinearMorphism

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    𝓡  : LinearlyOrderedCommRing ℓ   ℓ'
    𝓡' : LinearlyOrderedCommRing ℓ'' ℓ'''


{-

  Equivalence of linearly ordered commutative rings

-}

open OrderedCommRingHom

isLinearlyOrderedCommRingEquiv : OrderedCommRingHom (𝓡 .fst) (𝓡' .fst) → Type _
isLinearlyOrderedCommRingEquiv f = isEquiv (f .ring-hom .fst)


isPropLinearOrderStrOnOrderedCommRing :
  (𝓡ᶜ : OrderedCommRing ℓ ℓ') → isProp (LinearOrderStrOnOrderedCommRing 𝓡ᶜ)
isPropLinearOrderStrOnOrderedCommRing 𝓡ᶜ s t i .LinearOrderStrOnOrderedCommRing.trichotomy =
  isPropΠ2 (LinearBase.isPropTrichotomy 𝓡ᶜ) (s .LinearOrderStrOnOrderedCommRing.trichotomy) (t .LinearOrderStrOnOrderedCommRing.trichotomy) i


module _ {𝓡 𝓡' : LinearlyOrderedCommRing ℓ ℓ'}
  {f : OrderedCommRingHom (𝓡 .fst) (𝓡' .fst)}
  (isEquiv-f : isLinearlyOrderedCommRingEquiv {𝓡 = 𝓡} {𝓡' = 𝓡'} f) where

  private
    𝓡ᵒ  = 𝓡 .fst
    𝓡'ᵒ = 𝓡' .fst

  module R  = OrderedCommRingStr (𝓡ᵒ .snd)
  module R' = OrderedCommRingStr (𝓡'ᵒ .snd)

  open OrderedCommRingHom f
  open LinearMorphism.OrderedCommRingHomProperties {𝓡 = 𝓡} {𝓡' = 𝓡'} f
  open IsCommRingHom (f .ring-hom .snd)

  orderedCommRingEquiv : OrderedCommRingEquiv 𝓡ᵒ 𝓡'ᵒ
  orderedCommRingEquiv .fst = f .ring-hom .fst , isEquiv-f
  orderedCommRingEquiv .snd .IsOrderedCommRingEquiv.pres0 = pres0
  orderedCommRingEquiv .snd .IsOrderedCommRingEquiv.pres1 = pres1
  orderedCommRingEquiv .snd .IsOrderedCommRingEquiv.pres+ = pres+
  orderedCommRingEquiv .snd .IsOrderedCommRingEquiv.pres· = pres·
  orderedCommRingEquiv .snd .IsOrderedCommRingEquiv.pres- = pres-
  orderedCommRingEquiv .snd .IsOrderedCommRingEquiv.pres< x y =
    propBiimpl→Equiv (R.is-prop-valued< x y) (R'.is-prop-valued< _ _) (homPres< x y) (homRefl< x y)
  orderedCommRingEquiv .snd .IsOrderedCommRingEquiv.pres≤ x y =
    propBiimpl→Equiv (R.is-prop-valued≤ x y) (R'.is-prop-valued≤ _ _) (homPres≤ x y) (homRefl≤ x y)

  path-orderedCommRing : 𝓡ᵒ ≡ 𝓡'ᵒ
  path-orderedCommRing = uaOrderedCommRing orderedCommRingEquiv

  uaLinearlyOrderedCommRing : 𝓡 ≡ 𝓡'
  uaLinearlyOrderedCommRing i .fst = path-orderedCommRing i
  uaLinearlyOrderedCommRing i .snd =
    isProp→PathP (λ i → isPropLinearOrderStrOnOrderedCommRing (path-orderedCommRing i)) (𝓡 .snd) (𝓡' .snd) i
