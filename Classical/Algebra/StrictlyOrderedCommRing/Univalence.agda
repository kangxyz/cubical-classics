{-

SIP for strictly ordered commutative rings

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.Algebra.StrictlyOrderedCommRing.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing

open import Classical.Algebra.OrderedCommRing.Morphism
open import Classical.Algebra.OrderedCommRing.Univalence
open import Classical.Algebra.StrictlyOrderedCommRing
import Classical.Algebra.StrictlyOrderedCommRing.Base as StrictBase
open import Classical.Algebra.StrictlyOrderedCommRing.Morphism

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    𝓡  : StrictlyOrderedCommRing ℓ   ℓ'
    𝓡' : StrictlyOrderedCommRing ℓ'' ℓ'''


{-

  Equivalence of strictly ordered commutative rings

-}

open OrderedCommRingHom

isStrictlyOrderedCommRingEquiv : OrderedCommRingHom (𝓡 .fst) (𝓡' .fst) → Type _
isStrictlyOrderedCommRingEquiv f = isEquiv (f .ring-hom .fst)


isPropStrictOrderStrOnOrderedCommRing :
  (𝓡ᶜ : OrderedCommRing ℓ ℓ') → isProp (StrictOrderStrOnOrderedCommRing 𝓡ᶜ)
isPropStrictOrderStrOnOrderedCommRing 𝓡ᶜ s t i .StrictOrderStrOnOrderedCommRing.trichotomy =
  isPropΠ2 (StrictBase.isPropTrichotomy 𝓡ᶜ) (s .StrictOrderStrOnOrderedCommRing.trichotomy) (t .StrictOrderStrOnOrderedCommRing.trichotomy) i


module _ {𝓡 𝓡' : StrictlyOrderedCommRing ℓ ℓ'}
  {f : OrderedCommRingHom (𝓡 .fst) (𝓡' .fst)}
  (isEquiv-f : isStrictlyOrderedCommRingEquiv {𝓡 = 𝓡} {𝓡' = 𝓡'} f) where

  private
    𝓡ᵒ  = 𝓡 .fst
    𝓡'ᵒ = 𝓡' .fst

  module R  = OrderedCommRingStr (𝓡ᵒ .snd)
  module R' = OrderedCommRingStr (𝓡'ᵒ .snd)

  open OrderedCommRingHom f
  open OrderedCommRingHomProperties {𝓡 = 𝓡} {𝓡' = 𝓡'} f
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

  uaStrictlyOrderedCommRing : 𝓡 ≡ 𝓡'
  uaStrictlyOrderedCommRing i .fst = path-orderedCommRing i
  uaStrictlyOrderedCommRing i .snd =
    isProp→PathP (λ i → isPropStrictOrderStrOnOrderedCommRing (path-orderedCommRing i)) (𝓡 .snd) (𝓡' .snd) i
