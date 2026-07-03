{-

SIP for Ordered Ring

TODO: Using DUARel to automate this part.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.Algebra.OrderedRing.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty as Empty
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Univalence

open import Classical.Algebra.OrderedRing
open import Classical.Algebra.OrderedRing.Morphism

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    𝓡  : OrderedRing ℓ   ℓ'
    𝓡' : OrderedRing ℓ'' ℓ'''


{-

  Equivalence of Ordered Ring

-}

open OrderedRingHom
open IsRingHom

isOrderedRingEquiv : OrderedRingHom 𝓡 𝓡' → Type _
isOrderedRingEquiv f = isEquiv (f .ring-hom .fst)


{-

  The Structure Identity Principle

-}


open CommRingStr
open OrderedRingStr
open OrderStrOnCommRing

module _ {𝓡 𝓡' : OrderedRing ℓ ℓ'}
  (path-ring : 𝓡 .fst ≡ 𝓡' .fst)
  (path->0 : PathP (λ i → path-ring i .fst → Type _) (𝓡 .snd ._>0) (𝓡' .snd ._>0)) where

  path-isProp>0 : PathP (λ i → (x : path-ring i .fst) → isProp (path->0 i x)) (𝓡 .snd .isProp>0) (𝓡' .snd .isProp>0)
  path-isProp>0 = isProp→PathP (λ i → isPropΠ (λ _ → isPropIsProp)) (𝓡 .snd .isProp>0) (𝓡' .snd .isProp>0)

  path->0-1r : PathP (λ i → path->0 i (path-ring i .snd .1r)) (𝓡 .snd .>0-1r) (𝓡' .snd .>0-1r)
  path->0-1r = isProp→PathP (λ i → path-isProp>0 i (path-ring i .snd .1r)) (𝓡 .snd .>0-1r) (𝓡' .snd .>0-1r)

  path->0-asym : PathP (λ i → (x : path-ring i .fst) → path->0 i x → path->0 i (path-ring i .snd .-_ x) → ⊥)
    (𝓡 .snd .>0-asym) (𝓡' .snd .>0-asym)
  path->0-asym = isProp→PathP (λ i → isPropΠ3 (λ _ _ _ → isProp⊥)) (𝓡 .snd .>0-asym) (𝓡' .snd .>0-asym)

  path->0-+ : PathP (λ i → (x y : path-ring i .fst) → path->0 i x → path->0 i y → path->0 i (path-ring i .snd ._+_ x y))
    (𝓡 .snd .>0-+) (𝓡' .snd .>0-+)
  path->0-+ = isProp→PathP (λ i → isPropΠ4 (λ _ _ _ _ → path-isProp>0 i _)) (𝓡 .snd .>0-+) (𝓡' .snd .>0-+)

  path->0-· : PathP (λ i → (x y : path-ring i .fst) → path->0 i x → path->0 i y → path->0 i (path-ring i .snd ._·_ x y))
    (𝓡 .snd .>0-·) (𝓡' .snd .>0-·)
  path->0-· = isProp→PathP (λ i → isPropΠ4 (λ _ _ _ _ → path-isProp>0 i _)) (𝓡 .snd .>0-·) (𝓡' .snd .>0-·)

  private
    path-trichotomy>0-prop : (i : I) → isProp ((x : path-ring i .fst) → Trichotomy>0 (path-ring i) (path->0 i) x)
    path-trichotomy>0-prop i = isProp→PathP (λ i → isPropIsProp {A = (x : path-ring i .fst) → Trichotomy>0 (path-ring i) (path->0 i) x})
      (isPropΠ (λ x → isPropTrichotomy>0 (𝓡  .fst) (𝓡  .snd ._>0) (𝓡  .snd .isProp>0) (𝓡  .snd .>0-asym) x))
      (isPropΠ (λ x → isPropTrichotomy>0 (𝓡' .fst) (𝓡' .snd ._>0) (𝓡' .snd .isProp>0) (𝓡' .snd .>0-asym) x)) i

  path-trichotomy>0 : PathP (λ i → (x : path-ring i .fst) → Trichotomy>0 (path-ring i) (path->0 i) x)
    (𝓡 .snd .trichotomy>0) (𝓡' .snd .trichotomy>0)
  path-trichotomy>0 = isProp→PathP (λ i → path-trichotomy>0-prop i) (𝓡 .snd .trichotomy>0) (𝓡' .snd .trichotomy>0)


  liftPathOrderedRing : 𝓡 ≡ 𝓡'
  liftPathOrderedRing i .fst = path-ring i
  liftPathOrderedRing i .snd ._>0 = path->0 i
  liftPathOrderedRing i .snd .isProp>0 = path-isProp>0 i
  liftPathOrderedRing i .snd .>0-asym = path->0-asym i
  liftPathOrderedRing i .snd .>0-1r = path->0-1r i
  liftPathOrderedRing i .snd .>0-+ = path->0-+ i
  liftPathOrderedRing i .snd .>0-· = path->0-· i
  liftPathOrderedRing i .snd .trichotomy>0 = path-trichotomy>0 i


module _ {𝓡 𝓡' : OrderedRing ℓ ℓ'}
  {f : OrderedRingHom 𝓡 𝓡'}(isEquiv-f : isOrderedRingEquiv f) where

  open OrderedRingHom f
  open OrderedRingHomStr f

  path-ring : 𝓡 .fst ≡ 𝓡' .fst
  path-ring i = uaCommRing {A = 𝓡 .fst} {B = 𝓡' .fst} ((_ , isEquiv-f) , f .ring-hom .snd) i

  private

    path->0' : (x : 𝓡 .fst .fst) → 𝓡 .snd ._>0 x ≡ 𝓡' .snd ._>0 (f .ring-hom .fst x)
    path->0' x = hPropExt (𝓡 .snd .isProp>0 x) (𝓡' .snd .isProp>0 _) (f .pres->0 x) (homRefl>0' x)

    transport-helper :
      transport (λ i → path-ring (~ i) .fst → Type _) (𝓡' .snd ._>0)
        ≡ 𝓡 .snd ._>0
    transport-helper i x =
      (transportRefl _ ∙ (λ i → 𝓡' .snd ._>0 (transportRefl (f .ring-hom .fst x) i)) ∙ sym (path->0' x)) i

  path->0 : PathP (λ i → path-ring i .fst → Type _) (𝓡 .snd ._>0) (𝓡' .snd ._>0)
  path->0 i =
    hcomp (λ j → λ
      { (i = i0) → transport-helper j
      ; (i = i1) → 𝓡' .snd ._>0 })
    (transport-filler (λ i → path-ring (~ i) .fst → Type _) (𝓡' .snd ._>0) (~ i))


  uaOrderedRing : 𝓡 ≡ 𝓡'
  uaOrderedRing = liftPathOrderedRing path-ring path->0
