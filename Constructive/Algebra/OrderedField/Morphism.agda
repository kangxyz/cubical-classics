{-

Morphisms between constructive ordered fields

These are homomorphisms of the underlying ordered commutative rings.

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.OrderedField.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing

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


module OrderedFieldHomStr
  {𝒦  : OrderedField ℓ ℓ'}
  {𝒦' : OrderedField ℓ'' ℓ'''}
  (f : OrderedFieldHom 𝒦' 𝒦) where

  open OrderedFieldStr 𝒦
  open OrderedFieldStr 𝒦' using ()
    renaming ( 0r to 0r' ; 1r to 1r'
             ; inv to inv' ; ·-rInv to ·'-rInv)
  open OrderedCommRingHom f
  open IsCommRingHom (ring-hom .snd)

  private
    K' = 𝒦' .fst .fst
    f-map = ring-hom .fst

  0r≢1r : ¬ 0r ≡ 1r
  0r≢1r 0≡1 = >-arefl 1>0 (sym 0≡1)

  homPres≢0 : {x : K'} → ¬ x ≡ 0r' → ¬ f-map x ≡ 0r
  homPres≢0 {x = x} x≢0 fx≡0 =
    0r≢1r 0≡1
    where
    x⁻¹ : K'
    x⁻¹ = inv' x≢0

    0≡1 : 0r ≡ 1r
    0≡1 =
      sym (0LeftAnnihilates (f-map x⁻¹))
      ∙ (λ i → fx≡0 (~ i) · f-map x⁻¹)
      ∙ sym (pres· x x⁻¹)
      ∙ (λ i → f-map (·'-rInv x≢0 i))
      ∙ pres1

  homPresInv :
    {x : K'} →
    (x≢0 : ¬ x ≡ 0r') →
    f-map (inv' x≢0) ≡ inv (homPres≢0 x≢0)
  homPresInv {x = x} x≢0 =
    sym (·IdL _)
    ∙ (λ i → ·-lInv (homPres≢0 x≢0) (~ i) · f-map (inv' x≢0))
    ∙ sym (·Assoc _ _ _)
    ∙ (λ i → inv (homPres≢0 x≢0) · fxfx⁻¹≡1 i)
    ∙ ·IdR _
    where
    fxfx⁻¹≡1 : f-map x · f-map (inv' x≢0) ≡ 1r
    fxfx⁻¹≡1 =
      sym (pres· x (inv' x≢0))
      ∙ (λ i → f-map (·'-rInv x≢0 i))
      ∙ pres1
