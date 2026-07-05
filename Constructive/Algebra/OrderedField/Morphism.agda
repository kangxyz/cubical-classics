{-

Morphisms between constructive ordered fields

These are homomorphisms of the underlying ordered commutative rings.

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.OrderedField.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Int
  using    (ℤ ; pos ; pos·pos)
  renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_)
open import Cubical.Data.Int.Order
  using    (zero-<sucPos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals
  using    (ℚ ; ℕ₊₁→ℤ ; _∼_)
  renaming (_+_ to _+ℚ_ ; _·_ to _·ℚ_ ; -_ to -ℚ_)
open import Cubical.HITs.SetQuotients as SetQuot
open import Cubical.Relation.Nullary
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Int
  using (ℤOrderedCommRing)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Algebra.OrderedCommRing.Properties
open import Constructive.Algebra.OrderedCommRing.Morphism
open import Constructive.Algebra.OrderedField.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (a b c d b⁻¹ d⁻¹ : 𝓡 .fst)
      → (a · d + c · b) · (b⁻¹ · d⁻¹) ≡ (a · b⁻¹) · (d · d⁻¹) + (c · d⁻¹) · (b · b⁻¹)
    helper1 _ _ _ _ _ _ = solve! 𝓡

    helper2 : (a c b⁻¹ d⁻¹ : 𝓡 .fst) → (a · b⁻¹) · 1r + (c · d⁻¹) · 1r ≡ a · b⁻¹ + c · d⁻¹
    helper2 _ _ _ _ = solve! 𝓡

    helper3 : (a c b⁻¹ d⁻¹ : 𝓡 .fst) → (a · c) · (b⁻¹ · d⁻¹) ≡ (a · b⁻¹) · (c · d⁻¹)
    helper3 _ _ _ _ = solve! 𝓡

    helper4 : (a d b⁻¹ d⁻¹ : 𝓡 .fst) → (a · b⁻¹) · (d · d⁻¹) ≡ ((a · d) · b⁻¹) · d⁻¹
    helper4 _ _ _ _ = solve! 𝓡

    helper5 : (c b b⁻¹ d⁻¹ : 𝓡 .fst) → ((c · b) · b⁻¹) · d⁻¹ ≡ (c · d⁻¹) · (b · b⁻¹)
    helper5 _ _ _ _ = solve! 𝓡


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


{-

  The canonical map from ℚ

-}

module InclusionFromℚ (𝒦 : OrderedField ℓ ℓ') where

  open OrderedFieldStr 𝒦
  open InclusionFromℤ (OrderedField→OrderedCommRing 𝒦)
  open OrderedCommRingTheory ℤOrderedCommRing using ()
    renaming (_>_ to _>ℤ_)

  private
    K = 𝒦 .fst .fst
    isSetK = is-set

  open Helpers (OrderedField→CommRing 𝒦)

  ℕ₊₁→ℤ>0 : (n : ℕ₊₁) → ℕ₊₁→ℤ n >ℤ pos 0
  ℕ₊₁→ℤ>0 (1+ n) = zero-<sucPos

  ℕ₊₁→R : ℕ₊₁ → K
  ℕ₊₁→R n = ℤ→R (ℕ₊₁→ℤ n)

  ℕ₊₁→R>0 : (n : ℕ₊₁) → ℕ₊₁→R n > 0r
  ℕ₊₁→R>0 n = ℤ→R-Pres>0 (ℕ₊₁→ℤ n) (ℕ₊₁→ℤ>0 n)

  ℕ₊₁→R≢0 : (n : ℕ₊₁) → ¬ ℕ₊₁→R n ≡ 0r
  ℕ₊₁→R≢0 n = >-arefl (ℕ₊₁→R>0 n)

  ℕ₊₁→ℤ-·₊₁-comm : (m n : ℕ₊₁) → ℕ₊₁→ℤ (m ·₊₁ n) ≡ (ℕ₊₁→ℤ m) ·ℤ (ℕ₊₁→ℤ n)
  ℕ₊₁→ℤ-·₊₁-comm (1+ m) (1+ n) = pos·pos (suc m) (suc n)


  private

    module _ ((a , b) : ℤ × ℕ₊₁) where

      map-helper : K
      map-helper = ℤ→R a · inv (ℕ₊₁→R≢0 b)


    module _ ((a , b)(c , d) : ℤ × ℕ₊₁) where

      b≢0 = ℕ₊₁→R≢0 b
      d≢0 = ℕ₊₁→R≢0 d
      bd≢0 = ℕ₊₁→R≢0 (b ·₊₁ d)
      b⁻¹ = inv b≢0
      d⁻¹ = inv d≢0

      eq-helper : (r : (a , b) ∼ (c , d)) → map-helper (a , b) ≡ map-helper (c , d)
      eq-helper r = sym (·IdR _)
        ∙ (λ i → (ℤ→R a · b⁻¹) · ·-rInv d≢0 (~ i))
        ∙ helper4 _ _ _ _
        ∙ (λ i → (ℤ→R-Pres-· a (ℕ₊₁→ℤ d) (~ i) · b⁻¹) · d⁻¹)
        ∙ (λ i → (ℤ→R (r i) · b⁻¹) · d⁻¹)
        ∙ (λ i → (ℤ→R-Pres-· c (ℕ₊₁→ℤ b) i · b⁻¹) · d⁻¹)
        ∙ helper5 _ _ _ _
        ∙ (λ i → (ℤ→R c · d⁻¹) · ·-rInv b≢0 i)
        ∙ ·IdR _

      inv-path : inv (ℕ₊₁→R≢0 (b ·₊₁ d)) ≡ inv (·-≢0 b≢0 d≢0)
      inv-path i = invUniq {x≢0 = ℕ₊₁→R≢0 (b ·₊₁ d)} {y≢0 = ·-≢0 b≢0 d≢0}
        (cong ℤ→R (ℕ₊₁→ℤ-·₊₁-comm b d)
        ∙ ℤ→R-Pres-· (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) i

      hom-helper : (a b c d : ℤ) → ℤ→R (a ·ℤ d +ℤ c ·ℤ b) ≡ ℤ→R a · ℤ→R d + ℤ→R c · ℤ→R b
      hom-helper a b c d =
        ℤ→R-Pres-+ (a ·ℤ d) (c ·ℤ b)
        ∙ (λ i → ℤ→R-Pres-· a d i + ℤ→R-Pres-· c b i)

      +-helper : map-helper (a ·ℤ ℕ₊₁→ℤ d +ℤ c ·ℤ ℕ₊₁→ℤ b , b ·₊₁ d) ≡ map-helper (a , b) + map-helper (c , d)
      +-helper = (λ i → hom-helper a (ℕ₊₁→ℤ b) c (ℕ₊₁→ℤ d) i · inv bd≢0)
        ∙ (λ i → (ℤ→R a · ℕ₊₁→R d + ℤ→R c · ℕ₊₁→R b) · inv-path i)
        ∙ (λ i → (ℤ→R a · ℕ₊₁→R d + ℤ→R c · ℕ₊₁→R b) · ·-Inv b≢0 d≢0 (~ i))
        ∙ helper1 _ _ _ _ _ _
        ∙ (λ i → (ℤ→R a · b⁻¹) · ·-rInv d≢0 i + (ℤ→R c · d⁻¹) · ·-rInv b≢0 i)
        ∙ helper2 _ _ _ _

      ·-helper : map-helper (a ·ℤ c , b ·₊₁ d) ≡ map-helper (a , b) · map-helper (c , d)
      ·-helper = (λ i → ℤ→R-Pres-· a c i · inv bd≢0)
        ∙ (λ i → (ℤ→R a · ℤ→R c) · inv-path i)
        ∙ (λ i → (ℤ→R a · ℤ→R c) · ·-Inv b≢0 d≢0 (~ i))
        ∙ helper3 _ _ _ _


  ℚ→K : ℚ → K
  ℚ→K = SetQuot.elim (λ _ → isSetK) map-helper eq-helper

  ℚ→K-Pres-1 : ℚ→K 1 ≡ 1r
  ℚ→K-Pres-1 = ·-rInv _

  ℚ→K-Pres-+ : (p q : ℚ) → ℚ→K (p +ℚ q) ≡ ℚ→K p + ℚ→K q
  ℚ→K-Pres-+ = elimProp2 (λ _ _ → isSetK _ _) +-helper

  ℚ→K-Pres-· : (p q : ℚ) → ℚ→K (p ·ℚ q) ≡ ℚ→K p · ℚ→K q
  ℚ→K-Pres-· = elimProp2 (λ _ _ → isSetK _ _) ·-helper

  isRingHomℚ→K : IsRingHom (CommRing→Ring ℚCommRing .snd) ℚ→K (CommRing→Ring (OrderedField→CommRing 𝒦) .snd)
  isRingHomℚ→K =
    makeIsRingHom ℚ→K-Pres-1 ℚ→K-Pres-+ ℚ→K-Pres-·

  ℚ→KCommRingHom : CommRingHom ℚCommRing (OrderedField→CommRing 𝒦)
  ℚ→KCommRingHom =
    _ , IsRingHom→IsCommRingHom ℚCommRing (OrderedField→CommRing 𝒦) ℚ→K isRingHomℚ→K

  module ℚ→KHom = IsCommRingHom (ℚ→KCommRingHom .snd)

  ℚ→K-Pres-- : (p q : ℚ) → ℚ→K (q +ℚ (-ℚ p)) ≡ ℚ→K q - ℚ→K p
  ℚ→K-Pres-- p q =
    ℚ→KHom.pres+ q (-ℚ p)
    ∙ (λ i → ℚ→K q + ℚ→KHom.pres- p i)
