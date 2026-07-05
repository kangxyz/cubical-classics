{-

Constructive ordered fields

An ordered field is an ordered commutative ring whose underlying ring is a
field.

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.OrderedField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Relation.Nullary
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Field as CubicalField
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Algebra.OrderedCommRing.Properties

private
  variable
    ℓ ℓ' : Level


module Apartness (𝓡 : OrderedCommRing ℓ ℓ') where
  open OrderedCommRingStr (𝓡 .snd)

  _#_ : 𝓡 .fst → 𝓡 .fst → Type ℓ'
  x # y = (x < y) ⊎ (y < x)

  infix 4 _#_


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (x y z w : 𝓡 .fst) → (x · y) · (z · w) ≡ (x · z) · (y · w)
    helper1 _ _ _ _ = solve! 𝓡


IsFieldOnOrderedCommRing : OrderedCommRing ℓ ℓ' → Type ℓ
IsFieldOnOrderedCommRing 𝓡 = CubicalField.IsField 0r 1r _+_ _·_ (-_)
  where
  open CommRingStr ((OrderedCommRing→CommRing 𝓡) .snd)


OrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedField ℓ ℓ' =
  Σ[ 𝓡 ∈ OrderedCommRing ℓ ℓ' ] IsFieldOnOrderedCommRing 𝓡


OrderedField→OrderedCommRing : OrderedField ℓ ℓ' → OrderedCommRing ℓ ℓ'
OrderedField→OrderedCommRing = fst


OrderedField→CommRing : OrderedField ℓ ℓ' → CommRing ℓ
OrderedField→CommRing 𝒦 = OrderedCommRing→CommRing (OrderedField→OrderedCommRing 𝒦)


OrderedField→Field : OrderedField ℓ ℓ' → CubicalField.Field ℓ
OrderedField→Field 𝒦 .fst = 𝒦 .fst .fst
OrderedField→Field 𝒦 .snd = CubicalField.fieldstr _ _ _ _ _ (𝒦 .snd)


isPropIsFieldOnOrderedCommRing :
  (𝓡 : OrderedCommRing ℓ ℓ') → isProp (IsFieldOnOrderedCommRing 𝓡)
isPropIsFieldOnOrderedCommRing 𝓡 =
  CubicalField.isPropIsField 0r 1r _+_ _·_ (-_)
  where
  open CommRingStr ((OrderedCommRing→CommRing 𝓡) .snd)


liftPathIsFieldOnOrderedCommRing :
  {𝓡 𝓡' : OrderedCommRing ℓ ℓ'}(p : 𝓡 ≡ 𝓡')
  (h : IsFieldOnOrderedCommRing 𝓡)(h' : IsFieldOnOrderedCommRing 𝓡')
  → PathP (λ i → IsFieldOnOrderedCommRing (p i)) h h'
liftPathIsFieldOnOrderedCommRing p =
  isProp→PathP (λ i → isPropIsFieldOnOrderedCommRing (p i))


module OrderedFieldStr (𝒦 : OrderedField ℓ ℓ') where
  private
    𝒦ᶠ = OrderedField→Field 𝒦
    K = 𝒦 .fst .fst

    variable
      p q x y z : K

  open CubicalField.FieldStr (𝒦ᶠ .snd) public
  open RingTheory (CommRing→Ring (CubicalField.Field→CommRing 𝒦ᶠ)) public
  open Units (CubicalField.Field→CommRing 𝒦ᶠ) public
  open OrderedCommRingTheory (𝒦 .fst) public
  open Apartness (𝒦 .fst) public
  open Helpers (OrderedField→CommRing 𝒦)

  inv : ¬ x ≡ 0r → K
  inv {x = x} x≢0 = x [ x≢0 ]⁻¹

  ·-rInv : (x≢0 : ¬ x ≡ 0r) → x · inv x≢0 ≡ 1r
  ·-rInv {x = x} x≢0 = ·⁻¹≡1 x x≢0

  ·-lInv : (x≢0 : ¬ x ≡ 0r) → inv x≢0 · x ≡ 1r
  ·-lInv x≢0 = ·Comm _ _ ∙ ·-rInv x≢0

  inv-≢0 : (x≢0 : ¬ x ≡ 0r) → ¬ inv x≢0 ≡ 0r
  inv-≢0 {x = x} x≢0 x⁻¹≡0 = x≢0 (sym (·IdR _) ∙ (λ i → x · 1≡0 i) ∙ 0RightAnnihilates _)
    where
    1≡0 : 1r ≡ 0r
    1≡0 = sym (·-rInv _) ∙ (λ i → x · x⁻¹≡0 i) ∙ 0RightAnnihilates _

  invIdem : (x≢0 : ¬ x ≡ 0r) → inv (inv-≢0 x≢0) ≡ x
  invIdem {x = x} x≢0 = sym (·IdL _)
    ∙ (λ i → ·-rInv x≢0 (~ i) · inv (inv-≢0 x≢0))
    ∙ sym (·Assoc _ _ _) ∙ (λ i →  x · ·-rInv (inv-≢0 x≢0) i) ∙ ·IdR _

  invUniq : {x≢0 : ¬ x ≡ 0r}{y≢0 : ¬ y ≡ 0r} → x ≡ y → inv x≢0 ≡ inv y≢0
  invUniq {x≢0 = x≢0} {y≢0 = y≢0} x≡y i = inv (x≢0≡y≢0 i)
    where
    x≢0≡y≢0 : PathP (λ i → ¬ (x≡y i) ≡ 0r) x≢0 y≢0
    x≢0≡y≢0 = isProp→PathP (λ i → isProp¬ ((x≡y i) ≡ 0r)) x≢0 y≢0

  ·-≢0 : (x≢0 : ¬ x ≡ 0r)(y≢0 : ¬ y ≡ 0r) → ¬ x · y ≡ 0r
  ·-≢0 {y = y} x≢0 y≢0 xy≡0 = y≢0 y≡0
    where
    y≡0 : y ≡ 0r
    y≡0 = sym (·IdL _)
      ∙ (λ i → ·-lInv x≢0 (~ i) · y)
      ∙ sym (·Assoc _ _ _)
      ∙ (λ i → inv x≢0 · xy≡0 i)
      ∙ 0RightAnnihilates _

  ·-Inv : (x≢0 : ¬ x ≡ 0r)(y≢0 : ¬ y ≡ 0r) → inv x≢0 · inv y≢0 ≡ inv (·-≢0 x≢0 y≢0)
  ·-Inv {x = x} {y = y} x≢0 y≢0 = sym (·IdR _)
    ∙ (λ i → (inv x≢0 · inv y≢0) · ·-rInv (·-≢0 x≢0 y≢0) (~ i))
    ∙ ·Assoc _ _ _ ∙ (λ i → x⁻¹y⁻¹xy≡1 i · inv (·-≢0 x≢0 y≢0)) ∙ ·IdL _
    where
    x⁻¹y⁻¹xy≡1 : (inv x≢0 · inv y≢0) · (x · y) ≡ 1r
    x⁻¹y⁻¹xy≡1 = helper1 (inv x≢0) (inv y≢0) x y
      ∙ (λ i → ·-lInv x≢0 i · ·-lInv y≢0 i) ∙ ·IdL _

  1/_ : ℕ₊₁ → K
  1/ (1+ n) = inv {x = ℕ→R-Pos (suc n)} (>-arefl (ℕ→R-PosSuc>0 n))

  1/n·n≡1 : (n : ℕ₊₁) →  1/ n · ℕ→R-Pos (ℕ₊₁→ℕ n) ≡ 1r
  1/n·n≡1 (1+ n) = ·-lInv (>-arefl (ℕ→R-PosSuc>0 n))

  _/_ : K → ℕ₊₁ → K
  q / n = q · 1/ n

  ·-/-rInv : (q : K)(n : ℕ₊₁) → (q / n) · (ℕ→R-Pos (ℕ₊₁→ℕ n)) ≡ q
  ·-/-rInv q n = sym (·Assoc q _ _) ∙ (λ i → q · 1/n·n≡1 n i) ∙ ·IdR q

  ·-/-lInv : (q : K)(n : ℕ₊₁) → (ℕ→R-Pos (ℕ₊₁→ℕ n)) · (q / n) ≡ q
  ·-/-lInv q n = ·Comm _ (q / n) ∙ ·-/-rInv q n

  inv₊ : x > 0r → K
  inv₊ x>0 = inv (>-arefl x>0)

  ·-rInv₊ : (x>0 : x > 0r) → x · inv₊ x>0 ≡ 1r
  ·-rInv₊ x>0 = ·-rInv (>-arefl x>0)

  ·-lInv₊ : (x>0 : x > 0r) → inv₊ x>0 · x ≡ 1r
  ·-lInv₊ x>0 = ·Comm _ _ ∙ ·-rInv₊ x>0

  #→≢0 : (x : K) → x # 0r → ¬ x ≡ 0r
  #→≢0 x (inl x<0) x≡0 = <-arefl x<0 x≡0
  #→≢0 x (inr 0<x) x≡0 = >-arefl 0<x x≡0

  inv# :
    (x : K) →
    x # 0r →
    Σ[ y ∈ K ] x · y ≡ 1r
  inv# x x#0 =
    inv (#→≢0 x x#0) , ·-rInv (#→≢0 x x#0)

  ·-lInv# :
    (x : K) →
    x # 0r →
    Σ[ y ∈ K ] y · x ≡ 1r
  ·-lInv# x x#0 =
    inv (#→≢0 x x#0) , ·-lInv (#→≢0 x x#0)

  0#1 : 0r # 1r
  0#1 = inl 1>0
