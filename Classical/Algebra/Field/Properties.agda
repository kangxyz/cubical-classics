{-# OPTIONS --safe #-}
module Classical.Algebra.Field.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Relation.Nullary

open import Classical.Algebra.Field.Base

private
  variable
    ℓ : Level

private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (x y z w : 𝓡 .fst) → (x · y) · (z · w) ≡ (x · z) · (y · w)
    helper1 _ _ _ _ = solve! 𝓡


module FieldStr (𝒦 : Field ℓ) where

  private
    K = 𝒦 .fst .fst
    isFieldK = 𝒦 .snd

  private
    variable
      x y : K

  open RingTheory  (CommRing→Ring (𝒦 .fst)) public
  open CommRingStr (𝒦 .fst .snd) public
  open Units       (𝒦 .fst)      public

  open Helpers     (𝒦 .fst)


  inv : ¬ x ≡ 0r → K
  inv x≢0 = isFieldK _ x≢0 .fst

  ·-rInv : (x≢0 : ¬ x ≡ 0r) → x · inv x≢0 ≡ 1r
  ·-rInv x≢0 = isFieldK _ x≢0 .snd

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
    x≢0≡y≢0 = isProp→PathP (λ i → isPropΠ (λ _ → isProp⊥)) x≢0 y≢0


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
