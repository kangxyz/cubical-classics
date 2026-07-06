{-

Min and max order lemmas for Cubical rationals

-}
{-# OPTIONS --safe #-}
module Constructive.Data.Rationals.Bounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤOrder
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.NatPlusOne using (ℕ₊₁)
open import Cubical.Data.NatPlusOne.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁)
open import Cubical.Relation.Nullary using (Dec)
open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection
open import Constructive.Algebra.LinearlyOrderedCommRing
open import Constructive.Algebra.LinearlyOrderedCommRing.Instances.Rationals
  using (ℚLinearlyOrderedCommRing)
import Constructive.Algebra.LinearlyOrderedCommRing.Instances.Rationals.Archimedean as ℚArch
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Algebra.LinearlyOrderedField.Instances.Rationals
  using (ℚLinearlyOrderedField)


private
  module ℚLOR = LinearlyOrderedCommRingStr ℚLinearlyOrderedCommRing
  module ℚOF = LinearlyOrderedFieldStr ℚLinearlyOrderedField
  ℚCommRing = LinearlyOrderedCommRing→CommRing ℚLinearlyOrderedCommRing

  module RingSolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    mul-error-split :
      (lx ux ly uy : 𝓡 .fst) →
      ux · uy ≡ lx · ly + (((ux - lx) · uy) + (lx · (uy - ly)))
    mul-error-split _ _ _ _ = solve! 𝓡

open import Constructive.Data.Rationals.Base

min≤r : (p q : ℚ) → ℚ.min p q ℚOrder.≤ q
min≤r p q =
  subst (λ r → r ℚOrder.≤ q)
    (ℚ.minComm q p)
    (ℚOrder.min≤ q p)


≤max-r : (p q : ℚ) → q ℚOrder.≤ ℚ.max p q
≤max-r p q =
  subst (λ r → q ℚOrder.≤ r)
    (ℚ.maxComm q p)
    (ℚOrder.≤max q p)


<min :
  {q r s : ℚ} →
  q ℚOrder.< r →
  q ℚOrder.< s →
  q ℚOrder.< ℚ.min r s
<min {q = q} {r = r} {s = s} q<r q<s with r ℚOrder.≟ s
... | ℚOrder.lt r<s =
  subst (λ t → q ℚOrder.< t)
    (sym (ℚOrder.≤→min r s (ℚOrder.<Weaken≤ r s r<s)))
    q<r
... | ℚOrder.eq r≡s =
  subst (λ t → q ℚOrder.< t)
    (sym (ℚOrder.≤→min r s (ℚOrder.≡Weaken≤ r s r≡s)))
    q<r
... | ℚOrder.gt s<r =
  subst (λ t → q ℚOrder.< t)
    (sym
      (ℚ.min r s ≡⟨ ℚ.minComm r s ⟩
       ℚ.min s r ≡⟨ ℚOrder.≤→min s r (ℚOrder.<Weaken≤ s r s<r) ⟩
       s ∎))
    q<s


max< :
  {r s q : ℚ} →
  r ℚOrder.< q →
  s ℚOrder.< q →
  ℚ.max r s ℚOrder.< q
max< {r = r} {s = s} {q = q} r<q s<q with r ℚOrder.≟ s
... | ℚOrder.lt r<s =
  subst (λ t → t ℚOrder.< q)
    (sym (ℚOrder.≤→max r s (ℚOrder.<Weaken≤ r s r<s)))
    s<q
... | ℚOrder.eq r≡s =
  subst (λ t → t ℚOrder.< q)
    (sym (ℚOrder.≤→max r s (ℚOrder.≡Weaken≤ r s r≡s)))
    s<q
... | ℚOrder.gt s<r =
  subst (λ t → t ℚOrder.< q)
    (sym
      (ℚ.max r s ≡⟨ ℚ.maxComm r s ⟩
       ℚ.max s r ≡⟨ ℚOrder.≤→max s r (ℚOrder.<Weaken≤ s r s<r) ⟩
       r ∎))
    r<q
