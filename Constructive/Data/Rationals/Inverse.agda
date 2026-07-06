{-

Positive inverse lemmas for Cubical rationals

-}
{-# OPTIONS --safe #-}
module Constructive.Data.Rationals.Inverse where

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
open import Constructive.Data.Rationals.Multiplication

posInv : (q : ℚ) → 0ℚ ℚOrder.< q → ℚ
posInv q 0<q = ℚOF.inv₊ {q = q} 0<q


posInv-positive :
  {q : ℚ} →
  (0<q : 0ℚ ℚOrder.< q) →
  0ℚ ℚOrder.< posInv q 0<q
posInv-positive {q = q} 0<q =
  ℚOF.p>0→p⁻¹>0 {p = q} 0<q


posInv-right :
  (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  q ℚ.· posInv q 0<q ≡ 1ℚ
posInv-right q 0<q =
  ℚOF.·-rInv₊ {q = q} 0<q


posInv-left :
  (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  posInv q 0<q ℚ.· q ≡ 1ℚ
posInv-left q 0<q =
  ℚOF.·-lInv₊ {q = q} 0<q


mul-right-cancel-positive-≤ :
  {p q c : ℚ} →
  0ℚ ℚOrder.< c →
  p ℚ.· c ℚOrder.≤ q ℚ.· c →
  p ℚOrder.≤ q
mul-right-cancel-positive-≤ {p = p} {q = q} {c = c} 0<c pc≤qc =
  subst2 ℚOrder._≤_
    p-path
    q-path
    scaled≤
  where
  c⁻¹ : ℚ
  c⁻¹ =
    posInv c 0<c

  0≤c⁻¹ : 0ℚ ℚOrder.≤ c⁻¹
  0≤c⁻¹ =
    <→≤
      {p = 0ℚ}
      {q = c⁻¹}
      (posInv-positive {q = c} 0<c)

  scaled≤ : (p ℚ.· c) ℚ.· c⁻¹ ℚOrder.≤ (q ℚ.· c) ℚ.· c⁻¹
  scaled≤ =
    ℚOrder.≤-·o
      (p ℚ.· c)
      (q ℚ.· c)
      c⁻¹
      0≤c⁻¹
      pc≤qc

  p-path : (p ℚ.· c) ℚ.· c⁻¹ ≡ p
  p-path =
    sym (ℚ.·Assoc p c c⁻¹) ∙
    cong (p ℚ.·_) (posInv-right c 0<c) ∙
    ℚ.·IdR p

  q-path : (q ℚ.· c) ℚ.· c⁻¹ ≡ q
  q-path =
    sym (ℚ.·Assoc q c c⁻¹) ∙
    cong (q ℚ.·_) (posInv-right c 0<c) ∙
    ℚ.·IdR q


posInv-reverse< :
  {p q : ℚ} →
  (0<p : 0ℚ ℚOrder.< p) →
  (0<q : 0ℚ ℚOrder.< q) →
  p ℚOrder.< q →
  posInv q 0<q ℚOrder.< posInv p 0<p
posInv-reverse< {p = p} {q = q} 0<p 0<q p<q =
  ℚOF.inv-Reverse< {p = q} {q = p} 0<q 0<p p<q


posInv-involutive :
  (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  posInv (posInv q 0<q) (posInv-positive {q = q} 0<q) ≡ q
posInv-involutive q 0<q =
  ℚOF.inv₊Idem {q = q} 0<q

mul-posInv-cancelL :
  (a q : ℚ) →
  (0<a : 0ℚ ℚOrder.< a) →
  a ℚ.· (q ℚ.· posInv a 0<a) ≡ q
mul-posInv-cancelL a q 0<a =
  ℚ.·Assoc a q (posInv a 0<a) ∙
  cong (λ r → r ℚ.· posInv a 0<a) (ℚ.·Comm a q) ∙
  sym (ℚ.·Assoc q a (posInv a 0<a)) ∙
  cong (q ℚ.·_) (posInv-right a 0<a) ∙
  ℚ.·IdR q

div-positive-denom-<1 :
  {q a : ℚ} →
  q ℚOrder.< a →
  (0<a : 0ℚ ℚOrder.< a) →
  q ℚ.· posInv a 0<a ℚOrder.< 1ℚ
div-positive-denom-<1 {q = q} {a = a} q<a 0<a =
  subst (λ r → q ℚ.· posInv a 0<a ℚOrder.< r)
    (posInv-right a 0<a)
    (ℚOrder.<-·o q a (posInv a 0<a)
      (posInv-positive {q = a} 0<a)
      q<a)

1<div-positive-denom :
  {r q : ℚ} →
  r ℚOrder.< q →
  (0<r : 0ℚ ℚOrder.< r) →
  1ℚ ℚOrder.< q ℚ.· posInv r 0<r
1<div-positive-denom {r = r} {q = q} r<q 0<r =
  subst (λ lhs → lhs ℚOrder.< q ℚ.· posInv r 0<r)
    (posInv-right r 0<r)
    (ℚOrder.<-·o r q (posInv r 0<r)
      (posInv-positive {q = r} 0<r)
      r<q)

abstract
  mul-by-<1 :
    {a b : ℚ} →
    0ℚ ℚOrder.< a →
    b ℚOrder.< 1ℚ →
    a ℚ.· b ℚOrder.< a
  mul-by-<1 {a = a} {b = b} 0<a b<1 =
    subst2 ℚOrder._<_
      (ℚ.·Comm b a)
      (ℚ.·IdL a)
      (ℚOrder.<-·o b 1ℚ a 0<a b<1)

  mul-by->1 :
    {a b : ℚ} →
    0ℚ ℚOrder.< a →
    1ℚ ℚOrder.< b →
    a ℚOrder.< a ℚ.· b
  mul-by->1 {a = a} {b = b} 0<a 1<b =
    subst2 ℚOrder._<_
      (ℚ.·IdL a)
      (ℚ.·Comm b a)
      (ℚOrder.<-·o 1ℚ b a 0<a 1<b)

  unit-lower-factor :
    (q a : ℚ) →
    0ℚ ℚOrder.≤ q →
    q ℚOrder.< a →
    0ℚ ℚOrder.< a →
    Σ[ b ∈ ℚ ]
      (0ℚ ℚOrder.< b) ×
      (b ℚOrder.< 1ℚ) ×
      (q ℚOrder.< a ℚ.· b)
  unit-lower-factor q a 0≤q q<a 0<a =
    b , 0<b , b<1 , q<ab
    where
    qa : ℚ
    qa = q ℚ.· posInv a 0<a

    qa<1 : qa ℚOrder.< 1ℚ
    qa<1 = div-positive-denom-<1 {q = q} {a = a} q<a 0<a

    b : ℚ
    b = middle qa 1ℚ

    qa<b : qa ℚOrder.< b
    qa<b = middle>l {p = qa} {q = 1ℚ} qa<1

    b<1 : b ℚOrder.< 1ℚ
    b<1 = middle<r {p = qa} {q = 1ℚ} qa<1

    0≤qa : 0ℚ ℚOrder.≤ qa
    0≤qa =
      mul-nonnegative
        {a = q}
        {b = posInv a 0<a}
        0≤q
        (<→≤ {p = 0ℚ} {q = posInv a 0<a}
          (posInv-positive {q = a} 0<a))

    0<b : 0ℚ ℚOrder.< b
    0<b =
      ≤<-trans {p = 0ℚ} {q = qa} {r = b} 0≤qa qa<b

    aqa<ab : a ℚ.· qa ℚOrder.< a ℚ.· b
    aqa<ab =
      mul-left-positive-< {a = a} {b = qa} {c = b} 0<a qa<b

    q<ab : q ℚOrder.< a ℚ.· b
    q<ab =
      subst (λ v → v ℚOrder.< a ℚ.· b)
        (mul-posInv-cancelL a q 0<a)
        aqa<ab

  unit-upper-factor :
    (r q : ℚ) →
    0ℚ ℚOrder.< r →
    r ℚOrder.< q →
    Σ[ b ∈ ℚ ]
      (1ℚ ℚOrder.< b) ×
      (0ℚ ℚOrder.< b) ×
      (r ℚ.· b ℚOrder.< q)
  unit-upper-factor r q 0<r r<q =
    b , 1<b , 0<b , rb<q
    where
    t : ℚ
    t = q ℚ.· posInv r 0<r

    1<t : 1ℚ ℚOrder.< t
    1<t = 1<div-positive-denom {r = r} {q = q} r<q 0<r

    b : ℚ
    b = middle 1ℚ t

    1<b : 1ℚ ℚOrder.< b
    1<b = middle>l {p = 1ℚ} {q = t} 1<t

    b<t : b ℚOrder.< t
    b<t = middle<r {p = 1ℚ} {q = t} 1<t

    0<b : 0ℚ ℚOrder.< b
    0<b =
      ℚOrder.isTrans< 0ℚ 1ℚ b 0<1 1<b

    rb<rt : r ℚ.· b ℚOrder.< r ℚ.· t
    rb<rt =
      mul-left-positive-< {a = r} {b = b} {c = t} 0<r b<t

    rb<q : r ℚ.· b ℚOrder.< q
    rb<q =
      subst (λ v → r ℚ.· b ℚOrder.< v)
        (mul-posInv-cancelL r q 0<r)
        rb<rt
