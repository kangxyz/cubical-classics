{-

Multiplicative order lemmas for Cubical rationals

-}
{-# OPTIONS --safe #-}
module Constructive.Data.Rationals.Multiplication where

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

mul-positive :
  {a b : ℚ} →
  0ℚ ℚOrder.< a →
  0ℚ ℚOrder.< b →
  0ℚ ℚOrder.< a ℚ.· b
mul-positive {a = a} {b = b} 0<a 0<b =
  subst (λ v → v ℚOrder.< a ℚ.· b)
    (ℚ.·AnnihilL b)
    (ℚOrder.<-·o 0ℚ a b 0<b 0<a)

mul-nonnegative :
  {a b : ℚ} →
  0ℚ ℚOrder.≤ a →
  0ℚ ℚOrder.≤ b →
  0ℚ ℚOrder.≤ a ℚ.· b
mul-nonnegative {a = a} {b = b} 0≤a 0≤b =
  subst (λ v → v ℚOrder.≤ a ℚ.· b)
    (ℚ.·AnnihilL b)
    (ℚOrder.≤-·o 0ℚ a b 0≤b 0≤a)


mul-nonpositive-right :
  {a b : ℚ} →
  0ℚ ℚOrder.< a →
  b ℚOrder.≤ 0ℚ →
  a ℚ.· b ℚOrder.≤ 0ℚ
mul-nonpositive-right {a = a} {b = b} 0<a b≤0 =
  subst2 ℚOrder._≤_
    (ℚ.·Comm b a)
    (ℚ.·AnnihilL a)
    (ℚOrder.≤-·o b 0ℚ a (<→≤ {p = 0ℚ} {q = a} 0<a) b≤0)


mul-nonpositive-left :
  {a b : ℚ} →
  a ℚOrder.≤ 0ℚ →
  0ℚ ℚOrder.< b →
  a ℚ.· b ℚOrder.≤ 0ℚ
mul-nonpositive-left {a = a} {b = b} a≤0 0<b =
  subst (λ v → v ℚOrder.≤ 0ℚ)
    (ℚ.·Comm b a)
    (mul-nonpositive-right {a = b} {b = a} 0<b a≤0)


mul-distrib-left :
  (a b c : ℚ) →
  a ℚ.· (b ℚ.+ c) ≡ (a ℚ.· b) ℚ.+ (a ℚ.· c)
mul-distrib-left = ℚ.·DistL+


mul-mono-positive-< :
  {a b c d : ℚ} →
  a ℚOrder.< c →
  b ℚOrder.< d →
  0ℚ ℚOrder.< b →
  0ℚ ℚOrder.< c →
  a ℚ.· b ℚOrder.< c ℚ.· d
mul-mono-positive-< {a = a} {b = b} {c = c} {d = d}
  a<c b<d 0<b 0<c =
  ℚOrder.isTrans< (a ℚ.· b) (c ℚ.· b) (c ℚ.· d)
    a*b<c*b
    c*b<c*d
  where
  a*b<c*b : a ℚ.· b ℚOrder.< c ℚ.· b
  a*b<c*b = ℚOrder.<-·o a c b 0<b a<c

  c*b<c*d : c ℚ.· b ℚOrder.< c ℚ.· d
  c*b<c*d =
    subst2 ℚOrder._<_
      (ℚ.·Comm b c)
      (ℚ.·Comm d c)
      (ℚOrder.<-·o b d c 0<c b<d)


mul-mono-positive-<≤ :
  {a b c d : ℚ} →
  0ℚ ℚOrder.< a →
  0ℚ ℚOrder.< c →
  a ℚOrder.< b →
  c ℚOrder.≤ d →
  a ℚ.· c ℚOrder.< b ℚ.· d
mul-mono-positive-<≤ {a = a} {b = b} {c = c} {d = d} 0<a 0<c a<b c≤d =
  ℚOrder.isTrans<≤ (a ℚ.· c) (b ℚ.· c) (b ℚ.· d)
    a*c<b*c
    b*c≤b*d
  where
  0<b : 0ℚ ℚOrder.< b
  0<b = ℚOrder.isTrans< 0ℚ a b 0<a a<b

  0≤b : 0ℚ ℚOrder.≤ b
  0≤b = <→≤ {p = 0ℚ} {q = b} 0<b

  a*c<b*c : a ℚ.· c ℚOrder.< b ℚ.· c
  a*c<b*c = ℚOrder.<-·o a b c 0<c a<b

  b*c≤b*d : b ℚ.· c ℚOrder.≤ b ℚ.· d
  b*c≤b*d =
    subst2 ℚOrder._≤_
      (ℚ.·Comm c b)
      (ℚ.·Comm d b)
      (ℚOrder.≤-·o c d b 0≤b c≤d)


mul-close-left-nonpositive-upper< :
  {q gap δ V lx ux uy : ℚ} →
  lx ℚOrder.≤ 0ℚ →
  ux ℚOrder.< lx ℚ.+ δ →
  0ℚ ℚOrder.< ux →
  0ℚ ℚOrder.< uy →
  uy ℚOrder.≤ V →
  δ ℚ.· V ℚOrder.< gap →
  gap ℚOrder.≤ q →
  ux ℚ.· uy ℚOrder.< q
mul-close-left-nonpositive-upper<
  {q = q} {gap = gap} {δ = δ} {V = V} {lx = lx} {ux = ux} {uy = uy}
  lx≤0 ux<lx+δ 0<ux 0<uy uy≤V δV<gap gap≤q =
  <≤-trans {p = ux ℚ.· uy} {q = gap} {r = q}
    (ℚOrder.isTrans< (ux ℚ.· uy) (δ ℚ.· V) gap uxuy<δV δV<gap)
    gap≤q
  where
  lx+δ≤δ : lx ℚ.+ δ ℚOrder.≤ δ
  lx+δ≤δ =
    add-nonpositive≤right {p = lx} {r = δ} lx≤0

  ux<δ : ux ℚOrder.< δ
  ux<δ =
    <≤-trans {p = ux} {q = lx ℚ.+ δ} {r = δ}
      ux<lx+δ
      lx+δ≤δ

  uxuy<δV : ux ℚ.· uy ℚOrder.< δ ℚ.· V
  uxuy<δV =
    mul-mono-positive-<≤
      {a = ux} {b = δ} {c = uy} {d = V}
      0<ux 0<uy ux<δ uy≤V


mul-close-right-nonpositive-upper< :
  {q gap δ U ly ux uy : ℚ} →
  ly ℚOrder.≤ 0ℚ →
  uy ℚOrder.< ly ℚ.+ δ →
  0ℚ ℚOrder.< ux →
  0ℚ ℚOrder.< uy →
  ux ℚOrder.≤ U →
  δ ℚ.· U ℚOrder.< gap →
  gap ℚOrder.≤ q →
  ux ℚ.· uy ℚOrder.< q
mul-close-right-nonpositive-upper<
  {q = q} {gap = gap} {δ = δ} {U = U} {ly = ly} {ux = ux} {uy = uy}
  ly≤0 uy<ly+δ 0<ux 0<uy ux≤U δU<gap gap≤q =
  <≤-trans {p = ux ℚ.· uy} {q = gap} {r = q}
    (ℚOrder.isTrans< (ux ℚ.· uy) (δ ℚ.· U) gap uxuy<δU δU<gap)
    gap≤q
  where
  ly+δ≤δ : ly ℚ.+ δ ℚOrder.≤ δ
  ly+δ≤δ =
    add-nonpositive≤right {p = ly} {r = δ} ly≤0

  uy<δ : uy ℚOrder.< δ
  uy<δ =
    <≤-trans {p = uy} {q = ly ℚ.+ δ} {r = δ}
      uy<ly+δ
      ly+δ≤δ

  uyux<δU : uy ℚ.· ux ℚOrder.< δ ℚ.· U
  uyux<δU =
    mul-mono-positive-<≤
      {a = uy} {b = δ} {c = ux} {d = U}
      0<uy 0<ux uy<δ ux≤U

  uxuy<δU : ux ℚ.· uy ℚOrder.< δ ℚ.· U
  uxuy<δU =
    subst (λ r → r ℚOrder.< δ ℚ.· U)
      (ℚ.·Comm uy ux)
      uyux<δU


mul-close-positive-upper< :
  {p q gap δ U V lx ux ly uy : ℚ} →
  lx ℚOrder.< ux →
  ly ℚOrder.< uy →
  0ℚ ℚOrder.< lx →
  0ℚ ℚOrder.< ly →
  ux ℚOrder.< lx ℚ.+ δ →
  uy ℚOrder.< ly ℚ.+ δ →
  ux ℚOrder.≤ U →
  uy ℚOrder.≤ V →
  lx ℚ.· ly ℚOrder.≤ p →
  δ ℚ.· (U ℚ.+ V) ℚOrder.< gap →
  p ℚ.+ gap ≡ q →
  ux ℚ.· uy ℚOrder.< q
mul-close-positive-upper<
  {p = p} {q = q} {gap = gap} {δ = δ} {U = U} {V = V}
  {lx = lx} {ux = ux} {ly = ly} {uy = uy}
  lx<ux ly<uy 0<lx 0<ly ux<lx+δ uy<ly+δ ux≤U uy≤V lxly≤p δUV<gap p+gap≡q =
  subst (λ r → r ℚOrder.< q)
    (sym (mul-error-split lx ux ly uy))
    rhs<q
  where
  err₁ : ℚ
  err₁ = (ux ℚ.- lx) ℚ.· uy

  err₂ : ℚ
  err₂ = lx ℚ.· (uy ℚ.- ly)

  0<uy : 0ℚ ℚOrder.< uy
  0<uy = ℚOrder.isTrans< 0ℚ ly uy 0<ly ly<uy

  ux<δ+lx : ux ℚOrder.< δ ℚ.+ lx
  ux<δ+lx =
    subst (λ r → ux ℚOrder.< r)
      (ℚ.+Comm lx δ)
      ux<lx+δ

  ux-lx<δ : ux ℚ.- lx ℚOrder.< δ
  ux-lx<δ = <+→diff< ux δ lx ux<δ+lx

  0<ux-lx : 0ℚ ℚOrder.< ux ℚ.- lx
  0<ux-lx = diff-positive {p = lx} {q = ux} lx<ux

  err₁<δV : err₁ ℚOrder.< δ ℚ.· V
  err₁<δV =
    mul-mono-positive-<≤
      {a = ux ℚ.- lx} {b = δ} {c = uy} {d = V}
      0<ux-lx 0<uy ux-lx<δ uy≤V

  uy<δ+ly : uy ℚOrder.< δ ℚ.+ ly
  uy<δ+ly =
    subst (λ r → uy ℚOrder.< r)
      (ℚ.+Comm ly δ)
      uy<ly+δ

  uy-ly<δ : uy ℚ.- ly ℚOrder.< δ
  uy-ly<δ = <+→diff< uy δ ly uy<δ+ly

  0<uy-ly : 0ℚ ℚOrder.< uy ℚ.- ly
  0<uy-ly = diff-positive {p = ly} {q = uy} ly<uy

  lx≤ux : lx ℚOrder.≤ ux
  lx≤ux = <→≤ {p = lx} {q = ux} lx<ux

  lx≤U : lx ℚOrder.≤ U
  lx≤U = ≤-trans {p = lx} {q = ux} {r = U} lx≤ux ux≤U

  uy-ly*lx<δU : (uy ℚ.- ly) ℚ.· lx ℚOrder.< δ ℚ.· U
  uy-ly*lx<δU =
    mul-mono-positive-<≤
      {a = uy ℚ.- ly} {b = δ} {c = lx} {d = U}
      0<uy-ly 0<lx uy-ly<δ lx≤U

  err₂<δU : err₂ ℚOrder.< δ ℚ.· U
  err₂<δU =
    subst (λ r → r ℚOrder.< δ ℚ.· U)
      (ℚ.·Comm (uy ℚ.- ly) lx)
      uy-ly*lx<δU

  err₁+err₂<δV+δU :
    err₁ ℚ.+ err₂ ℚOrder.< (δ ℚ.· V) ℚ.+ (δ ℚ.· U)
  err₁+err₂<δV+δU =
    ℚOrder.<Monotone+
      err₁ (δ ℚ.· V)
      err₂ (δ ℚ.· U)
      err₁<δV
      err₂<δU

  δV+δU≡δUV : (δ ℚ.· V) ℚ.+ (δ ℚ.· U) ≡ δ ℚ.· (U ℚ.+ V)
  δV+δU≡δUV =
    sym (ℚ.·DistL+ δ V U) ∙
    cong (δ ℚ.·_) (ℚ.+Comm V U)

  err₁+err₂<δUV : err₁ ℚ.+ err₂ ℚOrder.< δ ℚ.· (U ℚ.+ V)
  err₁+err₂<δUV =
    subst (λ r → err₁ ℚ.+ err₂ ℚOrder.< r)
      δV+δU≡δUV
      err₁+err₂<δV+δU

  err₁+err₂<gap : err₁ ℚ.+ err₂ ℚOrder.< gap
  err₁+err₂<gap =
    ℚOrder.isTrans< (err₁ ℚ.+ err₂) (δ ℚ.· (U ℚ.+ V)) gap
      err₁+err₂<δUV
      δUV<gap

  base+err≤p+err :
    (lx ℚ.· ly) ℚ.+ (err₁ ℚ.+ err₂)
      ℚOrder.≤
    p ℚ.+ (err₁ ℚ.+ err₂)
  base+err≤p+err =
    +-rPres≤ {p = lx ℚ.· ly} {q = p} {r = err₁ ℚ.+ err₂} lxly≤p

  p+err<p+gap : p ℚ.+ (err₁ ℚ.+ err₂) ℚOrder.< p ℚ.+ gap
  p+err<p+gap =
    ℚOrder.<-o+ (err₁ ℚ.+ err₂) gap p err₁+err₂<gap

  rhs<p+gap :
    (lx ℚ.· ly) ℚ.+ (err₁ ℚ.+ err₂) ℚOrder.< p ℚ.+ gap
  rhs<p+gap =
    ℚOrder.isTrans≤< ((lx ℚ.· ly) ℚ.+ (err₁ ℚ.+ err₂))
      (p ℚ.+ (err₁ ℚ.+ err₂))
      (p ℚ.+ gap)
      base+err≤p+err
      p+err<p+gap

  rhs<q :
    (lx ℚ.· ly) ℚ.+ (err₁ ℚ.+ err₂) ℚOrder.< q
  rhs<q =
    subst (λ r → (lx ℚ.· ly) ℚ.+ (err₁ ℚ.+ err₂) ℚOrder.< r)
      p+gap≡q
      rhs<p+gap


mul-left-positive-< :
  {a b c : ℚ} →
  0ℚ ℚOrder.< a →
  b ℚOrder.< c →
  a ℚ.· b ℚOrder.< a ℚ.· c
mul-left-positive-< {a = a} {b = b} {c = c} 0<a b<c =
  subst2 ℚOrder._<_
    (ℚ.·Comm b a)
    (ℚ.·Comm c a)
    (ℚOrder.<-·o b c a 0<a b<c)


mul-right-positive-< :
  {a b c : ℚ} →
  0ℚ ℚOrder.< a →
  b ℚOrder.< c →
  b ℚ.· a ℚOrder.< c ℚ.· a
mul-right-positive-< {a = a} {b = b} {c = c} 0<a b<c =
  ℚOrder.<-·o b c a 0<a b<c


mul-left-nonnegative-≤ :
  {a b c : ℚ} →
  0ℚ ℚOrder.≤ a →
  b ℚOrder.≤ c →
  a ℚ.· b ℚOrder.≤ a ℚ.· c
mul-left-nonnegative-≤ {a = a} {b = b} {c = c} 0≤a b≤c =
  subst2 ℚOrder._≤_
    (ℚ.·Comm b a)
    (ℚ.·Comm c a)
    (ℚOrder.≤-·o b c a 0≤a b≤c)
