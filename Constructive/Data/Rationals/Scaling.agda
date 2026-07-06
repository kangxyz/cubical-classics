{-

Scaled multiplication error bounds for Cubical rationals

-}
{-# OPTIONS --safe #-}
module Constructive.Data.Rationals.Scaling where

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
open import Constructive.Data.Rationals.Inverse

scaleByPositive : (ε M : ℚ) → 0ℚ ℚOrder.< M → ℚ
scaleByPositive ε M 0<M = ε ℚ.· posInv M 0<M


scaleByPositive-positive :
  {ε M : ℚ} →
  0ℚ ℚOrder.< ε →
  (0<M : 0ℚ ℚOrder.< M) →
  0ℚ ℚOrder.< scaleByPositive ε M 0<M
scaleByPositive-positive {ε = ε} {M = M} 0<ε 0<M =
  mul-positive {a = ε} {b = posInv M 0<M}
    0<ε
    (posInv-positive {q = M} 0<M)


scaleByPositive-cancelR :
  (ε M : ℚ) →
  (0<M : 0ℚ ℚOrder.< M) →
  scaleByPositive ε M 0<M ℚ.· M ≡ ε
scaleByPositive-cancelR ε M 0<M =
  sym (ℚ.·Assoc ε (posInv M 0<M) M) ∙
  cong (ε ℚ.·_) (posInv-left M 0<M) ∙
  ℚ.·IdR ε


scaleByPositive-cancelL :
  (ε M : ℚ) →
  (0<M : 0ℚ ℚOrder.< M) →
  M ℚ.· scaleByPositive ε M 0<M ≡ ε
scaleByPositive-cancelL ε M 0<M =
  ℚ.·Comm M (scaleByPositive ε M 0<M) ∙
  scaleByPositive-cancelR ε M 0<M


mulErrorDenom : ℚ → ℚ → ℚ → ℚ
mulErrorDenom U V gap = ((U ℚ.+ V) ℚ.+ gap) ℚ.+ 1ℚ


mulErrorDenom-positive :
  {U V gap : ℚ} →
  0ℚ ℚOrder.< U →
  0ℚ ℚOrder.< V →
  0ℚ ℚOrder.< gap →
  0ℚ ℚOrder.< mulErrorDenom U V gap
mulErrorDenom-positive {U = U} {V = V} {gap = gap} 0<U 0<V 0<gap =
  positive-sum
    {p = (U ℚ.+ V) ℚ.+ gap}
    {q = 1ℚ}
    (positive-sum
      {p = U ℚ.+ V}
      {q = gap}
      (positive-sum {p = U} {q = V} 0<U 0<V)
      0<gap)
    0<1


mulErrorScale :
  (gap U V : ℚ) →
  0ℚ ℚOrder.< U →
  0ℚ ℚOrder.< V →
  0ℚ ℚOrder.< gap →
  ℚ
mulErrorScale gap U V 0<U 0<V 0<gap =
  scaleByPositive gap
    (mulErrorDenom U V gap)
    (mulErrorDenom-positive {U = U} {V = V} {gap = gap} 0<U 0<V 0<gap)


mulErrorScale-positive :
  {gap U V : ℚ}
  (0<U : 0ℚ ℚOrder.< U)
  (0<V : 0ℚ ℚOrder.< V)
  (0<gap : 0ℚ ℚOrder.< gap) →
  0ℚ ℚOrder.< mulErrorScale gap U V 0<U 0<V 0<gap
mulErrorScale-positive {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap =
  scaleByPositive-positive
    {ε = gap}
    {M = mulErrorDenom U V gap}
    0<gap
    (mulErrorDenom-positive {U = U} {V = V} {gap = gap} 0<U 0<V 0<gap)


private
  denom>U-path : (U V gap : ℚ) →
    U ℚ.+ ((V ℚ.+ gap) ℚ.+ 1ℚ) ≡ mulErrorDenom U V gap
  denom>U-path U V gap =
    ℚ.+Assoc U (V ℚ.+ gap) 1ℚ ∙
    cong (λ r → r ℚ.+ 1ℚ) (ℚ.+Assoc U V gap)

  denom>V-path : (U V gap : ℚ) →
    V ℚ.+ ((U ℚ.+ gap) ℚ.+ 1ℚ) ≡ mulErrorDenom U V gap
  denom>V-path U V gap =
    ℚ.+Assoc V (U ℚ.+ gap) 1ℚ ∙
    cong (λ r → r ℚ.+ 1ℚ)
      (ℚ.+Assoc V U gap ∙
       cong (λ r → r ℚ.+ gap) (ℚ.+Comm V U))

  denom>U+V-path : (U V gap : ℚ) →
    (U ℚ.+ V) ℚ.+ (gap ℚ.+ 1ℚ) ≡ mulErrorDenom U V gap
  denom>U+V-path U V gap =
    ℚ.+Assoc (U ℚ.+ V) gap 1ℚ


mulErrorDenom>U :
  {gap U V : ℚ} →
  0ℚ ℚOrder.< V →
  0ℚ ℚOrder.< gap →
  U ℚOrder.< mulErrorDenom U V gap
mulErrorDenom>U {gap = gap} {U = U} {V = V} 0<V 0<gap =
  subst (λ r → U ℚOrder.< r)
    (denom>U-path U V gap)
    (q<q+positive U ((V ℚ.+ gap) ℚ.+ 1ℚ)
      (positive-sum
        {p = V ℚ.+ gap}
        {q = 1ℚ}
        (positive-sum {p = V} {q = gap} 0<V 0<gap)
        0<1))


mulErrorDenom>V :
  {gap U V : ℚ} →
  0ℚ ℚOrder.< U →
  0ℚ ℚOrder.< gap →
  V ℚOrder.< mulErrorDenom U V gap
mulErrorDenom>V {gap = gap} {U = U} {V = V} 0<U 0<gap =
  subst (λ r → V ℚOrder.< r)
    (denom>V-path U V gap)
    (q<q+positive V ((U ℚ.+ gap) ℚ.+ 1ℚ)
      (positive-sum
        {p = U ℚ.+ gap}
        {q = 1ℚ}
        (positive-sum {p = U} {q = gap} 0<U 0<gap)
        0<1))


mulErrorDenom>U+V :
  {gap U V : ℚ} →
  0ℚ ℚOrder.< gap →
  U ℚ.+ V ℚOrder.< mulErrorDenom U V gap
mulErrorDenom>U+V {gap = gap} {U = U} {V = V} 0<gap =
  subst (λ r → U ℚ.+ V ℚOrder.< r)
    (denom>U+V-path U V gap)
    (q<q+positive (U ℚ.+ V) (gap ℚ.+ 1ℚ)
      (positive-sum {p = gap} {q = 1ℚ} 0<gap 0<1))


mulErrorScale-times-U<gap :
  {gap U V : ℚ} →
  (0<U : 0ℚ ℚOrder.< U) →
  (0<V : 0ℚ ℚOrder.< V) →
  (0<gap : 0ℚ ℚOrder.< gap) →
  mulErrorScale gap U V 0<U 0<V 0<gap ℚ.· U ℚOrder.< gap
mulErrorScale-times-U<gap {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap =
  subst (λ r → δ ℚ.· U ℚOrder.< r)
    (scaleByPositive-cancelR gap D 0<D)
    δU<δD
  where
  D : ℚ
  D = mulErrorDenom U V gap

  0<D : 0ℚ ℚOrder.< D
  0<D = mulErrorDenom-positive {U = U} {V = V} {gap = gap} 0<U 0<V 0<gap

  δ : ℚ
  δ = mulErrorScale gap U V 0<U 0<V 0<gap

  0<δ : 0ℚ ℚOrder.< δ
  0<δ = mulErrorScale-positive {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap

  U<D : U ℚOrder.< D
  U<D = mulErrorDenom>U {gap = gap} {U = U} {V = V} 0<V 0<gap

  δU<δD : δ ℚ.· U ℚOrder.< δ ℚ.· D
  δU<δD = mul-left-positive-< {a = δ} {b = U} {c = D} 0<δ U<D


mulErrorScale-times-V<gap :
  {gap U V : ℚ} →
  (0<U : 0ℚ ℚOrder.< U) →
  (0<V : 0ℚ ℚOrder.< V) →
  (0<gap : 0ℚ ℚOrder.< gap) →
  mulErrorScale gap U V 0<U 0<V 0<gap ℚ.· V ℚOrder.< gap
mulErrorScale-times-V<gap {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap =
  subst (λ r → δ ℚ.· V ℚOrder.< r)
    (scaleByPositive-cancelR gap D 0<D)
    δV<δD
  where
  D : ℚ
  D = mulErrorDenom U V gap

  0<D : 0ℚ ℚOrder.< D
  0<D = mulErrorDenom-positive {U = U} {V = V} {gap = gap} 0<U 0<V 0<gap

  δ : ℚ
  δ = mulErrorScale gap U V 0<U 0<V 0<gap

  0<δ : 0ℚ ℚOrder.< δ
  0<δ = mulErrorScale-positive {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap

  V<D : V ℚOrder.< D
  V<D = mulErrorDenom>V {gap = gap} {U = U} {V = V} 0<U 0<gap

  δV<δD : δ ℚ.· V ℚOrder.< δ ℚ.· D
  δV<δD = mul-left-positive-< {a = δ} {b = V} {c = D} 0<δ V<D


mulErrorScale-times-sum<gap :
  {gap U V : ℚ} →
  (0<U : 0ℚ ℚOrder.< U) →
  (0<V : 0ℚ ℚOrder.< V) →
  (0<gap : 0ℚ ℚOrder.< gap) →
  mulErrorScale gap U V 0<U 0<V 0<gap ℚ.· (U ℚ.+ V) ℚOrder.< gap
mulErrorScale-times-sum<gap {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap =
  subst (λ r → δ ℚ.· (U ℚ.+ V) ℚOrder.< r)
    (scaleByPositive-cancelR gap D 0<D)
    δUV<δD
  where
  D : ℚ
  D = mulErrorDenom U V gap

  0<D : 0ℚ ℚOrder.< D
  0<D = mulErrorDenom-positive {U = U} {V = V} {gap = gap} 0<U 0<V 0<gap

  δ : ℚ
  δ = mulErrorScale gap U V 0<U 0<V 0<gap

  0<δ : 0ℚ ℚOrder.< δ
  0<δ = mulErrorScale-positive {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap

  U+V<D : U ℚ.+ V ℚOrder.< D
  U+V<D = mulErrorDenom>U+V {gap = gap} {U = U} {V = V} 0<gap

  δUV<δD : δ ℚ.· (U ℚ.+ V) ℚOrder.< δ ℚ.· D
  δUV<δD =
    mul-left-positive-< {a = δ} {b = U ℚ.+ V} {c = D} 0<δ U+V<D
