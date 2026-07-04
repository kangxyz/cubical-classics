{-

Unit laws for constructive Dedekind-cut multiplication.

This module is kept separate from Cubical.DedekindCut.Arithmetic so the main
arithmetic development remains quick to typecheck while the unit-law estimates
are developed in smaller pieces.

-}
{-# OPTIONS --safe #-}
module Cubical.DedekindCut.Arithmetic.Unit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals using (ℚ)
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Cubical.DedekindCut
open import Cubical.DedekindCut.Arithmetic
import Cubical.Rationals as ℚExtra


module NonnegativeUnit {ℓ : Level} where
  open Order {ℓ}
  open Algebra {ℓ}
  open Lattice {ℓ}
  open Addition {ℓ}
  open NonnegativeMultiplication {ℓ}
  open SignedMultiplication {ℓ}

  abstract
    nnMul-idR-lower⊆ :
      (x : DedekindCut ℓ) →
      (0≤x : Nonnegative x) →
      nnMulLower x 1D ⊆ lower x
    nnMul-idR-lower⊆ x 0≤x q =
      Prop.rec (isProp∈ (lower x) q)
        (λ where
          (Sum.inl q<0) →
            0≤x q (lift q<0)
          (Sum.inr (a , b , a∈Lx , b∈L1 , 0<a , 0<b , q<ab)) →
            lower-closed x q a
              (ℚOrder.isTrans< q (a ℚ.· b) a q<ab
                (ℚExtra.mul-by-<1 {a = a} {b = b} 0<a (Lift.lower b∈L1)))
              a∈Lx)

    nnMul-idR-lower⊇-nonnegative :
      (x : DedekindCut ℓ) →
      (q : ℚ) →
      ℚExtra.0ℚ ℚOrder.≤ q →
      q ∈ lower x →
      q ∈ nnMulLower x 1D
    nnMul-idR-lower⊇-nonnegative x q 0≤q q∈Lx =
      Prop.rec squash₁ step (lower-rounded x q q∈Lx)
      where
      step :
        Σ[ a ∈ ℚ ] (q ℚOrder.< a) × (a ∈ lower x) →
        q ∈ nnMulLower x 1D
      step (a , q<a , a∈Lx) with
        ℚExtra.unit-lower-factor q a 0≤q q<a
          (ℚExtra.nonnegative-right-of-< {p = q} {q = a} 0≤q q<a)
      ... | b , 0<b , b<1 , q<ab =
        ∣ Sum.inr
            (a , b
            , a∈Lx
            , lift b<1
            , ℚExtra.nonnegative-right-of-< {p = q} {q = a} 0≤q q<a
            , 0<b
            , q<ab)
        ∣₁

    nnMul-idR-lower⊇ :
      (x : DedekindCut ℓ) →
      (0≤x : Nonnegative x) →
      lower x ⊆ nnMulLower x 1D
    nnMul-idR-lower⊇ x 0≤x q q∈Lx with ℚExtra.negative-or-nonnegative q
    ... | Sum.inl q<0 =
      ∣ Sum.inl q<0 ∣₁
    ... | Sum.inr 0≤q =
      nnMul-idR-lower⊇-nonnegative x q 0≤q q∈Lx

    nnMul-idR-upper⊆ :
      (x : DedekindCut ℓ) →
      nnMulUpper x 1D ⊆ upper x
    nnMul-idR-upper⊆ x q (0<q , q∈U) =
      Prop.rec (isProp∈ (upper x) q)
        (λ (a , b , a∈Ux , b∈U1 , 0<a , 0<b , ab<q) →
          upper-closed x a q
            (ℚOrder.isTrans< a (a ℚ.· b) q
              (ℚExtra.mul-by->1 {a = a} {b = b} 0<a (Lift.lower b∈U1))
              ab<q)
            a∈Ux)
        q∈U

    nnMul-idR-upper⊇ :
      (x : DedekindCut ℓ) →
      (0≤x : Nonnegative x) →
      upper x ⊆ nnMulUpper x 1D
    nnMul-idR-upper⊇ x 0≤x q q∈Ux =
      nonnegative-upper-positive x 0≤x q q∈Ux ,
      Prop.rec squash₁ step (upper-rounded x q q∈Ux)
      where
      step :
        Σ[ r ∈ ℚ ] (r ℚOrder.< q) × (r ∈ upper x) →
        ∥ ProductUpperWitness x 1D q ∥₁
      step (r , r<q , r∈Ux) with
        ℚExtra.unit-upper-factor r q
          (nonnegative-upper-positive x 0≤x r r∈Ux)
          r<q
      ... | b , 1<b , 0<b , rb<q =
        ∣ r , b
        , r∈Ux
        , lift 1<b
        , nonnegative-upper-positive x 0≤x r r∈Ux
        , 0<b
        , rb<q
        ∣₁

  nnMul-idR :
    (x : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    nnMul x 1D 0≤x 1D-nonnegative ≡ x
  nnMul-idR x 0≤x =
    cutExt
      (nnMul x 1D 0≤x 1D-nonnegative)
      x
      (nnMul-idR-lower⊆ x 0≤x)
      (nnMul-idR-lower⊇ x 0≤x)
      (nnMul-idR-upper⊆ x)
      (nnMul-idR-upper⊇ x 0≤x)

  nnMul-idL :
    (x : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    nnMul 1D x 1D-nonnegative 0≤x ≡ x
  nnMul-idL x 0≤x =
    nnMul-comm 1D x 1D-nonnegative 0≤x ∙
    nnMul-idR x 0≤x

  *-idR-nonnegative :
    (x : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    x * 1D ≡ x
  *-idR-nonnegative x 0≤x =
    *-of-nonnegative x 1D 0≤x 1D-nonnegative ∙
    nnMul-idR x 0≤x

  *-idL-nonnegative :
    (x : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    1D * x ≡ x
  *-idL-nonnegative x 0≤x =
    *-comm 1D x ∙
    *-idR-nonnegative x 0≤x

  *-idR-positive-negative-form :
    (x : DedekindCut ℓ) →
    x * 1D ≡ positivePart x + (- negativePart x)
  *-idR-positive-negative-form x =
    *-right-nonnegative-form x 1D 1D-nonnegative ∙
    cong₂ _+_
      (nnMul-idR (positivePart x) (positivePart-nonnegative x))
      (cong -_ (nnMul-idR (negativePart x) (negativePart-nonnegative x)))

  abstract
    plus-minus-cancelR :
      (x n : DedekindCut ℓ) →
      (x + n) + (- n) ≡ x
    plus-minus-cancelR x n =
      sym (+-assoc x n (- n)) ∙
      cong (x +_) (+-invR n) ∙
      +-idR x

    positivePart≤x+negativePart :
      (x : DedekindCut ℓ) →
      positivePart x ≤ x + negativePart x
    positivePart≤x+negativePart x =
      ⊔≤ x 0D (x + negativePart x)
        x≤x+n
        0≤x+n
      where
      n : DedekindCut ℓ
      n = negativePart x

      x≤x+n : x ≤ x + n
      x≤x+n =
        ≤-trans x (x + 0D) (x + n)
          (≡→≤ (sym (+-idR x)))
          (+-monoL-≤ 0D n x (negativePart-nonnegative x))

      0≤x+-x : 0D ≤ x + (- x)
      0≤x+-x =
        ≡→≤ (sym (+-invR x))

      x+-x≤x+n : x + (- x) ≤ x + n
      x+-x≤x+n =
        +-monoL-≤ (- x) n x (left≤⊔ (- x) 0D)

      0≤x+n : 0D ≤ x + n
      0≤x+n =
        ≤-trans 0D (x + (- x)) (x + n)
          0≤x+-x
          x+-x≤x+n

    x+negativePart≤positivePart :
      (x : DedekindCut ℓ) →
      x + negativePart x ≤ positivePart x
    x+negativePart≤positivePart x q =
      Prop.rec (isProp∈ (lower (positivePart x)) q) step
      where
      step :
        Σ[ r ∈ ℚ ] Σ[ s ∈ ℚ ]
          (r ∈ lower x) ×
          (s ∈ lower (negativePart x)) ×
          (q ℚOrder.< r ℚ.+ s) →
        q ∈ lower (positivePart x)
      step (r , s , r∈Lx , s∈Lx- , q<r+s) =
        Prop.rec squash₁ split-negative-part s∈Lx-
        where
        split-negative-part :
          (s ∈ lower (- x)) ⊎ (s ∈ lower 0D) →
          q ∈ lower (positivePart x)
        split-negative-part (Sum.inl s∈L-x) =
          ∣ Sum.inr (lift q<0) ∣₁
          where
          r<-s : r ℚOrder.< ℚ.- s
          r<-s =
            lower<upper x r (ℚ.- s) r∈Lx s∈L-x

          r<0-s : r ℚOrder.< ℚExtra.0ℚ ℚ.- s
          r<0-s =
            subst (λ v → r ℚOrder.< v)
              (sym (ℚ.+IdL (ℚ.- s)))
              r<-s

          r+s<0 : r ℚ.+ s ℚOrder.< ℚExtra.0ℚ
          r+s<0 =
            ℚExtra.diff-right<→+< r s ℚExtra.0ℚ r<0-s

          q<0 : q ℚOrder.< ℚExtra.0ℚ
          q<0 =
            ℚOrder.isTrans< q (r ℚ.+ s) ℚExtra.0ℚ q<r+s r+s<0

        split-negative-part (Sum.inr s∈L0) =
          ∣ Sum.inl q∈Lx ∣₁
          where
          r+s<r : r ℚ.+ s ℚOrder.< r
          r+s<r =
            subst (λ v → r ℚ.+ s ℚOrder.< v)
              (ℚ.+IdR r)
              (ℚOrder.<-o+ s ℚExtra.0ℚ r (Lift.lower s∈L0))

          q<r : q ℚOrder.< r
          q<r =
            ℚOrder.isTrans< q (r ℚ.+ s) r q<r+s r+s<r

          q∈Lx : q ∈ lower x
          q∈Lx =
            lower-closed x q r q<r r∈Lx

    positive-negative-decomposition :
      (x : DedekindCut ℓ) →
      positivePart x + (- negativePart x) ≡ x
    positive-negative-decomposition x =
      ≤-antisym (positivePart x + (- n)) x lhs≤x x≤lhs
      where
      n : DedekindCut ℓ
      n = negativePart x

      cancel : (x + n) + (- n) ≡ x
      cancel = plus-minus-cancelR x n

      lhs≤cancelled :
        positivePart x + (- n) ≤ (x + n) + (- n)
      lhs≤cancelled =
        +-monoR-≤ (positivePart x) (x + n) (- n)
          (positivePart≤x+negativePart x)

      lhs≤x : positivePart x + (- n) ≤ x
      lhs≤x =
        ≤-trans
          (positivePart x + (- n))
          ((x + n) + (- n))
          x
          lhs≤cancelled
          (≡→≤ cancel)

      cancelled≤lhs :
        (x + n) + (- n) ≤ positivePart x + (- n)
      cancelled≤lhs =
        +-monoR-≤ (x + n) (positivePart x) (- n)
          (x+negativePart≤positivePart x)

      x≤cancelled : x ≤ (x + n) + (- n)
      x≤cancelled =
        ≡→≤ (sym cancel)

      x≤lhs : x ≤ positivePart x + (- n)
      x≤lhs =
        ≤-trans
          x
          ((x + n) + (- n))
          (positivePart x + (- n))
          x≤cancelled
          cancelled≤lhs

  *-idR :
    (x : DedekindCut ℓ) →
    x * 1D ≡ x
  *-idR x =
    *-idR-positive-negative-form x ∙
    positive-negative-decomposition x

  *-idL :
    (x : DedekindCut ℓ) →
    1D * x ≡ x
  *-idL x =
    *-comm 1D x ∙
    *-idR x
