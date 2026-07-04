{-

Unit laws for constructive Dedekind-cut multiplication.

This module is kept separate from Constructive.DedekindCut.Arithmetic so the main
arithmetic development remains quick to typecheck while the unit-law estimates
are developed in smaller pieces.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindCut.Arithmetic.Unit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals using (ℚ)
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Constructive.DedekindCut
open import Constructive.DedekindCut.Arithmetic.Base
open import Constructive.DedekindCut.Arithmetic.AdditiveGroup
import Constructive.Rationals as ℚExtra


module UnitProperties {ℓ : Level} where
  open Order {ℓ}
  open Algebra {ℓ}
  open Lattice {ℓ}
  open Addition {ℓ}
  open AdditiveGroup {ℓ}
  open NonNegativeMultiplication {ℓ}
  open Multiplication {ℓ}

  abstract
    nnMul-idR-lower⊆ :
      (x : DedekindCut ℓ) →
      (0≤x : x ≥0) →
      nnMulLower x 1𝔻 ⊆ lower x
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

    nnMul-idR-lower⊇-≥0 :
      (x : DedekindCut ℓ) →
      (q : ℚ) →
      ℚExtra.0ℚ ℚOrder.≤ q →
      q ∈ lower x →
      q ∈ nnMulLower x 1𝔻
    nnMul-idR-lower⊇-≥0 x q 0≤q q∈Lx =
      Prop.rec squash₁ step (lower-rounded x q q∈Lx)
      where
      step :
        Σ[ a ∈ ℚ ] (q ℚOrder.< a) × (a ∈ lower x) →
        q ∈ nnMulLower x 1𝔻
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
      (0≤x : x ≥0) →
      lower x ⊆ nnMulLower x 1𝔻
    nnMul-idR-lower⊇ x 0≤x q q∈Lx with ℚExtra.negative-or-nonnegative q
    ... | Sum.inl q<0 =
      ∣ Sum.inl q<0 ∣₁
    ... | Sum.inr 0≤q =
      nnMul-idR-lower⊇-≥0 x q 0≤q q∈Lx

    nnMul-idR-upper⊆ :
      (x : DedekindCut ℓ) →
      nnMulUpper x 1𝔻 ⊆ upper x
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
      (0≤x : x ≥0) →
      upper x ⊆ nnMulUpper x 1𝔻
    nnMul-idR-upper⊇ x 0≤x q q∈Ux =
      ≥0+upper→>0 x 0≤x q q∈Ux ,
      Prop.rec squash₁ step (upper-rounded x q q∈Ux)
      where
      step :
        Σ[ r ∈ ℚ ] (r ℚOrder.< q) × (r ∈ upper x) →
        ∥ ProductUpperWitness x 1𝔻 q ∥₁
      step (r , r<q , r∈Ux) with
        ℚExtra.unit-upper-factor r q
          (≥0+upper→>0 x 0≤x r r∈Ux)
          r<q
      ... | b , 1<b , 0<b , rb<q =
        ∣ r , b
        , r∈Ux
        , lift 1<b
        , ≥0+upper→>0 x 0≤x r r∈Ux
        , 0<b
        , rb<q
        ∣₁

  nnMul-idR :
    (x : DedekindCut ℓ) →
    (0≤x : x ≥0) →
    nnMul x 1𝔻 0≤x 1𝔻≥0 ≡ x
  nnMul-idR x 0≤x =
    cutExt
      (nnMul x 1𝔻 0≤x 1𝔻≥0)
      x
      (nnMul-idR-lower⊆ x 0≤x)
      (nnMul-idR-lower⊇ x 0≤x)
      (nnMul-idR-upper⊆ x)
      (nnMul-idR-upper⊇ x 0≤x)

  nnMul-idL :
    (x : DedekindCut ℓ) →
    (0≤x : x ≥0) →
    nnMul 1𝔻 x 1𝔻≥0 0≤x ≡ x
  nnMul-idL x 0≤x =
    nnMul-comm 1𝔻 x 1𝔻≥0 0≤x ∙
    nnMul-idR x 0≤x

  *-idR-≥0 :
    (x : DedekindCut ℓ) →
    (0≤x : x ≥0) →
    x * 1𝔻 ≡ x
  *-idR-≥0 x 0≤x =
    *-of-≥0 x 1𝔻 0≤x 1𝔻≥0 ∙
    nnMul-idR x 0≤x

  *-idL-≥0 :
    (x : DedekindCut ℓ) →
    (0≤x : x ≥0) →
    1𝔻 * x ≡ x
  *-idL-≥0 x 0≤x =
    *-comm 1𝔻 x ∙
    *-idR-≥0 x 0≤x

  *-idR-positive-negative-form :
    (x : DedekindCut ℓ) →
    x * 1𝔻 ≡ posPart x + (- negPart x)
  *-idR-positive-negative-form x =
    *-r≥0-form x 1𝔻 1𝔻≥0 ∙
    cong₂ _+_
      (nnMul-idR (posPart x) (posPart≥0 x))
      (cong -_ (nnMul-idR (negPart x) (negPart≥0 x)))

  abstract
    posPart≤x+negPart :
      (x : DedekindCut ℓ) →
      posPart x ≤ x + negPart x
    posPart≤x+negPart x =
      ⊔≤ x 0𝔻 (x + negPart x)
        x≤x+n
        0≤x+n
      where
      n : DedekindCut ℓ
      n = negPart x

      x≤x+n : x ≤ x + n
      x≤x+n =
        ≤-trans x (x + 0𝔻) (x + n)
          (≡→≤ (sym (+-idR x)))
          (+-monoL-≤ 0𝔻 n x (negPart≥0 x))

      0≤x+-x : 0𝔻 ≤ x + (- x)
      0≤x+-x =
        ≡→≤ (sym (+-invR x))

      x+-x≤x+n : x + (- x) ≤ x + n
      x+-x≤x+n =
        +-monoL-≤ (- x) n x (left≤⊔ (- x) 0𝔻)

      0≤x+n : 0𝔻 ≤ x + n
      0≤x+n =
        ≤-trans 0𝔻 (x + (- x)) (x + n)
          0≤x+-x
          x+-x≤x+n

    x+negPart≤posPart :
      (x : DedekindCut ℓ) →
      x + negPart x ≤ posPart x
    x+negPart≤posPart x q =
      Prop.rec (isProp∈ (lower (posPart x)) q) step
      where
      step :
        Σ[ r ∈ ℚ ] Σ[ s ∈ ℚ ]
          (r ∈ lower x) ×
          (s ∈ lower (negPart x)) ×
          (q ℚOrder.< r ℚ.+ s) →
        q ∈ lower (posPart x)
      step (r , s , r∈Lx , s∈Lx- , q<r+s) =
        Prop.rec squash₁ split-negative-part s∈Lx-
        where
        split-negative-part :
          (s ∈ lower (- x)) ⊎ (s ∈ lower 0𝔻) →
          q ∈ lower (posPart x)
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
      posPart x + (- negPart x) ≡ x
    positive-negative-decomposition x =
      cong (_+ (- n))
        (≤-antisym (posPart x) (x + n)
          (posPart≤x+negPart x)
          (x+negPart≤posPart x)) ∙
      plus-minus-cancelR x n
      where
      n : DedekindCut ℓ
      n = negPart x

  *-idR :
    (x : DedekindCut ℓ) →
    x * 1𝔻 ≡ x
  *-idR x =
    *-idR-positive-negative-form x ∙
    positive-negative-decomposition x

  *-idL :
    (x : DedekindCut ℓ) →
    1𝔻 * x ≡ x
  *-idL x =
    *-comm 1𝔻 x ∙
    *-idR x
