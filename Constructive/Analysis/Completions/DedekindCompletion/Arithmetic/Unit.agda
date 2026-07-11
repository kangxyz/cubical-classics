{-

Unit laws for constructive Dedekind-completion multiplication

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Unit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Analysis.Completions.DedekindCompletion.Base
open import Constructive.Analysis.Completions.DedekindCompletion.Order
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Addition
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Negation
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.NonnegativeProduct
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Multiplication
open import Constructive.Foundations.Powerset hiding (Pred)

private
  variable
    ℓ ℓ' ℓᴾ : Level


module UnitProperties (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  baseField : LinearlyOrderedField ℓ ℓ'
  baseField = 𝒜 .fst

  open CompletionBase baseField
  module UnitOrder = CompletionOrder baseField
  open UnitOrder
    using
      ( ⊔≤ ; left≤⊔
      )
    renaming
      ( ≡→≤ to ≡→≤D
      ; ≤-trans to ≤D-trans
      ; ≤-antisym to ≤D-antisym
      ; lower<upper to lower<upperD
      )
  open LinearlyOrderedFieldStr baseField

  open Addition 𝒜 {ℓᴾ}
  open Negation 𝒜 {ℓᴾ}
  open AdditiveGroup 𝒜 {ℓᴾ}
  open NonnegativeProduct 𝒜 {ℓᴾ}
  open Multiplication 𝒜 {ℓᴾ}

  private
    K : Type ℓ
    K = baseField .fst .fst .fst

  abstract
    nnMul-idR-lower⊆ :
      (x : DedekindCompletion ℓᴾ) →
      (0≤x : x ≥0) →
      nnMulLower x 1𝔻 ⊆ lower x
    nnMul-idR-lower⊆ x 0≤x q =
      Prop.rec (isProp∈ (lower x) q)
        (λ where
          (Sum.inl q<0) →
            0≤x q (lift q<0)
          (Sum.inr (a , b , a∈Lx , b∈L1 , 0<a , 0<b , q<ab)) →
            CompletionBase.lower-closed {𝒦 = baseField} x q a
              (<-trans q<ab
                (mul-by-<1 0<a (Lift.lower b∈L1)))
              a∈Lx)

    nnMul-idR-lower⊇-≥0 :
      (x : DedekindCompletion ℓᴾ) →
      (q : K) →
      0r ≤ q →
      q ∈ lower x →
      q ∈ nnMulLower x 1𝔻
    nnMul-idR-lower⊇-≥0 x q 0≤q q∈Lx =
      Prop.rec squash₁ step (CompletionBase.lower-rounded {𝒦 = baseField} x q q∈Lx)
      where
      step :
        Σ[ a ∈ K ] (q < a) × (a ∈ lower x) →
        q ∈ nnMulLower x 1𝔻
      step (a , q<a , a∈Lx) with
        unit-lower-factor q a 0≤q q<a
          (≤<-trans 0≤q q<a)
      ... | b , 0<b , b<1 , q<ab =
        ∣ Sum.inr
            (a , b
            , a∈Lx
            , lift b<1
            , ≤<-trans 0≤q q<a
            , 0<b
            , q<ab)
        ∣₁

    nnMul-idR-lower⊇ :
      (x : DedekindCompletion ℓᴾ) →
      (0≤x : x ≥0) →
      lower x ⊆ nnMulLower x 1𝔻
    nnMul-idR-lower⊇ x 0≤x q q∈Lx with negative-or-nonnegative q
    ... | Sum.inl q<0 =
      ∣ Sum.inl q<0 ∣₁
    ... | Sum.inr 0≤q =
      nnMul-idR-lower⊇-≥0 x q 0≤q q∈Lx

    nnMul-idR-upper⊆ :
      (x : DedekindCompletion ℓᴾ) →
      nnMulUpper x 1𝔻 ⊆ upper x
    nnMul-idR-upper⊆ x q (0<q , q∈U) =
      Prop.rec (isProp∈ (upper x) q)
        (λ (a , b , a∈Ux , b∈U1 , 0<a , 0<b , ab<q) →
          CompletionBase.upper-closed {𝒦 = baseField} x a q
            (<-trans
              (mul-by->1 0<a (Lift.lower b∈U1))
              ab<q)
            a∈Ux)
        q∈U

    nnMul-idR-upper⊇ :
      (x : DedekindCompletion ℓᴾ) →
      (0≤x : x ≥0) →
      upper x ⊆ nnMulUpper x 1𝔻
    nnMul-idR-upper⊇ x 0≤x q q∈Ux =
      ≥0+upper→>0 x 0≤x q q∈Ux ,
      Prop.rec squash₁ step (CompletionBase.upper-rounded {𝒦 = baseField} x q q∈Ux)
      where
      step :
        Σ[ r ∈ K ] (r < q) × (r ∈ upper x) →
        ∥ ProductUpperWitness x 1𝔻 q ∥₁
      step (r , r<q , r∈Ux) with
        unit-upper-factor r q
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
    (x : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    nnMul x 1𝔻 0≤x 1𝔻≥0 ≡ x
  nnMul-idR x 0≤x =
    completionExt
      (nnMul x 1𝔻 0≤x 1𝔻≥0)
      x
      (nnMul-idR-lower⊆ x 0≤x)
      (nnMul-idR-lower⊇ x 0≤x)
      (nnMul-idR-upper⊆ x)
      (nnMul-idR-upper⊇ x 0≤x)

  nnMul-idL :
    (x : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    nnMul 1𝔻 x 1𝔻≥0 0≤x ≡ x
  nnMul-idL x 0≤x =
    nnMul-comm 1𝔻 x 1𝔻≥0 0≤x ∙
    nnMul-idR x 0≤x

  *𝔻-idR-≥0 :
    (x : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    x *𝔻 1𝔻 ≡ x
  *𝔻-idR-≥0 x 0≤x =
    *𝔻-of-≥0 x 1𝔻 0≤x 1𝔻≥0 ∙
    nnMul-idR x 0≤x

  *𝔻-idL-≥0 :
    (x : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    1𝔻 *𝔻 x ≡ x
  *𝔻-idL-≥0 x 0≤x =
    *𝔻-comm 1𝔻 x ∙
    *𝔻-idR-≥0 x 0≤x

  *𝔻-idR-positive-negative-form :
    (x : DedekindCompletion ℓᴾ) →
    x *𝔻 1𝔻 ≡ posPart x +𝔻 (-𝔻 negPart x)
  *𝔻-idR-positive-negative-form x =
    *𝔻-r≥0-form x 1𝔻 1𝔻≥0 ∙
    cong₂ _+𝔻_
      (nnMul-idR (posPart x) (posPart≥0 x))
      (cong -𝔻_ (nnMul-idR (negPart x) (negPart≥0 x)))

  abstract
    posPart≤x+negPart :
      (x : DedekindCompletion ℓᴾ) →
      UnitOrder._≤_ (posPart x) (x +𝔻 negPart x)
    posPart≤x+negPart x =
      ⊔≤ x 0𝔻 (x +𝔻 negPart x)
        x≤x+n
        0≤x+n
      where
      n : DedekindCompletion ℓᴾ
      n = negPart x

      x≤x+n : UnitOrder._≤_ x (x +𝔻 n)
      x≤x+n =
        ≤D-trans x (x +𝔻 0𝔻) (x +𝔻 n)
          (≡→≤D (sym (+-idR x)))
          (+-monoL-≤ 0𝔻 n x (negPart≥0 x))

      0≤x+-x : UnitOrder._≤_ 0𝔻 (x +𝔻 (-𝔻 x))
      0≤x+-x =
        ≡→≤D (sym (+-invR x))

      x+-x≤x+n : UnitOrder._≤_ (x +𝔻 (-𝔻 x)) (x +𝔻 n)
      x+-x≤x+n =
        +-monoL-≤ (-𝔻 x) n x (left≤⊔ (-𝔻 x) 0𝔻)

      0≤x+n : UnitOrder._≤_ 0𝔻 (x +𝔻 n)
      0≤x+n =
        ≤D-trans 0𝔻 (x +𝔻 (-𝔻 x)) (x +𝔻 n)
          0≤x+-x
          x+-x≤x+n

    x+negPart≤posPart :
      (x : DedekindCompletion ℓᴾ) →
      UnitOrder._≤_ (x +𝔻 negPart x) (posPart x)
    x+negPart≤posPart x q =
      Prop.rec (isProp∈ (lower (posPart x)) q) step
      where
      step :
        Σ[ r ∈ K ] Σ[ s ∈ K ]
          (r ∈ lower x) ×
          (s ∈ lower (negPart x)) ×
          (q < r + s) →
        q ∈ lower (posPart x)
      step (r , s , r∈Lx , s∈Lx- , q<r+s) =
        Prop.rec squash₁ split-negative-part s∈Lx-
        where
        split-negative-part :
          (s ∈ lower (-𝔻 x)) ⊎ (s ∈ lower 0𝔻) →
          q ∈ lower (posPart x)
        split-negative-part (Sum.inl s∈L-x) =
          ∣ Sum.inr (lift q<0) ∣₁
          where
          r<-s : r < - s
          r<-s =
            lower<upperD x r (- s) r∈Lx s∈L-x

          r<0-s : r < 0r - s
          r<0-s =
            subst (λ v → r < v)
              (sym (+IdL (- s)))
              r<-s

          r+s<0 : r + s < 0r
          r+s<0 =
            -MoveRToL< r<0-s

          q<0 : q < 0r
          q<0 =
            <-trans q<r+s r+s<0

        split-negative-part (Sum.inr s∈L0) =
          ∣ Sum.inl q∈Lx ∣₁
          where
          r+s<r : r + s < r
          r+s<r =
            +-rNeg→< (Lift.lower s∈L0)

          q<r : q < r
          q<r =
            <-trans q<r+s r+s<r

          q∈Lx : q ∈ lower x
          q∈Lx =
            CompletionBase.lower-closed {𝒦 = baseField} x q r q<r r∈Lx

    positive-negative-decomposition :
      (x : DedekindCompletion ℓᴾ) →
      posPart x +𝔻 (-𝔻 negPart x) ≡ x
    positive-negative-decomposition x =
      cong (_+𝔻 (-𝔻 n))
        (≤D-antisym (posPart x) (x +𝔻 n)
          (posPart≤x+negPart x)
          (x+negPart≤posPart x)) ∙
      plus-minus-cancelR x n
      where
      n : DedekindCompletion ℓᴾ
      n = negPart x

  *𝔻-idR :
    (x : DedekindCompletion ℓᴾ) →
    x *𝔻 1𝔻 ≡ x
  *𝔻-idR x =
    *𝔻-idR-positive-negative-form x ∙
    positive-negative-decomposition x

  *𝔻-idL :
    (x : DedekindCompletion ℓᴾ) →
    1𝔻 *𝔻 x ≡ x
  *𝔻-idL x =
    *𝔻-comm 1𝔻 x ∙
    *𝔻-idR x
