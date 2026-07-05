{-

Reciprocal cuts for positive constructive Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindCompletion.Arithmetic.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Nullary using (¬_)

import Constructive.Algebra.LinearlyOrderedCommRing.Base as LinearBase
open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedes
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.DedekindCompletion
open import Constructive.DedekindCompletion.Arithmetic.Base
open import Constructive.DedekindCompletion.Arithmetic.Negation
open import Constructive.DedekindCompletion.Arithmetic.NonNegative
open import Constructive.DedekindCompletion.Arithmetic.Multiplication
open import Constructive.DedekindCompletion.Arithmetic.Order

private
  variable
    ℓ ℓ' ℓᴾ : Level


module Inverse (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  inverseBaseField : LinearlyOrderedField ℓ ℓ'
  inverseBaseField = 𝒜 .fst

  open CompletionBase inverseBaseField
  module CutOrder = CompletionOrder inverseBaseField
  open CutOrder
    using
      ( _#_ ; <→≤ ; ≤-antisym ; ¬>→≤ ; lower<upper
      )
    renaming
      ( _≤_ to _≤D_
      ; _<_ to _<D_
      )
  open LinearlyOrderedFieldStr inverseBaseField
    renaming
      ( inv₊ to invK₊
      ; ·-rInv₊ to ·-rInvK₊
      ; p>0→p⁻¹>0 to invK-positive
      ; inv-Reverse< to invK-Reverse<
      ; inv₊Idem to invK-Idem
      ; inv# to invK#
      )

  open ArithmeticBase 𝒜
  open Addition {ℓᴾ}
  open Negation 𝒜 {ℓᴾ}
  open NonNegativeMultiplication 𝒜 {ℓᴾ}
  open Multiplication 𝒜 {ℓᴾ}
  open MultiplicationNegation 𝒜 {ℓᴾ}
  open OrderProperties 𝒜 {ℓᴾ}

  private
    K : Type ℓ
    K = Carrier

  InvLowerWitness : DedekindCompletion ℓᴾ → K → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  InvLowerWitness x q =
    Σ[ u ∈ K ]
      (u ∈ upper x) ×
      (Σ[ 0<u ∈ 0r < u ]
        q < invK₊ 0<u)

  InvUpperWitness : DedekindCompletion ℓᴾ → K → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  InvUpperWitness x q =
    Σ[ l ∈ K ]
      (l ∈ lower x) ×
      (Σ[ 0<l ∈ 0r < l ]
        invK₊ 0<l < q)

  invLower : DedekindCompletion ℓᴾ → Pred ℓᴾ
  invLower x q =
    ∥ (q < 0r) ⊎ InvLowerWitness x q ∥₁ ,
    squash₁

  invUpper : DedekindCompletion ℓᴾ → Pred ℓᴾ
  invUpper x q =
    (0r < q) × ∥ InvUpperWitness x q ∥₁ ,
    isProp× isProp< squash₁

  inv-lower-negative :
    (x : DedekindCompletion ℓᴾ) (q : K) →
    q < 0r →
    q ∈ invLower x
  inv-lower-negative x q q<0 = ∣ Sum.inl q<0 ∣₁

  inv-lower-witness :
    (x : DedekindCompletion ℓᴾ) (q : K) →
    InvLowerWitness x q →
    q ∈ invLower x
  inv-lower-witness x q w = ∣ Sum.inr w ∣₁

  inv-upper-witness :
    (x : DedekindCompletion ℓᴾ) (q : K) →
    0r < q →
    InvUpperWitness x q →
    q ∈ invUpper x
  inv-upper-witness x q 0<q w = 0<q , ∣ w ∣₁

  upperBound>0 :
    (x : DedekindCompletion ℓᴾ) →
    x >0𝔻 →
    ∥ Σ[ u ∈ K ] (u ∈ upper x) × (0r < u) ∥₁
  upperBound>0 x 0<x =
    ∃upper>0 x

  isDedekindCutInv₊ :
    (x : DedekindCompletion ℓᴾ) →
    x >0𝔻 →
    IsDedekindCut (invLower x) (invUpper x)
  isDedekindCutInv₊ x 0<x .IsDedekindCut.lower-inhabited =
    ∣ - 1r , inv-lower-negative x (- 1r) -1<0 ∣₁
  isDedekindCutInv₊ x 0<x .IsDedekindCut.upper-inhabited =
    Prop.rec squash₁
      (λ (l , 0<l , l∈Lx) →
        let
          q = invK₊ 0<l + 1r
          invl<q = q+1>q {q = invK₊ 0<l}
          0<invl = invK-positive 0<l
          0<q = <-trans 0<invl invl<q
        in
        ∣ q , inv-upper-witness x q 0<q (l , l∈Lx , 0<l , invl<q) ∣₁)
      (∃lower>0 x 0<x)
  isDedekindCutInv₊ x 0<x .IsDedekindCut.lower-closed =
    λ p q p<q q∈L →
      Prop.rec squash₁
        (λ where
          (Sum.inl q<0) →
            ∣ Sum.inl (<-trans p<q q<0) ∣₁
          (Sum.inr (u , u∈Ux , 0<u , q<1/u)) →
            ∣ Sum.inr
                (u , u∈Ux , 0<u ,
                 <-trans p<q q<1/u)
            ∣₁)
        q∈L
  isDedekindCutInv₊ x 0<x .IsDedekindCut.upper-closed =
    λ p q p<q (0<p , p∈U) →
      <-trans 0<p p<q ,
      Prop.rec squash₁
        (λ (l , l∈Lx , 0<l , invl<p) →
          ∣ l , l∈Lx , 0<l ,
            <-trans invl<p p<q
          ∣₁)
        p∈U
  isDedekindCutInv₊ x 0<x .IsDedekindCut.lower-rounded =
    λ q q∈L →
      Prop.rec squash₁
        (λ where
          (Sum.inl q<0) →
            Prop.rec squash₁
              (λ (r , q<r , r<0) →
                ∣ r , q<r , inv-lower-negative x r r<0 ∣₁)
              (dense q<0)
          (Sum.inr (u , u∈Ux , 0<u , q<1/u)) →
            Prop.rec squash₁
              (λ (r , q<r , r<1/u) →
                ∣ r , q<r ,
                  inv-lower-witness x r (u , u∈Ux , 0<u , r<1/u)
                ∣₁)
              (dense q<1/u))
        q∈L
  isDedekindCutInv₊ x 0<x .IsDedekindCut.upper-rounded =
    λ q (0<q , q∈U) →
      Prop.rec squash₁
        (λ (l , l∈Lx , 0<l , invl<q) →
          Prop.rec squash₁
            (λ (r , invl<r , r<q) →
              let
                0<r = <-trans (invK-positive 0<l) invl<r
              in
              ∣ r , r<q , inv-upper-witness x r 0<r (l , l∈Lx , 0<l , invl<r) ∣₁)
            (dense invl<q))
        q∈U
  isDedekindCutInv₊ x 0<x .IsDedekindCut.disjoint =
    λ q q∈L (0<q , q∈U) →
      Prop.rec2 Empty.isProp⊥ (lower-upper q 0<q) q∈L q∈U
    where
    lower-upper :
      (q : K) →
      0r < q →
      (q < 0r) ⊎ InvLowerWitness x q →
      InvUpperWitness x q →
      ⊥
    lower-upper q 0<q (Sum.inl q<0) _ =
      <-asym 0<q q<0
    lower-upper q 0<q (Sum.inr (u , u∈Ux , 0<u , q<1/u))
      (l , l∈Lx , 0<l , invl<q) =
      <-arefl invl<invl refl
      where
      l<u : l < u
      l<u = lower<upper x l u l∈Lx u∈Ux

      invu<invl : invK₊ 0<u < invK₊ 0<l
      invu<invl = invK-Reverse< 0<u 0<l l<u

      invl<invl : invK₊ 0<l < invK₊ 0<l
      invl<invl =
        <-trans invl<q
          (<-trans q<1/u invu<invl)
  isDedekindCutInv₊ x 0<x .IsDedekindCut.located =
    λ p q p<q → located-inv p q p<q
    where
    lower-from-zero :
      (p : K) →
      p ≡ 0r →
      ∥ p ∈ invLower x ∥₁
    lower-from-zero p p≡0 =
      Prop.rec squash₁
        (λ (u , u∈Ux , 0<u) →
          ∣ inv-lower-witness x p
              (u , u∈Ux , 0<u ,
               subst (λ t → t < invK₊ 0<u)
                 (sym p≡0)
                 (invK-positive 0<u))
          ∣₁)
        (upperBound>0 x 0<x)

    upper-from-lower :
      (q : K) →
      (0<q : 0r < q) →
      invK₊ 0<q ∈ lower x →
      ∥ q ∈ invUpper x ∥₁
    upper-from-lower q 0<q invq∈Lx =
      Prop.rec squash₁
        (λ (l , invq<l , l∈Lx) →
          let
            0<invq = invK-positive 0<q
            0<l = <-trans 0<invq invq<l
            invl<invinvq = invK-Reverse< 0<l 0<invq invq<l
            invinvoq≡q = invK-Idem 0<q
            invl<q =
              subst (λ t → invK₊ 0<l < t)
                invinvoq≡q
                invl<invinvq
          in
          ∣ inv-upper-witness x q 0<q (l , l∈Lx , 0<l , invl<q) ∣₁)
        (CompletionBase.lower-rounded {𝒦 = inverseBaseField} x (invK₊ 0<q) invq∈Lx)

    lower-from-upper :
      (p : K) →
      (0<p : 0r < p) →
      invK₊ 0<p ∈ upper x →
      ∥ p ∈ invLower x ∥₁
    lower-from-upper p 0<p invp∈Ux =
      Prop.rec squash₁
        (λ (u , u<invp , u∈Ux) →
          let
            0≤x = >0→≥0 x 0<x
            0<u = ≥0+upper→>0 x 0≤x u u∈Ux
            invinvp>invu = invK-Reverse< (invK-positive 0<p) 0<u u<invp
            p<invu =
              subst (λ t → t < invK₊ 0<u)
                (invK-Idem 0<p)
                invinvp>invu
          in
          ∣ inv-lower-witness x p (u , u∈Ux , 0<u , p<invu) ∣₁)
        (CompletionBase.upper-rounded {𝒦 = inverseBaseField} x (invK₊ 0<p) invp∈Ux)

    located-positive :
      (p q : K) →
      (0<p : 0r < p) →
      (0<q : 0r < q) →
      p < q →
      ∥ (p ∈ invLower x) ⊎ (q ∈ invUpper x) ∥₁
    located-positive p q 0<p 0<q p<q =
      Prop.rec squash₁
        (λ where
          (Sum.inl invq∈Lx) →
            Prop.rec squash₁
              (λ q∈U → ∣ Sum.inr q∈U ∣₁)
              (upper-from-lower q 0<q invq∈Lx)
          (Sum.inr invp∈Ux) →
            Prop.rec squash₁
              (λ p∈L → ∣ Sum.inl p∈L ∣₁)
              (lower-from-upper p 0<p invp∈Ux))
        (CompletionBase.located {𝒦 = inverseBaseField} x
          (invK₊ 0<q)
          (invK₊ 0<p)
          (invK-Reverse< 0<q 0<p p<q))

    located-inv :
      (p q : K) →
      p < q →
      ∥ (p ∈ invLower x) ⊎ (q ∈ invUpper x) ∥₁
    located-inv-positive-q :
      (p q : K) →
      (0<q : 0r < q) →
      p < q →
      ∥ (p ∈ invLower x) ⊎ (q ∈ invUpper x) ∥₁
    located-inv-positive-q p q 0<q p<q with trichotomy 0r p
    ... | LinearBase.lt 0<p = located-positive p q 0<p 0<q p<q
    ... | LinearBase.eq 0≡p =
      Prop.rec squash₁
        (λ p∈L → ∣ Sum.inl p∈L ∣₁)
        (lower-from-zero p (sym 0≡p))
    ... | LinearBase.gt p<0 =
      ∣ Sum.inl (inv-lower-negative x p p<0) ∣₁

    located-inv p q p<q with trichotomy 0r q
    ... | LinearBase.lt 0<q = located-inv-positive-q p q 0<q p<q
    ... | LinearBase.eq 0≡q =
      ∣ Sum.inl
          (inv-lower-negative x p
            (transport (λ i → p < 0≡q (~ i)) p<q))
      ∣₁
    ... | LinearBase.gt q<0 =
      ∣ Sum.inl (inv-lower-negative x p
          (<-trans p<q q<0))
      ∣₁

  inv𝔻₊ :
    (x : DedekindCompletion ℓᴾ) →
    x >0𝔻 →
    DedekindCompletion ℓᴾ
  inv𝔻₊ x 0<x .lower = invLower x
  inv𝔻₊ x 0<x .upper = invUpper x
  inv𝔻₊ x 0<x .isDedekindCut = isDedekindCutInv₊ x 0<x

  inv𝔻₊≥0 :
    (x : DedekindCompletion ℓᴾ) →
    (0<x : x >0𝔻) →
    (inv𝔻₊ x 0<x) ≥0
  inv𝔻₊≥0 x 0<x q q<0 =
    inv-lower-negative x q (Lift.lower q<0)

  private
    mul-below-one :
      {a b u : K} →
      a < u →
      (0<u : 0r < u) →
      (0<b : 0r < b) →
      b < invK₊ 0<u →
      a · b < 1r
    mul-below-one {a = a} {b = b} {u = u} a<u 0<u 0<b b<1/u =
      <-trans
        (·-rPosPres< {x = b} 0<b a<u)
        u*b<1
      where
      u*b<1 : u · b < 1r
      u*b<1 =
        subst (λ t → u · b < t)
          (·-rInvK₊ 0<u)
          (·-lPosPres< 0<u b<1/u)

    one-below-mul :
      {l a b : K} →
      (0<l : 0r < l) →
      l < a →
      invK₊ 0<l < b →
      1r < a · b
    one-below-mul {l = l} {a = a} {b = b} 0<l l<a 1/l<b =
      <-trans 1<a/l a/l<ab
      where
      0<1/l : 0r < invK₊ 0<l
      0<1/l = invK-positive 0<l

      0<a : 0r < a
      0<a = <-trans 0<l l<a

      1<a/l : 1r < a · invK₊ 0<l
      1<a/l =
        subst (λ t → t < a · invK₊ 0<l)
          (·-rInvK₊ 0<l)
          (·-rPosPres< {x = invK₊ 0<l} 0<1/l l<a)

      a/l<ab : a · invK₊ 0<l < a · b
      a/l<ab =
        ·-lPosPres< 0<a 1/l<b

  ·-rInv𝔻₊ :
    (x : DedekindCompletion ℓᴾ) →
    (0<x : x >0𝔻) →
    x *𝔻 inv𝔻₊ x 0<x ≡ 1𝔻
  ·-rInv𝔻₊ x 0<x =
    ≤-antisym (x *𝔻 invD) 1𝔻
      (¬>→≤ (x *𝔻 invD) 1𝔻 not-1<product)
      (¬>→≤ 1𝔻 (x *𝔻 invD) not-product<1)
    where
    invD : DedekindCompletion ℓᴾ
    invD = inv𝔻₊ x 0<x

    0≤x : x ≥0
    0≤x = >0→≥0 x 0<x

    0≤inv : invD ≥0
    0≤inv = inv𝔻₊≥0 x 0<x

    product≡nn : x *𝔻 invD ≡ nnMul x invD 0≤x 0≤inv
    product≡nn = *𝔻-of-≥0 x invD 0≤x 0≤inv

    not-1<product : ¬ 1𝔻 <D x *𝔻 invD
    not-1<product =
      Prop.rec Empty.isProp⊥
        (λ (q , 1<q , q∈Lproduct) →
          let
            q∈Lnn : q ∈ nnMulLower x invD
            q∈Lnn = subst (λ z → q ∈ lower z) product≡nn q∈Lproduct
          in
          Prop.rec Empty.isProp⊥
            (λ where
              (Sum.inl q<0) →
                <-asym (<-trans 1>0 (Lift.lower 1<q)) q<0
              (Sum.inr (a , b , a∈Lx , b∈Linv , 0<a , 0<b , q<ab)) →
                Prop.rec Empty.isProp⊥
                  (λ where
                    (Sum.inl b<0) →
                      <-asym 0<b b<0
                    (Sum.inr (u , u∈Ux , 0<u , b<1/u)) →
                      let
                        a<u : a < u
                        a<u = lower<upper x a u a∈Lx u∈Ux

                        ab<1 : a · b < 1r
                        ab<1 = mul-below-one a<u 0<u 0<b b<1/u

                        1<1 : 1r < 1r
                        1<1 =
                          <-trans (Lift.lower 1<q)
                            (<-trans q<ab ab<1)
                      in
                      <-arefl 1<1 refl)
                  b∈Linv)
            q∈Lnn)

    not-product<1 : ¬ (x *𝔻 invD) <D 1𝔻
    not-product<1 =
      Prop.rec Empty.isProp⊥
        (λ (q , q∈Uproduct , q<1) →
          let
            q∈Unn : q ∈ nnMulUpper x invD
            q∈Unn = subst (λ z → q ∈ upper z) product≡nn q∈Uproduct
          in
          Prop.rec Empty.isProp⊥
            (λ (a , b , a∈Ux , b∈Uinv , 0<a , 0<b , ab<q) →
              Prop.rec Empty.isProp⊥
                (λ (l , l∈Lx , 0<l , 1/l<b) →
                  let
                    l<a : l < a
                    l<a = lower<upper x l a l∈Lx a∈Ux

                    1<ab : 1r < a · b
                    1<ab = one-below-mul 0<l l<a 1/l<b

                    1<1 : 1r < 1r
                    1<1 =
                      <-trans
                        (<-trans 1<ab ab<q)
                        (Lift.lower q<1)
                  in
                  <-arefl 1<1 refl)
                (b∈Uinv .snd))
            (q∈Unn .snd))

  neg-reverse<0 :
    (x : DedekindCompletion ℓᴾ) →
    x <D 0𝔻 →
    (-𝔻 x) >0𝔻
  neg-reverse<0 x x<0 =
    subst (λ z → z <D (-𝔻 x))
      neg-0𝔻
      (neg-<-reverse x 0𝔻 x<0)

  HasInv# : DedekindCompletion ℓᴾ → Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ)))
  HasInv# x = Σ[ y ∈ DedekindCompletion ℓᴾ ] x *𝔻 y ≡ 1𝔻

  inv# :
    (x : DedekindCompletion ℓᴾ) →
    x # 0𝔻 →
    HasInv# x
  inv# x (Sum.inr 0<x) =
    inv𝔻₊ x 0<x , ·-rInv𝔻₊ x 0<x
  inv# x (Sum.inl x<0) =
    -𝔻 nx⁻¹ ,
    *𝔻-negR x nx⁻¹ ∙
    sym (*𝔻-negL x nx⁻¹) ∙
    ·-rInv𝔻₊ (-𝔻 x) 0<-x
    where
    0<-x : (-𝔻 x) >0𝔻
    0<-x = neg-reverse<0 x x<0

    nx⁻¹ : DedekindCompletion ℓᴾ
    nx⁻¹ = inv𝔻₊ (-𝔻 x) 0<-x
