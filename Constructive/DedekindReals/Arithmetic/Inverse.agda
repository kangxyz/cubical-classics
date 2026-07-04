{-

reciprocal >0 cuts for constructive Dedekind reals.

For a positive cut `x`, the reciprocal is defined by the standard rational
Dedekind real:

  q < 1/x  iff  q < 0 or q < 1/u for some positive upper bound u of x
  1/x < q  iff  q > 0 and 1/l < q for some positive lower bound l of x

The definition and cut laws are constructive; the sign information comes from
the input proof `0𝔻 < x`.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindReals.Arithmetic.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Rationals using (ℚ)
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Nullary using (¬_)

open import Constructive.DedekindReals
open import Constructive.DedekindReals.Arithmetic.Base
open import Constructive.DedekindReals.Arithmetic.Negation
open import Constructive.DedekindReals.Arithmetic.Order
import Constructive.Rationals as ℚExtra


module Inverse {ℓ : Level} where
  open Order {ℓ}
  open RationalEmbedding {ℓ}
  open Algebra {ℓ}
  open Addition {ℓ}
  open NonNegativeMultiplication {ℓ}
  open Multiplication {ℓ}
  open NegationProperties {ℓ}
  open OrderProperties {ℓ}

  InvLowerWitness : DedekindReal ℓ → ℚ → Type ℓ
  InvLowerWitness x q =
    Σ[ u ∈ ℚ ]
      (u ∈ upper x) ×
      (Σ[ 0<u ∈ ℚExtra.0ℚ ℚOrder.< u ]
        q ℚOrder.< ℚExtra.posInv u 0<u)

  InvUpperWitness : DedekindReal ℓ → ℚ → Type ℓ
  InvUpperWitness x q =
    Σ[ l ∈ ℚ ]
      (l ∈ lower x) ×
      (Σ[ 0<l ∈ ℚExtra.0ℚ ℚOrder.< l ]
        ℚExtra.posInv l 0<l ℚOrder.< q)

  invLower : DedekindReal ℓ → ℚPred ℓ
  invLower x q =
    ∥ (q ℚOrder.< ℚExtra.0ℚ) ⊎ InvLowerWitness x q ∥₁ ,
    squash₁

  invUpper : DedekindReal ℓ → ℚPred ℓ
  invUpper x q =
    (ℚExtra.0ℚ ℚOrder.< q) × ∥ InvUpperWitness x q ∥₁ ,
    isProp× (ℚOrder.isProp< ℚExtra.0ℚ q) squash₁

  inv-lower-negative :
    (x : DedekindReal ℓ) (q : ℚ) →
    q ℚOrder.< ℚExtra.0ℚ →
    q ∈ invLower x
  inv-lower-negative x q q<0 = ∣ Sum.inl q<0 ∣₁

  inv-lower-witness :
    (x : DedekindReal ℓ) (q : ℚ) →
    InvLowerWitness x q →
    q ∈ invLower x
  inv-lower-witness x q w = ∣ Sum.inr w ∣₁

  inv-upper-witness :
    (x : DedekindReal ℓ) (q : ℚ) →
    ℚExtra.0ℚ ℚOrder.< q →
    InvUpperWitness x q →
    q ∈ invUpper x
  inv-upper-witness x q 0<q w = 0<q , ∣ w ∣₁

  upperBound>0 :
    (x : DedekindReal ℓ) →
    x >0 →
    ∥ Σ[ u ∈ ℚ ] (u ∈ upper x) × (ℚExtra.0ℚ ℚOrder.< u) ∥₁
  upperBound>0 x 0<x =
    ∃upper>0 x

  isDedekindRealInv₊ :
    (x : DedekindReal ℓ) →
    x >0 →
    IsDedekindReal (invLower x) (invUpper x)
  isDedekindRealInv₊ x 0<x .IsDedekindReal.lower-inhabited =
    ∣ ℚExtra.-1ℚ , inv-lower-negative x ℚExtra.-1ℚ ℚExtra.-1<0 ∣₁
  isDedekindRealInv₊ x 0<x .IsDedekindReal.upper-inhabited =
    Prop.rec squash₁
      (λ (l , 0<l , l∈Lx) →
        let
          q = ℚExtra.posInv l 0<l ℚ.+ ℚExtra.1ℚ
          invl<q = ℚExtra.q<q+1 (ℚExtra.posInv l 0<l)
          0<invl = ℚExtra.posInv-positive {q = l} 0<l
          0<q = ℚOrder.isTrans< ℚExtra.0ℚ (ℚExtra.posInv l 0<l) q 0<invl invl<q
        in
        ∣ q , inv-upper-witness x q 0<q (l , l∈Lx , 0<l , invl<q) ∣₁)
      (∃lower>0 x 0<x)
  isDedekindRealInv₊ x 0<x .IsDedekindReal.lower-closed =
    λ p q p<q q∈L →
      Prop.rec squash₁
        (λ where
          (Sum.inl q<0) →
            ∣ Sum.inl (ℚOrder.isTrans< p q ℚExtra.0ℚ p<q q<0) ∣₁
          (Sum.inr (u , u∈Ux , 0<u , q<1/u)) →
            ∣ Sum.inr
                (u , u∈Ux , 0<u ,
                 ℚOrder.isTrans< p q (ℚExtra.posInv u 0<u) p<q q<1/u)
            ∣₁)
        q∈L
  isDedekindRealInv₊ x 0<x .IsDedekindReal.upper-closed =
    λ p q p<q (0<p , p∈U) →
      ℚOrder.isTrans< ℚExtra.0ℚ p q 0<p p<q ,
      Prop.rec squash₁
        (λ (l , l∈Lx , 0<l , invl<p) →
          ∣ l , l∈Lx , 0<l ,
            ℚOrder.isTrans< (ℚExtra.posInv l 0<l) p q invl<p p<q
          ∣₁)
        p∈U
  isDedekindRealInv₊ x 0<x .IsDedekindReal.lower-rounded =
    λ q q∈L →
      Prop.rec squash₁
        (λ where
          (Sum.inl q<0) →
            Prop.rec squash₁
              (λ (r , q<r , r<0) →
                ∣ r , q<r , inv-lower-negative x r r<0 ∣₁)
              (ℚExtra.dense {p = q} {q = ℚExtra.0ℚ} q<0)
          (Sum.inr (u , u∈Ux , 0<u , q<1/u)) →
            Prop.rec squash₁
              (λ (r , q<r , r<1/u) →
                ∣ r , q<r ,
                  inv-lower-witness x r (u , u∈Ux , 0<u , r<1/u)
                ∣₁)
              (ℚExtra.dense {p = q} {q = ℚExtra.posInv u 0<u} q<1/u))
        q∈L
  isDedekindRealInv₊ x 0<x .IsDedekindReal.upper-rounded =
    λ q (0<q , q∈U) →
      Prop.rec squash₁
        (λ (l , l∈Lx , 0<l , invl<q) →
          Prop.rec squash₁
            (λ (r , invl<r , r<q) →
              let
                0<r = ℚOrder.isTrans< ℚExtra.0ℚ (ℚExtra.posInv l 0<l) r
                  (ℚExtra.posInv-positive {q = l} 0<l)
                  invl<r
              in
              ∣ r , r<q , inv-upper-witness x r 0<r (l , l∈Lx , 0<l , invl<r) ∣₁)
            (ℚExtra.dense {p = ℚExtra.posInv l 0<l} {q = q} invl<q))
        q∈U
  isDedekindRealInv₊ x 0<x .IsDedekindReal.disjoint =
    λ q q∈L (0<q , q∈U) →
      Prop.rec2 Empty.isProp⊥ (lower-upper q 0<q) q∈L q∈U
    where
    lower-upper :
      (q : ℚ) →
      ℚExtra.0ℚ ℚOrder.< q →
      (q ℚOrder.< ℚExtra.0ℚ) ⊎ InvLowerWitness x q →
      InvUpperWitness x q →
      ⊥
    lower-upper q 0<q (Sum.inl q<0) _ =
      ℚOrder.isAsym< ℚExtra.0ℚ q 0<q q<0
    lower-upper q 0<q (Sum.inr (u , u∈Ux , 0<u , q<1/u))
      (l , l∈Lx , 0<l , invl<q) =
      ℚOrder.isIrrefl< (ℚExtra.posInv l 0<l) invl<invl
      where
      l<u : l ℚOrder.< u
      l<u = lower<upper x l u l∈Lx u∈Ux

      invu<invl : ℚExtra.posInv u 0<u ℚOrder.< ℚExtra.posInv l 0<l
      invu<invl = ℚExtra.posInv-reverse< 0<l 0<u l<u

      invl<invl : ℚExtra.posInv l 0<l ℚOrder.< ℚExtra.posInv l 0<l
      invl<invl =
        ℚOrder.isTrans< (ℚExtra.posInv l 0<l) q (ℚExtra.posInv l 0<l)
          invl<q
          (ℚOrder.isTrans< q (ℚExtra.posInv u 0<u) (ℚExtra.posInv l 0<l)
            q<1/u invu<invl)
  isDedekindRealInv₊ x 0<x .IsDedekindReal.located =
    λ p q p<q → located-inv p q p<q
    where
    lower-from-zero :
      (p : ℚ) →
      p ≡ ℚExtra.0ℚ →
      ∥ p ∈ invLower x ∥₁
    lower-from-zero p p≡0 =
      Prop.rec squash₁
        (λ (u , u∈Ux , 0<u) →
          ∣ inv-lower-witness x p
              (u , u∈Ux , 0<u ,
               subst (λ t → t ℚOrder.< ℚExtra.posInv u 0<u)
                 (sym p≡0)
                 (ℚExtra.posInv-positive {q = u} 0<u))
          ∣₁)
        (upperBound>0 x 0<x)

    upper-from-lower :
      (q : ℚ) →
      (0<q : ℚExtra.0ℚ ℚOrder.< q) →
      ℚExtra.posInv q 0<q ∈ lower x →
      ∥ q ∈ invUpper x ∥₁
    upper-from-lower q 0<q invq∈Lx =
      Prop.rec squash₁
        (λ (l , invq<l , l∈Lx) →
          let
            0<invq = ℚExtra.posInv-positive {q = q} 0<q
            0<l = ℚOrder.isTrans< ℚExtra.0ℚ (ℚExtra.posInv q 0<q) l 0<invq invq<l
            invl<invinvq = ℚExtra.posInv-reverse< 0<invq 0<l invq<l
            invinvoq≡q = ℚExtra.posInv-involutive q 0<q
            invl<q =
              subst (λ t → ℚExtra.posInv l 0<l ℚOrder.< t)
                invinvoq≡q
                invl<invinvq
          in
          ∣ inv-upper-witness x q 0<q (l , l∈Lx , 0<l , invl<q) ∣₁)
        (lower-rounded x (ℚExtra.posInv q 0<q) invq∈Lx)

    lower-from-upper :
      (p : ℚ) →
      (0<p : ℚExtra.0ℚ ℚOrder.< p) →
      ℚExtra.posInv p 0<p ∈ upper x →
      ∥ p ∈ invLower x ∥₁
    lower-from-upper p 0<p invp∈Ux =
      Prop.rec squash₁
        (λ (u , u<invp , u∈Ux) →
          let
            0≤x = >0→≥0 x 0<x
            0<u = ≥0+upper→>0 x 0≤x u u∈Ux
            invinvp>invu = ℚExtra.posInv-reverse< 0<u
              (ℚExtra.posInv-positive {q = p} 0<p)
              u<invp
            p<invu =
              subst (λ t → t ℚOrder.< ℚExtra.posInv u 0<u)
                (ℚExtra.posInv-involutive p 0<p)
                invinvp>invu
          in
          ∣ inv-lower-witness x p (u , u∈Ux , 0<u , p<invu) ∣₁)
        (upper-rounded x (ℚExtra.posInv p 0<p) invp∈Ux)

    located-positive :
      (p q : ℚ) →
      (0<p : ℚExtra.0ℚ ℚOrder.< p) →
      (0<q : ℚExtra.0ℚ ℚOrder.< q) →
      p ℚOrder.< q →
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
        (located x
          (ℚExtra.posInv q 0<q)
          (ℚExtra.posInv p 0<p)
          (ℚExtra.posInv-reverse< 0<p 0<q p<q))

    located-inv :
      (p q : ℚ) →
      p ℚOrder.< q →
      ∥ (p ∈ invLower x) ⊎ (q ∈ invUpper x) ∥₁
    located-inv-positive-q :
      (p q : ℚ) →
      (0<q : ℚExtra.0ℚ ℚOrder.< q) →
      p ℚOrder.< q →
      ∥ (p ∈ invLower x) ⊎ (q ∈ invUpper x) ∥₁
    located-inv-positive-q p q 0<q p<q with ℚExtra.0ℚ ℚOrder.≟ p
    ... | ℚOrder.lt 0<p = located-positive p q 0<p 0<q p<q
    ... | ℚOrder.eq 0≡p =
      Prop.rec squash₁
        (λ p∈L → ∣ Sum.inl p∈L ∣₁)
        (lower-from-zero p (sym 0≡p))
    ... | ℚOrder.gt p<0 =
      ∣ Sum.inl (inv-lower-negative x p p<0) ∣₁

    located-inv p q p<q with ℚExtra.0ℚ ℚOrder.≟ q
    ... | ℚOrder.lt 0<q = located-inv-positive-q p q 0<q p<q
    ... | ℚOrder.eq 0≡q =
      ∣ Sum.inl
          (inv-lower-negative x p
            (transport (λ i → p ℚOrder.< 0≡q (~ i)) p<q))
      ∣₁
    ... | ℚOrder.gt q<0 =
      ∣ Sum.inl (inv-lower-negative x p
          (ℚOrder.isTrans< p q ℚExtra.0ℚ p<q q<0))
      ∣₁

  inv₊ :
    (x : DedekindReal ℓ) →
    x >0 →
    DedekindReal ℓ
  inv₊ x 0<x .lower = invLower x
  inv₊ x 0<x .upper = invUpper x
  inv₊ x 0<x .isDedekindReal = isDedekindRealInv₊ x 0<x

  inv₊≥0 :
    (x : DedekindReal ℓ) →
    (0<x : x >0) →
    (inv₊ x 0<x) ≥0
  inv₊≥0 x 0<x q q<0 =
    inv-lower-negative x q (Lift.lower q<0)

  private
    mul-below-one :
      {a b u : ℚ} →
      a ℚOrder.< u →
      (0<u : ℚExtra.0ℚ ℚOrder.< u) →
      (0<b : ℚExtra.0ℚ ℚOrder.< b) →
      b ℚOrder.< ℚExtra.posInv u 0<u →
      a ℚ.· b ℚOrder.< ℚExtra.1ℚ
    mul-below-one {a = a} {b = b} {u = u} a<u 0<u 0<b b<1/u =
      ℚOrder.isTrans< (a ℚ.· b) (u ℚ.· b) ℚExtra.1ℚ
        (ℚOrder.<-·o a u b 0<b a<u)
        u*b<1
      where
      u*b<1 : u ℚ.· b ℚOrder.< ℚExtra.1ℚ
      u*b<1 =
        subst (λ t → u ℚ.· b ℚOrder.< t)
          (ℚExtra.posInv-right u 0<u)
          (ℚExtra.mul-left-positive-< {a = u} {b = b}
            {c = ℚExtra.posInv u 0<u}
            0<u
            b<1/u)

    one-below-mul :
      {l a b : ℚ} →
      (0<l : ℚExtra.0ℚ ℚOrder.< l) →
      l ℚOrder.< a →
      ℚExtra.posInv l 0<l ℚOrder.< b →
      ℚExtra.1ℚ ℚOrder.< a ℚ.· b
    one-below-mul {l = l} {a = a} {b = b} 0<l l<a 1/l<b =
      ℚOrder.isTrans< ℚExtra.1ℚ (a ℚ.· ℚExtra.posInv l 0<l) (a ℚ.· b)
        1<a/l
        a/l<ab
      where
      0<1/l : ℚExtra.0ℚ ℚOrder.< ℚExtra.posInv l 0<l
      0<1/l = ℚExtra.posInv-positive {q = l} 0<l

      0<a : ℚExtra.0ℚ ℚOrder.< a
      0<a = ℚOrder.isTrans< ℚExtra.0ℚ l a 0<l l<a

      1<a/l : ℚExtra.1ℚ ℚOrder.< a ℚ.· ℚExtra.posInv l 0<l
      1<a/l =
        subst (λ t → t ℚOrder.< a ℚ.· ℚExtra.posInv l 0<l)
          (ℚExtra.posInv-right l 0<l)
          (ℚOrder.<-·o l a (ℚExtra.posInv l 0<l) 0<1/l l<a)

      a/l<ab : a ℚ.· ℚExtra.posInv l 0<l ℚOrder.< a ℚ.· b
      a/l<ab =
        ℚExtra.mul-left-positive-< {a = a}
          {b = ℚExtra.posInv l 0<l}
          {c = b}
          0<a
          1/l<b

  ·-rInv₊ :
    (x : DedekindReal ℓ) →
    (0<x : x >0) →
    x * inv₊ x 0<x ≡ 1𝔻
  ·-rInv₊ x 0<x =
    ≤-antisym (x * inv) 1𝔻
      (¬>→≤ (x * inv) 1𝔻 not-1<product)
      (¬>→≤ 1𝔻 (x * inv) not-product<1)
    where
    inv : DedekindReal ℓ
    inv = inv₊ x 0<x

    0≤x : x ≥0
    0≤x = >0→≥0 x 0<x

    0≤inv : inv ≥0
    0≤inv = inv₊≥0 x 0<x

    product≡nn : x * inv ≡ nnMul x inv 0≤x 0≤inv
    product≡nn = *-of-≥0 x inv 0≤x 0≤inv

    not-1<product : ¬ 1𝔻 < x * inv
    not-1<product =
      Prop.rec Empty.isProp⊥
        (λ (q , 1<q , q∈Lproduct) →
          let
            q∈Lnn : q ∈ nnMulLower x inv
            q∈Lnn = subst (λ z → q ∈ lower z) product≡nn q∈Lproduct
          in
          Prop.rec Empty.isProp⊥
            (λ where
              (Sum.inl q<0) →
                ℚOrder.isAsym< ℚExtra.0ℚ q
                  (ℚOrder.isTrans< ℚExtra.0ℚ ℚExtra.1ℚ q
                    ℚExtra.0<1
                    (Lift.lower 1<q))
                  q<0
              (Sum.inr (a , b , a∈Lx , b∈Linv , 0<a , 0<b , q<ab)) →
                Prop.rec Empty.isProp⊥
                  (λ where
                    (Sum.inl b<0) →
                      ℚOrder.isAsym< ℚExtra.0ℚ b 0<b b<0
                    (Sum.inr (u , u∈Ux , 0<u , b<1/u)) →
                      let
                        a<u : a ℚOrder.< u
                        a<u = lower<upper x a u a∈Lx u∈Ux

                        ab<1 : a ℚ.· b ℚOrder.< ℚExtra.1ℚ
                        ab<1 = mul-below-one a<u 0<u 0<b b<1/u

                        1<1 : ℚExtra.1ℚ ℚOrder.< ℚExtra.1ℚ
                        1<1 =
                          ℚOrder.isTrans< ℚExtra.1ℚ q ℚExtra.1ℚ
                            (Lift.lower 1<q)
                            (ℚOrder.isTrans< q (a ℚ.· b) ℚExtra.1ℚ q<ab ab<1)
                      in
                      ℚOrder.isIrrefl< ℚExtra.1ℚ 1<1)
                  b∈Linv)
            q∈Lnn)

    not-product<1 : ¬ (x * inv) < 1𝔻
    not-product<1 =
      Prop.rec Empty.isProp⊥
        (λ (q , q∈Uproduct , q<1) →
          let
            q∈Unn : q ∈ nnMulUpper x inv
            q∈Unn = subst (λ z → q ∈ upper z) product≡nn q∈Uproduct
          in
          Prop.rec Empty.isProp⊥
            (λ (a , b , a∈Ux , b∈Uinv , 0<a , 0<b , ab<q) →
              Prop.rec Empty.isProp⊥
                (λ (l , l∈Lx , 0<l , 1/l<b) →
                  let
                    l<a : l ℚOrder.< a
                    l<a = lower<upper x l a l∈Lx a∈Ux

                    1<ab : ℚExtra.1ℚ ℚOrder.< a ℚ.· b
                    1<ab = one-below-mul 0<l l<a 1/l<b

                    1<1 : ℚExtra.1ℚ ℚOrder.< ℚExtra.1ℚ
                    1<1 =
                      ℚOrder.isTrans< ℚExtra.1ℚ q ℚExtra.1ℚ
                        (ℚOrder.isTrans< ℚExtra.1ℚ (a ℚ.· b) q 1<ab ab<q)
                        (Lift.lower q<1)
                  in
                  ℚOrder.isIrrefl< ℚExtra.1ℚ 1<1)
                (b∈Uinv .snd))
            (q∈Unn .snd))

  -Reverse<0 :
    (x : DedekindReal ℓ) →
    x < 0𝔻 →
    (- x) >0
  -Reverse<0 x x<0 =
    subst (λ z → z < (- x))
      neg-0𝔻
      (neg-<-reverse x 0𝔻 x<0)

  HasInv# : DedekindReal ℓ → Type (ℓ-suc ℓ)
  HasInv# x = Σ[ y ∈ DedekindReal ℓ ] x * y ≡ 1𝔻

  inv# :
    (x : DedekindReal ℓ) →
    x # 0𝔻 →
    HasInv# x
  inv# x (Sum.inr 0<x) =
    inv₊ x 0<x , ·-rInv₊ x 0<x
  inv# x (Sum.inl x<0) =
    - nx⁻¹ ,
    *-negR x nx⁻¹ ∙
    sym (*-negL x nx⁻¹) ∙
    ·-rInv₊ (- x) 0<-x
    where
    0<-x : (- x) >0
    0<-x = -Reverse<0 x x<0

    nx⁻¹ : DedekindReal ℓ
    nx⁻¹ = inv₊ (- x) 0<-x
