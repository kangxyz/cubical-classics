{-

Algebraic laws for nonnegative Dedekind-real multiplication

Order antisymmetry reduces equality of cuts to lower inclusions.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals.Arithmetic.NonNegative where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Rationals using (ℚ)
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∣_∣₁ ; squash₁)

open import Constructive.DedekindReals
open import Constructive.DedekindReals.Arithmetic.Base
import Constructive.Rationals as ℚExtra


module NonNegativeProperties {ℓ : Level} where
  open Order {ℓ}
  open Addition {ℓ}
  open NonNegativeMultiplication {ℓ}

  nnMul-lower-positive-product :
    (x y : DedekindReal ℓ) →
    (a b : ℚ) →
    a ∈ lower x →
    b ∈ lower y →
    ℚExtra.0ℚ ℚOrder.< a →
    ℚExtra.0ℚ ℚOrder.< b →
    (a ℚ.· b) ∈ nnMulLower x y
  nnMul-lower-positive-product x y a b a∈Lx b∈Ly 0<a 0<b =
    Prop.rec squash₁ step (lower-rounded x a a∈Lx)
    where
    step :
      Σ[ a' ∈ ℚ ] (a ℚOrder.< a') × (a' ∈ lower x) →
      (a ℚ.· b) ∈ nnMulLower x y
    step (a' , a<a' , a'∈Lx) =
      ∣ Sum.inr
          (a' , b
          , a'∈Lx
          , b∈Ly
          , ℚOrder.isTrans< ℚExtra.0ℚ a a' 0<a a<a'
          , 0<b
          , ℚOrder.<-·o a a' b 0<b a<a')
      ∣₁

  nnMul-assoc-≤LR :
    (x y z : DedekindReal ℓ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (0≤z : z ≥0) →
    nnMul x (nnMul y z 0≤y 0≤z)
      0≤x
      (nnMul-Pres≥0 y z 0≤y 0≤z)
    ≤
    nnMul (nnMul x y 0≤x 0≤y) z
      (nnMul-Pres≥0 x y 0≤x 0≤y)
      0≤z
  nnMul-assoc-≤LR x y z 0≤x 0≤y 0≤z q =
    Prop.rec squash₁ outer
    where
    outer :
      (q ℚOrder.< ℚExtra.0ℚ) ⊎
      ProductLowerWitness x (nnMul y z 0≤y 0≤z) q →
      q ∈ nnMulLower (nnMul x y 0≤x 0≤y) z
    outer (Sum.inl q<0) =
      ∣ Sum.inl q<0 ∣₁
    outer (Sum.inr (a , b , a∈Lx , b∈Lyz , 0<a , 0<b , q<ab)) =
      Prop.rec squash₁ inner b∈Lyz
      where
      inner :
        (b ℚOrder.< ℚExtra.0ℚ) ⊎ ProductLowerWitness y z b →
        q ∈ nnMulLower (nnMul x y 0≤x 0≤y) z
      inner (Sum.inl b<0) =
        Empty.rec (ℚOrder.isAsym< ℚExtra.0ℚ b 0<b b<0)
      inner (Sum.inr (c , d , c∈Ly , d∈Lz , 0<c , 0<d , b<cd)) =
        ∣ Sum.inr
            (a ℚ.· c , d
            , nnMul-lower-positive-product x y a c a∈Lx c∈Ly 0<a 0<c
            , d∈Lz
            , ℚExtra.mul-positive {a = a} {b = c} 0<a 0<c
            , 0<d
            , q<ac*d)
        ∣₁
        where
        ab<a*cd : a ℚ.· b ℚOrder.< a ℚ.· (c ℚ.· d)
        ab<a*cd =
          ℚExtra.mul-left-positive-<
            {a = a} {b = b} {c = c ℚ.· d}
            0<a b<cd

        q<a*cd : q ℚOrder.< a ℚ.· (c ℚ.· d)
        q<a*cd =
          ℚOrder.isTrans< q (a ℚ.· b) (a ℚ.· (c ℚ.· d)) q<ab ab<a*cd

        q<ac*d : q ℚOrder.< (a ℚ.· c) ℚ.· d
        q<ac*d =
          subst (λ v → q ℚOrder.< v) (ℚ.·Assoc a c d) q<a*cd

  nnMul-assoc-≤RL :
    (x y z : DedekindReal ℓ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (0≤z : z ≥0) →
    nnMul (nnMul x y 0≤x 0≤y) z
      (nnMul-Pres≥0 x y 0≤x 0≤y)
      0≤z
    ≤
    nnMul x (nnMul y z 0≤y 0≤z)
      0≤x
      (nnMul-Pres≥0 y z 0≤y 0≤z)
  nnMul-assoc-≤RL x y z 0≤x 0≤y 0≤z q =
    Prop.rec squash₁ outer
    where
    outer :
      (q ℚOrder.< ℚExtra.0ℚ) ⊎
      ProductLowerWitness (nnMul x y 0≤x 0≤y) z q →
      q ∈ nnMulLower x (nnMul y z 0≤y 0≤z)
    outer (Sum.inl q<0) =
      ∣ Sum.inl q<0 ∣₁
    outer (Sum.inr (A , d , A∈Lxy , d∈Lz , 0<A , 0<d , q<Ad)) =
      Prop.rec squash₁ inner A∈Lxy
      where
      inner :
        (A ℚOrder.< ℚExtra.0ℚ) ⊎ ProductLowerWitness x y A →
        q ∈ nnMulLower x (nnMul y z 0≤y 0≤z)
      inner (Sum.inl A<0) =
        Empty.rec (ℚOrder.isAsym< ℚExtra.0ℚ A 0<A A<0)
      inner (Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , A<ab)) =
        ∣ Sum.inr
            (a , b ℚ.· d
            , a∈Lx
            , nnMul-lower-positive-product y z b d b∈Ly d∈Lz 0<b 0<d
            , 0<a
            , ℚExtra.mul-positive {a = b} {b = d} 0<b 0<d
            , q<a*bd)
        ∣₁
        where
        Ad<ab*d : A ℚ.· d ℚOrder.< (a ℚ.· b) ℚ.· d
        Ad<ab*d =
          ℚOrder.<-·o A (a ℚ.· b) d 0<d A<ab

        q<ab*d : q ℚOrder.< (a ℚ.· b) ℚ.· d
        q<ab*d =
          ℚOrder.isTrans< q (A ℚ.· d) ((a ℚ.· b) ℚ.· d) q<Ad Ad<ab*d

        q<a*bd : q ℚOrder.< a ℚ.· (b ℚ.· d)
        q<a*bd =
          subst (λ v → q ℚOrder.< v) (sym (ℚ.·Assoc a b d)) q<ab*d

  nnMul-assoc :
    (x y z : DedekindReal ℓ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (0≤z : z ≥0) →
    nnMul x (nnMul y z 0≤y 0≤z)
      0≤x
      (nnMul-Pres≥0 y z 0≤y 0≤z)
    ≡
    nnMul (nnMul x y 0≤x 0≤y) z
      (nnMul-Pres≥0 x y 0≤x 0≤y)
      0≤z
  nnMul-assoc x y z 0≤x 0≤y 0≤z =
    ≤-antisym
      (nnMul x (nnMul y z 0≤y 0≤z)
        0≤x
        (nnMul-Pres≥0 y z 0≤y 0≤z))
      (nnMul (nnMul x y 0≤x 0≤y) z
        (nnMul-Pres≥0 x y 0≤x 0≤y)
        0≤z)
      (nnMul-assoc-≤LR x y z 0≤x 0≤y 0≤z)
      (nnMul-assoc-≤RL x y z 0≤x 0≤y 0≤z)

  nnMul-distribL-≤LR :
    (x y z : DedekindReal ℓ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (0≤z : z ≥0) →
    nnMul x (y + z)
      0≤x
      (+-Pres≥0 y z 0≤y 0≤z)
    ≤
    (nnMul x y 0≤x 0≤y) + (nnMul x z 0≤x 0≤z)
  nnMul-distribL-≤LR x y z 0≤x 0≤y 0≤z q =
    Prop.rec squash₁ outer
    where
    xy : DedekindReal ℓ
    xy = nnMul x y 0≤x 0≤y

    xz : DedekindReal ℓ
    xz = nnMul x z 0≤x 0≤z

    0≤xy : xy ≥0
    0≤xy = nnMul-Pres≥0 x y 0≤x 0≤y

    0≤xz : xz ≥0
    0≤xz = nnMul-Pres≥0 x z 0≤x 0≤z

    target : ℚ → Type ℓ
    target t = t ∈ lower (xy + xz)

    lower-add :
      (r s : ℚ) →
      r ∈ nnMulLower x y →
      s ∈ nnMulLower x z →
      q ℚOrder.< r ℚ.+ s →
      target q
    lower-add r s r∈Lxy s∈Lxz q<r+s =
      ∣ r , s , r∈Lxy , s∈Lxz , q<r+s ∣₁

    q<ac+ad :
      (a b c d : ℚ) →
      ℚExtra.0ℚ ℚOrder.< a →
      q ℚOrder.< a ℚ.· b →
      b ℚOrder.< c ℚ.+ d →
      q ℚOrder.< (a ℚ.· c) ℚ.+ (a ℚ.· d)
    q<ac+ad a b c d 0<a q<ab b<c+d =
      subst (λ v → q ℚOrder.< v)
        (ℚExtra.mul-distrib-left a c d)
        q<a[c+d]
      where
      ab<a[c+d] : a ℚ.· b ℚOrder.< a ℚ.· (c ℚ.+ d)
      ab<a[c+d] =
        ℚExtra.mul-left-positive-<
          {a = a} {b = b} {c = c ℚ.+ d}
          0<a b<c+d

      q<a[c+d] : q ℚOrder.< a ℚ.· (c ℚ.+ d)
      q<a[c+d] =
        ℚOrder.isTrans< q (a ℚ.· b) (a ℚ.· (c ℚ.+ d))
          q<ab ab<a[c+d]

    pos-pos :
      (a b c d : ℚ) →
      a ∈ lower x →
      c ∈ lower y →
      d ∈ lower z →
      ℚExtra.0ℚ ℚOrder.< a →
      ℚExtra.0ℚ ℚOrder.< c →
      ℚExtra.0ℚ ℚOrder.< d →
      q ℚOrder.< a ℚ.· b →
      b ℚOrder.< c ℚ.+ d →
      target q
    pos-pos a b c d a∈Lx c∈Ly d∈Lz 0<a 0<c 0<d q<ab b<c+d =
      lower-add
        (a ℚ.· c)
        (a ℚ.· d)
        (nnMul-lower-positive-product x y a c a∈Lx c∈Ly 0<a 0<c)
        (nnMul-lower-positive-product x z a d a∈Lx d∈Lz 0<a 0<d)
        (q<ac+ad a b c d 0<a q<ab b<c+d)

    nonpos-pos :
      (a b c d : ℚ) →
      a ∈ lower x →
      d ∈ lower z →
      ℚExtra.0ℚ ℚOrder.< a →
      c ℚOrder.≤ ℚExtra.0ℚ →
      ℚExtra.0ℚ ℚOrder.< d →
      q ℚOrder.< a ℚ.· b →
      b ℚOrder.< c ℚ.+ d →
      target q
    nonpos-pos a b c d a∈Lx d∈Lz 0<a c≤0 0<d q<ab b<c+d =
      Prop.rec squash₁ step
        (ℚExtra.dense
          {p = q}
          {q = (a ℚ.· c) ℚ.+ (a ℚ.· d)}
          (q<ac+ad a b c d 0<a q<ab b<c+d))
      where
      ad : ℚ
      ad = a ℚ.· d

      ac : ℚ
      ac = a ℚ.· c

      ac≤0 : ac ℚOrder.≤ ℚExtra.0ℚ
      ac≤0 = ℚExtra.mul-nonpositive-right {a = a} {b = c} 0<a c≤0

      step :
        Σ[ m ∈ ℚ ]
          (q ℚOrder.< m) ×
          (m ℚOrder.< ac ℚ.+ ad) →
        target q
      step (m , q<m , m<ac+ad) =
        lower-add
          (m ℚ.- ad)
          ad
          (nnMul-lower-from-negative x y (m ℚ.- ad) m-ad<0)
          (nnMul-lower-positive-product x z a d a∈Lx d∈Lz 0<a 0<d)
          q<split
        where
        m-ad<ac : m ℚ.- ad ℚOrder.< ac
        m-ad<ac =
          ℚExtra.<+→diff< m ac ad m<ac+ad

        m-ad<0 : m ℚ.- ad ℚOrder.< ℚExtra.0ℚ
        m-ad<0 =
          ℚExtra.<≤-trans {p = m ℚ.- ad} {q = ac} {r = ℚExtra.0ℚ}
            m-ad<ac ac≤0

        q<split : q ℚOrder.< (m ℚ.- ad) ℚ.+ ad
        q<split =
          subst (λ v → q ℚOrder.< v)
            (sym (ℚExtra.[p-q]+q≡p m ad))
            q<m

    pos-nonpos :
      (a b c d : ℚ) →
      a ∈ lower x →
      c ∈ lower y →
      ℚExtra.0ℚ ℚOrder.< a →
      ℚExtra.0ℚ ℚOrder.< c →
      d ℚOrder.≤ ℚExtra.0ℚ →
      q ℚOrder.< a ℚ.· b →
      b ℚOrder.< c ℚ.+ d →
      target q
    pos-nonpos a b c d a∈Lx c∈Ly 0<a 0<c d≤0 q<ab b<c+d =
      Prop.rec squash₁ step
        (ℚExtra.dense
          {p = q}
          {q = (a ℚ.· c) ℚ.+ (a ℚ.· d)}
          (q<ac+ad a b c d 0<a q<ab b<c+d))
      where
      ac : ℚ
      ac = a ℚ.· c

      ad : ℚ
      ad = a ℚ.· d

      ad≤0 : ad ℚOrder.≤ ℚExtra.0ℚ
      ad≤0 = ℚExtra.mul-nonpositive-right {a = a} {b = d} 0<a d≤0

      step :
        Σ[ m ∈ ℚ ]
          (q ℚOrder.< m) ×
          (m ℚOrder.< ac ℚ.+ ad) →
        target q
      step (m , q<m , m<ac+ad) =
        lower-add
          ac
          (m ℚ.- ac)
          (nnMul-lower-positive-product x y a c a∈Lx c∈Ly 0<a 0<c)
          (nnMul-lower-from-negative x z (m ℚ.- ac) m-ac<0)
          q<split
        where
        m-ac<ad : m ℚ.- ac ℚOrder.< ad
        m-ac<ad =
          ℚExtra.<+→diff< m ad ac
            (subst (λ v → m ℚOrder.< v) (ℚ.+Comm ac ad) m<ac+ad)

        m-ac<0 : m ℚ.- ac ℚOrder.< ℚExtra.0ℚ
        m-ac<0 =
          ℚExtra.<≤-trans {p = m ℚ.- ac} {q = ad} {r = ℚExtra.0ℚ}
            m-ac<ad ad≤0

        q<split : q ℚOrder.< ac ℚ.+ (m ℚ.- ac)
        q<split =
          subst (λ v → q ℚOrder.< v)
            (sym (ℚExtra.left-diff+ ac m))
            q<m

    nonpos-nonpos-absurd :
      (b c d : ℚ) →
      ℚExtra.0ℚ ℚOrder.< b →
      b ℚOrder.< c ℚ.+ d →
      c ℚOrder.≤ ℚExtra.0ℚ →
      d ℚOrder.≤ ℚExtra.0ℚ →
      target q
    nonpos-nonpos-absurd b c d 0<b b<c+d c≤0 d≤0 =
      Empty.rec (ℚOrder.isAsym< ℚExtra.0ℚ b 0<b b<0)
      where
      c+d≤0+0 : c ℚ.+ d ℚOrder.≤ ℚExtra.0ℚ ℚ.+ ℚExtra.0ℚ
      c+d≤0+0 =
        ℚOrder.≤Monotone+
          c ℚExtra.0ℚ
          d ℚExtra.0ℚ
          c≤0 d≤0

      c+d≤0 : c ℚ.+ d ℚOrder.≤ ℚExtra.0ℚ
      c+d≤0 =
        subst (λ v → c ℚ.+ d ℚOrder.≤ v)
          (ℚ.+IdR ℚExtra.0ℚ)
          c+d≤0+0

      b<0 : b ℚOrder.< ℚExtra.0ℚ
      b<0 =
        ℚExtra.<≤-trans {p = b} {q = c ℚ.+ d} {r = ℚExtra.0ℚ}
          b<c+d c+d≤0

    split-cd :
      (a b c d : ℚ) →
      a ∈ lower x →
      c ∈ lower y →
      d ∈ lower z →
      ℚExtra.0ℚ ℚOrder.< a →
      ℚExtra.0ℚ ℚOrder.< b →
      q ℚOrder.< a ℚ.· b →
      b ℚOrder.< c ℚ.+ d →
      target q
    split-cd a b c d a∈Lx c∈Ly d∈Lz 0<a 0<b q<ab b<c+d
      with ℚExtra.0ℚ ℚOrder.≟ c | ℚExtra.0ℚ ℚOrder.≟ d
    ... | ℚOrder.lt 0<c | ℚOrder.lt 0<d =
      pos-pos a b c d a∈Lx c∈Ly d∈Lz 0<a 0<c 0<d q<ab b<c+d
    ... | ℚOrder.lt 0<c | ℚOrder.eq 0≡d =
      pos-nonpos a b c d a∈Lx c∈Ly 0<a 0<c
        (ℚOrder.≡Weaken≤ d ℚExtra.0ℚ (sym 0≡d))
        q<ab b<c+d
    ... | ℚOrder.lt 0<c | ℚOrder.gt d<0 =
      pos-nonpos a b c d a∈Lx c∈Ly 0<a 0<c
        (ℚExtra.<→≤ {p = d} {q = ℚExtra.0ℚ} d<0)
        q<ab b<c+d
    ... | ℚOrder.eq 0≡c | ℚOrder.lt 0<d =
      nonpos-pos a b c d a∈Lx d∈Lz 0<a
        (ℚOrder.≡Weaken≤ c ℚExtra.0ℚ (sym 0≡c))
        0<d q<ab b<c+d
    ... | ℚOrder.eq 0≡c | ℚOrder.eq 0≡d =
      nonpos-nonpos-absurd b c d 0<b b<c+d
        (ℚOrder.≡Weaken≤ c ℚExtra.0ℚ (sym 0≡c))
        (ℚOrder.≡Weaken≤ d ℚExtra.0ℚ (sym 0≡d))
    ... | ℚOrder.eq 0≡c | ℚOrder.gt d<0 =
      nonpos-nonpos-absurd b c d 0<b b<c+d
        (ℚOrder.≡Weaken≤ c ℚExtra.0ℚ (sym 0≡c))
        (ℚExtra.<→≤ {p = d} {q = ℚExtra.0ℚ} d<0)
    ... | ℚOrder.gt c<0 | ℚOrder.lt 0<d =
      nonpos-pos a b c d a∈Lx d∈Lz 0<a
        (ℚExtra.<→≤ {p = c} {q = ℚExtra.0ℚ} c<0)
        0<d q<ab b<c+d
    ... | ℚOrder.gt c<0 | ℚOrder.eq 0≡d =
      nonpos-nonpos-absurd b c d 0<b b<c+d
        (ℚExtra.<→≤ {p = c} {q = ℚExtra.0ℚ} c<0)
        (ℚOrder.≡Weaken≤ d ℚExtra.0ℚ (sym 0≡d))
    ... | ℚOrder.gt c<0 | ℚOrder.gt d<0 =
      nonpos-nonpos-absurd b c d 0<b b<c+d
        (ℚExtra.<→≤ {p = c} {q = ℚExtra.0ℚ} c<0)
        (ℚExtra.<→≤ {p = d} {q = ℚExtra.0ℚ} d<0)

    outer :
      (q ℚOrder.< ℚExtra.0ℚ) ⊎ ProductLowerWitness x (y + z) q →
      target q
    outer (Sum.inl q<0) =
      +-Pres≥0 xy xz 0≤xy 0≤xz q (lift q<0)
    outer (Sum.inr (a , b , a∈Lx , b∈Ly+z , 0<a , 0<b , q<ab)) =
      Prop.rec squash₁
        (λ (c , d , c∈Ly , d∈Lz , b<c+d) →
          split-cd a b c d a∈Lx c∈Ly d∈Lz 0<a 0<b q<ab b<c+d)
        b∈Ly+z

  nnMul-distribL-≤RL :
    (x y z : DedekindReal ℓ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (0≤z : z ≥0) →
    (nnMul x y 0≤x 0≤y) + (nnMul x z 0≤x 0≤z)
    ≤
    nnMul x (y + z)
      0≤x
      (+-Pres≥0 y z 0≤y 0≤z)
  nnMul-distribL-≤RL x y z 0≤x 0≤y 0≤z q =
    Prop.rec squash₁ outer
    where
    yz : DedekindReal ℓ
    yz = y + z

    0≤yz : yz ≥0
    0≤yz = +-Pres≥0 y z 0≤y 0≤z

    xy : DedekindReal ℓ
    xy = nnMul x y 0≤x 0≤y

    xz : DedekindReal ℓ
    xz = nnMul x z 0≤x 0≤z

    x-yz : DedekindReal ℓ
    x-yz = nnMul x yz 0≤x 0≤yz

    y≤yz : y ≤ yz
    y≤yz =
      ≤-trans y (y + 0𝔻) yz
        (≡→≤ (sym (+-idR y)))
        (+-monoL-≤ 0𝔻 z y 0≤z)

    z≤yz : z ≤ yz
    z≤yz =
      ≤-trans z (0𝔻 + z) yz
        (≡→≤ (sym (+-idL z)))
        (+-monoR-≤ 0𝔻 y z 0≤y)

    xy≤x-yz : xy ≤ x-yz
    xy≤x-yz =
      nnMul-monoR-≤ x y yz 0≤x 0≤y 0≤yz y≤yz

    xz≤x-yz : xz ≤ x-yz
    xz≤x-yz =
      nnMul-monoR-≤ x z yz 0≤x 0≤z 0≤yz z≤yz

    lower-from-xy :
      (r s : ℚ) →
      r ℚOrder.< ℚExtra.0ℚ →
      s ∈ nnMulLower x z →
      q ℚOrder.< r ℚ.+ s →
      q ∈ nnMulLower x yz
    lower-from-xy r s r<0 s∈Lxz q<r+s =
      xz≤x-yz q q∈Lxz
      where
      r+s<s : r ℚ.+ s ℚOrder.< s
      r+s<s =
        subst (λ v → r ℚ.+ s ℚOrder.< v)
          (ℚ.+IdL s)
          (ℚOrder.<-+o r ℚExtra.0ℚ s r<0)

      q<s : q ℚOrder.< s
      q<s = ℚOrder.isTrans< q (r ℚ.+ s) s q<r+s r+s<s

      q∈Lxz : q ∈ lower xz
      q∈Lxz = lower-closed xz q s q<s s∈Lxz

    lower-from-xz :
      (r s : ℚ) →
      r ∈ nnMulLower x y →
      s ℚOrder.< ℚExtra.0ℚ →
      q ℚOrder.< r ℚ.+ s →
      q ∈ nnMulLower x yz
    lower-from-xz r s r∈Lxy s<0 q<r+s =
      xy≤x-yz q q∈Lxy
      where
      r+s<r : r ℚ.+ s ℚOrder.< r
      r+s<r =
        subst (λ v → r ℚ.+ s ℚOrder.< v)
          (ℚ.+IdR r)
          (ℚOrder.<-o+ s ℚExtra.0ℚ r s<0)

      q<r : q ℚOrder.< r
      q<r = ℚOrder.isTrans< q (r ℚ.+ s) r q<r+s r+s<r

      q∈Lxy : q ∈ lower xy
      q∈Lxy = lower-closed xy q r q<r r∈Lxy

    sum-lower :
      (b d : ℚ) →
      b ∈ lower y →
      d ∈ lower z →
      (b ℚ.+ d) ∈ lower yz
    sum-lower b d b∈Ly d∈Lz =
      Prop.rec squash₁ step (lower-rounded y b b∈Ly)
      where
      step :
        Σ[ b' ∈ ℚ ] (b ℚOrder.< b') × (b' ∈ lower y) →
        (b ℚ.+ d) ∈ lower yz
      step (b' , b<b' , b'∈Ly) =
        ∣ b' , d
        , b'∈Ly
        , d∈Lz
        , ℚOrder.<-+o b b' d b<b'
        ∣₁

    both-positive :
      (r s a b c d : ℚ) →
      a ∈ lower x →
      b ∈ lower y →
      c ∈ lower x →
      d ∈ lower z →
      ℚExtra.0ℚ ℚOrder.< a →
      ℚExtra.0ℚ ℚOrder.< b →
      ℚExtra.0ℚ ℚOrder.< c →
      ℚExtra.0ℚ ℚOrder.< d →
      r ℚOrder.< a ℚ.· b →
      s ℚOrder.< c ℚ.· d →
      q ℚOrder.< r ℚ.+ s →
      q ∈ nnMulLower x yz
    both-positive r s a b c d a∈Lx b∈Ly c∈Lx d∈Lz
      0<a 0<b 0<c 0<d r<ab s<cd q<r+s
      with ℚExtra.≤-total a c
    ... | Sum.inl a≤c =
      ∣ Sum.inr
          (c , b ℚ.+ d
          , c∈Lx
          , sum-lower b d b∈Ly d∈Lz
          , 0<c
          , ℚExtra.positive-sum {p = b} {q = d} 0<b 0<d
          , q<c[b+d])
      ∣₁
      where
      r+s<ab+cd : r ℚ.+ s ℚOrder.< (a ℚ.· b) ℚ.+ (c ℚ.· d)
      r+s<ab+cd =
        ℚOrder.<Monotone+
          r (a ℚ.· b)
          s (c ℚ.· d)
          r<ab s<cd

      q<ab+cd : q ℚOrder.< (a ℚ.· b) ℚ.+ (c ℚ.· d)
      q<ab+cd =
        ℚOrder.isTrans< q (r ℚ.+ s) ((a ℚ.· b) ℚ.+ (c ℚ.· d))
          q<r+s r+s<ab+cd

      ab≤cb : a ℚ.· b ℚOrder.≤ c ℚ.· b
      ab≤cb =
        ℚOrder.≤-·o a c b (ℚExtra.<→≤ {p = ℚExtra.0ℚ} {q = b} 0<b) a≤c

      ab+cd≤cb+cd :
        (a ℚ.· b) ℚ.+ (c ℚ.· d) ℚOrder.≤
        (c ℚ.· b) ℚ.+ (c ℚ.· d)
      ab+cd≤cb+cd =
        ℚOrder.≤Monotone+
          (a ℚ.· b) (c ℚ.· b)
          (c ℚ.· d) (c ℚ.· d)
          ab≤cb
          (ℚExtra.≤-refl (c ℚ.· d))

      q<cb+cd : q ℚOrder.< (c ℚ.· b) ℚ.+ (c ℚ.· d)
      q<cb+cd =
        ℚExtra.<≤-trans
          {p = q}
          {q = (a ℚ.· b) ℚ.+ (c ℚ.· d)}
          {r = (c ℚ.· b) ℚ.+ (c ℚ.· d)}
          q<ab+cd
          ab+cd≤cb+cd

      q<c[b+d] : q ℚOrder.< c ℚ.· (b ℚ.+ d)
      q<c[b+d] =
        subst (λ v → q ℚOrder.< v)
          (sym (ℚExtra.mul-distrib-left c b d))
          q<cb+cd
    ... | Sum.inr c≤a =
      ∣ Sum.inr
          (a , b ℚ.+ d
          , a∈Lx
          , sum-lower b d b∈Ly d∈Lz
          , 0<a
          , ℚExtra.positive-sum {p = b} {q = d} 0<b 0<d
          , q<a[b+d])
      ∣₁
      where
      r+s<ab+cd : r ℚ.+ s ℚOrder.< (a ℚ.· b) ℚ.+ (c ℚ.· d)
      r+s<ab+cd =
        ℚOrder.<Monotone+
          r (a ℚ.· b)
          s (c ℚ.· d)
          r<ab s<cd

      q<ab+cd : q ℚOrder.< (a ℚ.· b) ℚ.+ (c ℚ.· d)
      q<ab+cd =
        ℚOrder.isTrans< q (r ℚ.+ s) ((a ℚ.· b) ℚ.+ (c ℚ.· d))
          q<r+s r+s<ab+cd

      cd≤ad : c ℚ.· d ℚOrder.≤ a ℚ.· d
      cd≤ad =
        ℚOrder.≤-·o c a d (ℚExtra.<→≤ {p = ℚExtra.0ℚ} {q = d} 0<d) c≤a

      ab+cd≤ab+ad :
        (a ℚ.· b) ℚ.+ (c ℚ.· d) ℚOrder.≤
        (a ℚ.· b) ℚ.+ (a ℚ.· d)
      ab+cd≤ab+ad =
        ℚOrder.≤Monotone+
          (a ℚ.· b) (a ℚ.· b)
          (c ℚ.· d) (a ℚ.· d)
          (ℚExtra.≤-refl (a ℚ.· b))
          cd≤ad

      q<ab+ad : q ℚOrder.< (a ℚ.· b) ℚ.+ (a ℚ.· d)
      q<ab+ad =
        ℚExtra.<≤-trans
          {p = q}
          {q = (a ℚ.· b) ℚ.+ (c ℚ.· d)}
          {r = (a ℚ.· b) ℚ.+ (a ℚ.· d)}
          q<ab+cd
          ab+cd≤ab+ad

      q<a[b+d] : q ℚOrder.< a ℚ.· (b ℚ.+ d)
      q<a[b+d] =
        subst (λ v → q ℚOrder.< v)
          (sym (ℚExtra.mul-distrib-left a b d))
          q<ab+ad

    split-products :
      (r s : ℚ) →
      r ∈ nnMulLower x y →
      s ∈ nnMulLower x z →
      q ℚOrder.< r ℚ.+ s →
      q ∈ nnMulLower x yz
    split-products r s r∈Lxy s∈Lxz q<r+s =
      Prop.rec (isProp∈ (nnMulLower x yz) q) left-case r∈Lxy
      where
      left-case :
        (r ℚOrder.< ℚExtra.0ℚ) ⊎ ProductLowerWitness x y r →
        q ∈ nnMulLower x yz
      left-case (Sum.inl r<0) =
        lower-from-xy r s r<0 s∈Lxz q<r+s
      left-case (Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , r<ab)) =
        Prop.rec (isProp∈ (nnMulLower x yz) q) right-case s∈Lxz
        where
        right-case :
          (s ℚOrder.< ℚExtra.0ℚ) ⊎ ProductLowerWitness x z s →
          q ∈ nnMulLower x yz
        right-case (Sum.inl s<0) =
          lower-from-xz r s
            (∣ Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , r<ab) ∣₁)
            s<0
            q<r+s
        right-case (Sum.inr (c , d , c∈Lx , d∈Lz , 0<c , 0<d , s<cd)) =
          both-positive r s a b c d
            a∈Lx b∈Ly c∈Lx d∈Lz
            0<a 0<b 0<c 0<d
            r<ab s<cd q<r+s

    outer :
      Σ[ r ∈ ℚ ] Σ[ s ∈ ℚ ]
        (r ∈ lower xy) ×
        (s ∈ lower xz) ×
        (q ℚOrder.< r ℚ.+ s) →
      q ∈ nnMulLower x yz
    outer (r , s , r∈Lxy , s∈Lxz , q<r+s) =
      split-products r s r∈Lxy s∈Lxz q<r+s

  nnMul-distribL :
    (x y z : DedekindReal ℓ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (0≤z : z ≥0) →
    nnMul x (y + z)
      0≤x
      (+-Pres≥0 y z 0≤y 0≤z)
    ≡
    (nnMul x y 0≤x 0≤y) + (nnMul x z 0≤x 0≤z)
  nnMul-distribL x y z 0≤x 0≤y 0≤z =
    ≤-antisym
      (nnMul x (y + z)
        0≤x
        (+-Pres≥0 y z 0≤y 0≤z))
      ((nnMul x y 0≤x 0≤y) + (nnMul x z 0≤x 0≤z))
      (nnMul-distribL-≤LR x y z 0≤x 0≤y 0≤z)
      (nnMul-distribL-≤RL x y z 0≤x 0≤y 0≤z)

  nnMul-distribR :
    (x y z : DedekindReal ℓ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (0≤z : z ≥0) →
    nnMul (x + y) z
      (+-Pres≥0 x y 0≤x 0≤y)
      0≤z
    ≡
    (nnMul x z 0≤x 0≤z) + (nnMul y z 0≤y 0≤z)
  nnMul-distribR x y z 0≤x 0≤y 0≤z =
    nnMul-comm (x + y) z (+-Pres≥0 x y 0≤x 0≤y) 0≤z ∙
    nnMul-distribL z x y 0≤z 0≤x 0≤y ∙
    cong₂ _+_
      (nnMul-comm z x 0≤z 0≤x)
      (nnMul-comm z y 0≤z 0≤y)
