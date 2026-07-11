{-

Laws for nonnegative multiplication of constructive Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.NonnegativeProductLaws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

import Constructive.Algebra.LinearlyOrderedCommRing.Base as LinearBase
open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Analysis.Completions.DedekindCompletion.Base
open import Constructive.Analysis.Completions.DedekindCompletion.Order
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Addition
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Approximation
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.NonnegativeProduct
open import Constructive.Foundations.Powerset hiding (Pred)

private
  variable
    ℓ ℓ' ℓᴾ : Level


module NonnegativeProductLaws
  (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  baseField : LinearlyOrderedField ℓ ℓ'
  baseField = 𝒜 .fst

  open CompletionBase baseField
  private
    module CutOrder = CompletionOrder baseField

  open CutOrder
    using ()
    renaming
      ( _≤_ to _≤D_
      ; ≤-antisym to ≤D-antisym
      ; ≤-trans to ≤D-trans
      ; ≡→≤ to ≡→≤D
      )
  open LinearlyOrderedFieldStr baseField
    renaming (+-Pres≥0 to K+-Pres≥0)

  open Addition 𝒜 {ℓᴾ}
  open AdditiveGroup 𝒜 {ℓᴾ}
  open NonnegativeProduct 𝒜 {ℓᴾ}

  private
    K : Type ℓ
    K = baseField .fst .fst .fst

  nnMul-lower-positive-product :
    (x y : DedekindCompletion ℓᴾ) →
    (a b : K) →
    a ∈ lower x →
    b ∈ lower y →
    0r < a →
    0r < b →
    (a · b) ∈ nnMulLower x y
  nnMul-lower-positive-product x y a b a∈Lx b∈Ly 0<a 0<b =
    Prop.rec squash₁ step
      (CompletionBase.lower-rounded {𝒦 = baseField} x a a∈Lx)
    where
    step :
      Σ[ a' ∈ K ] (a < a') × (a' ∈ lower x) →
      (a · b) ∈ nnMulLower x y
    step (a' , a<a' , a'∈Lx) =
      ∣ Sum.inr
          (a' , b
          , a'∈Lx
          , b∈Ly
          , <-trans 0<a a<a'
          , 0<b
          , ·-rPosPres< {x = b} 0<b a<a')
      ∣₁

  nnMul-assoc-≤LR :
    (x y z : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (0≤z : z ≥0) →
    nnMul x (nnMul y z 0≤y 0≤z)
      0≤x
      (nnMul-Pres≥0 y z 0≤y 0≤z)
    ≤D
    nnMul (nnMul x y 0≤x 0≤y) z
      (nnMul-Pres≥0 x y 0≤x 0≤y)
      0≤z
  nnMul-assoc-≤LR x y z 0≤x 0≤y 0≤z q =
    Prop.rec squash₁ outer
    where
    outer :
      (q < 0r) ⊎
      ProductLowerWitness x (nnMul y z 0≤y 0≤z) q →
      q ∈ nnMulLower (nnMul x y 0≤x 0≤y) z
    outer (Sum.inl q<0) =
      ∣ Sum.inl q<0 ∣₁
    outer (Sum.inr (a , b , a∈Lx , b∈Lyz , 0<a , 0<b , q<ab)) =
      Prop.rec squash₁ inner b∈Lyz
      where
      inner :
        (b < 0r) ⊎ ProductLowerWitness y z b →
        q ∈ nnMulLower (nnMul x y 0≤x 0≤y) z
      inner (Sum.inl b<0) =
        Empty.rec (<-asym 0<b b<0)
      inner (Sum.inr (c , d , c∈Ly , d∈Lz , 0<c , 0<d , b<cd)) =
        ∣ Sum.inr
            (a · c , d
            , nnMul-lower-positive-product x y a c a∈Lx c∈Ly 0<a 0<c
            , d∈Lz
            , ·-Pres>0 0<a 0<c
            , 0<d
            , q<ac*d)
        ∣₁
        where
        ab<a*cd : a · b < a · (c · d)
        ab<a*cd =
          ·-lPosPres< 0<a b<cd

        q<a*cd : q < a · (c · d)
        q<a*cd =
          <-trans q<ab ab<a*cd

        q<ac*d : q < (a · c) · d
        q<ac*d =
          subst (λ v → q < v) (·Assoc a c d) q<a*cd

  nnMul-assoc-≤RL :
    (x y z : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (0≤z : z ≥0) →
    nnMul (nnMul x y 0≤x 0≤y) z
      (nnMul-Pres≥0 x y 0≤x 0≤y)
      0≤z
    ≤D
    nnMul x (nnMul y z 0≤y 0≤z)
      0≤x
      (nnMul-Pres≥0 y z 0≤y 0≤z)
  nnMul-assoc-≤RL x y z 0≤x 0≤y 0≤z q =
    Prop.rec squash₁ outer
    where
    outer :
      (q < 0r) ⊎
      ProductLowerWitness (nnMul x y 0≤x 0≤y) z q →
      q ∈ nnMulLower x (nnMul y z 0≤y 0≤z)
    outer (Sum.inl q<0) =
      ∣ Sum.inl q<0 ∣₁
    outer (Sum.inr (A , d , A∈Lxy , d∈Lz , 0<A , 0<d , q<Ad)) =
      Prop.rec squash₁ inner A∈Lxy
      where
      inner :
        (A < 0r) ⊎ ProductLowerWitness x y A →
        q ∈ nnMulLower x (nnMul y z 0≤y 0≤z)
      inner (Sum.inl A<0) =
        Empty.rec (<-asym 0<A A<0)
      inner (Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , A<ab)) =
        ∣ Sum.inr
            (a , b · d
            , a∈Lx
            , nnMul-lower-positive-product y z b d b∈Ly d∈Lz 0<b 0<d
            , 0<a
            , ·-Pres>0 0<b 0<d
            , q<a*bd)
        ∣₁
        where
        Ad<ab*d : A · d < (a · b) · d
        Ad<ab*d =
          ·-rPosPres< {x = d} 0<d A<ab

        q<ab*d : q < (a · b) · d
        q<ab*d =
          <-trans q<Ad Ad<ab*d

        q<a*bd : q < a · (b · d)
        q<a*bd =
          subst (λ v → q < v) (sym (·Assoc a b d)) q<ab*d

  nnMul-assoc :
    (x y z : DedekindCompletion ℓᴾ) →
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
    ≤D-antisym
      (nnMul x (nnMul y z 0≤y 0≤z)
        0≤x
        (nnMul-Pres≥0 y z 0≤y 0≤z))
      (nnMul (nnMul x y 0≤x 0≤y) z
        (nnMul-Pres≥0 x y 0≤x 0≤y)
        0≤z)
      (nnMul-assoc-≤LR x y z 0≤x 0≤y 0≤z)
      (nnMul-assoc-≤RL x y z 0≤x 0≤y 0≤z)

  nnMul-distribL-≤LR :
    (x y z : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (0≤z : z ≥0) →
    nnMul x (y +𝔻 z)
      0≤x
      (+-Pres≥0 y z 0≤y 0≤z)
    ≤D
    (nnMul x y 0≤x 0≤y) +𝔻 (nnMul x z 0≤x 0≤z)
  nnMul-distribL-≤LR x y z 0≤x 0≤y 0≤z q =
    Prop.rec squash₁ outer
    where
    xy : DedekindCompletion ℓᴾ
    xy = nnMul x y 0≤x 0≤y

    xz : DedekindCompletion ℓᴾ
    xz = nnMul x z 0≤x 0≤z

    0≤xy : xy ≥0
    0≤xy = nnMul-Pres≥0 x y 0≤x 0≤y

    0≤xz : xz ≥0
    0≤xz = nnMul-Pres≥0 x z 0≤x 0≤z

    target : K → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
    target t = t ∈ lower (xy +𝔻 xz)

    lower-add :
      (r s : K) →
      r ∈ nnMulLower x y →
      s ∈ nnMulLower x z →
      q < r + s →
      target q
    lower-add r s r∈Lxy s∈Lxz q<r+s =
      ∣ r , s , r∈Lxy , s∈Lxz , q<r+s ∣₁

    q<ac+ad :
      (a b c d : K) →
      0r < a →
      q < a · b →
      b < c + d →
      q < (a · c) + (a · d)
    q<ac+ad a b c d 0<a q<ab b<c+d =
      subst (λ v → q < v)
        (mul-distrib-left a c d)
        q<a[c+d]
      where
      ab<a[c+d] : a · b < a · (c + d)
      ab<a[c+d] =
        ·-lPosPres< 0<a b<c+d

      q<a[c+d] : q < a · (c + d)
      q<a[c+d] =
        <-trans q<ab ab<a[c+d]

    pos-pos :
      (a b c d : K) →
      a ∈ lower x →
      c ∈ lower y →
      d ∈ lower z →
      0r < a →
      0r < c →
      0r < d →
      q < a · b →
      b < c + d →
      target q
    pos-pos a b c d a∈Lx c∈Ly d∈Lz 0<a 0<c 0<d q<ab b<c+d =
      lower-add
        (a · c)
        (a · d)
        (nnMul-lower-positive-product x y a c a∈Lx c∈Ly 0<a 0<c)
        (nnMul-lower-positive-product x z a d a∈Lx d∈Lz 0<a 0<d)
        (q<ac+ad a b c d 0<a q<ab b<c+d)

    nonpos-pos :
      (a b c d : K) →
      a ∈ lower x →
      d ∈ lower z →
      0r < a →
      c ≤ 0r →
      0r < d →
      q < a · b →
      b < c + d →
      target q
    nonpos-pos a b c d a∈Lx d∈Lz 0<a c≤0 0<d q<ab b<c+d =
      Prop.rec squash₁ step
        (dense (q<ac+ad a b c d 0<a q<ab b<c+d))
      where
      ad : K
      ad = a · d

      ac : K
      ac = a · c

      ac≤0 : ac ≤ 0r
      ac≤0 = mul-nonpositive-right 0<a c≤0

      step :
        Σ[ m ∈ K ] (q < m) × (m < ac + ad) →
        target q
      step (m , q<m , m<ac+ad) =
        lower-add
          (m - ad)
          ad
          (nnMul-lower-from-negative x y (m - ad) m-ad<0)
          (nnMul-lower-positive-product x z a d a∈Lx d∈Lz 0<a 0<d)
          q<split
        where
        m-ad<ac : m - ad < ac
        m-ad<ac =
          +-MoveRToL< m<ac+ad

        m-ad<0 : m - ad < 0r
        m-ad<0 =
          <≤-trans m-ad<ac ac≤0

        q<split : q < (m - ad) + ad
        q<split =
          subst (λ v → q < v)
            (sym ([p-q]+q≡p m ad))
            q<m

    pos-nonpos :
      (a b c d : K) →
      a ∈ lower x →
      c ∈ lower y →
      0r < a →
      0r < c →
      d ≤ 0r →
      q < a · b →
      b < c + d →
      target q
    pos-nonpos a b c d a∈Lx c∈Ly 0<a 0<c d≤0 q<ab b<c+d =
      Prop.rec squash₁ step
        (dense (q<ac+ad a b c d 0<a q<ab b<c+d))
      where
      ac : K
      ac = a · c

      ad : K
      ad = a · d

      ad≤0 : ad ≤ 0r
      ad≤0 = mul-nonpositive-right 0<a d≤0

      step :
        Σ[ m ∈ K ] (q < m) × (m < ac + ad) →
        target q
      step (m , q<m , m<ac+ad) =
        lower-add
          ac
          (m - ac)
          (nnMul-lower-positive-product x y a c a∈Lx c∈Ly 0<a 0<c)
          (nnMul-lower-from-negative x z (m - ac) m-ac<0)
          q<split
        where
        m-ac<ad : m - ac < ad
        m-ac<ad =
          +-MoveRToL<' m<ac+ad

        m-ac<0 : m - ac < 0r
        m-ac<0 =
          <≤-trans m-ac<ad ad≤0

        q<split : q < ac + (m - ac)
        q<split =
          subst (λ v → q < v)
            (sym (p+[q-p]≡q ac m))
            q<m

    nonpos-nonpos-absurd :
      (b c d : K) →
      0r < b →
      b < c + d →
      c ≤ 0r →
      d ≤ 0r →
      target q
    nonpos-nonpos-absurd b c d 0<b b<c+d c≤0 d≤0 =
      Empty.rec (<-asym 0<b b<0)
      where
      c+d≤0+0 : c + d ≤ 0r + 0r
      c+d≤0+0 =
        +-Pres≤ c≤0 d≤0

      c+d≤0 : c + d ≤ 0r
      c+d≤0 =
        subst (λ v → c + d ≤ v)
          (+IdR 0r)
          c+d≤0+0

      b<0 : b < 0r
      b<0 =
        <≤-trans b<c+d c+d≤0

    split-cd :
      (a b c d : K) →
      a ∈ lower x →
      c ∈ lower y →
      d ∈ lower z →
      0r < a →
      0r < b →
      q < a · b →
      b < c + d →
      target q
    split-cd a b c d a∈Lx c∈Ly d∈Lz 0<a 0<b q<ab b<c+d
      with trichotomy 0r c | trichotomy 0r d
    ... | LinearBase.lt 0<c | LinearBase.lt 0<d =
      pos-pos a b c d a∈Lx c∈Ly d∈Lz 0<a 0<c 0<d q<ab b<c+d
    ... | LinearBase.lt 0<c | LinearBase.eq 0≡d =
      pos-nonpos a b c d a∈Lx c∈Ly 0<a 0<c
        (≤-refl (sym 0≡d))
        q<ab b<c+d
    ... | LinearBase.lt 0<c | LinearBase.gt d<0 =
      pos-nonpos a b c d a∈Lx c∈Ly 0<a 0<c
        (<-≤-weaken d<0)
        q<ab b<c+d
    ... | LinearBase.eq 0≡c | LinearBase.lt 0<d =
      nonpos-pos a b c d a∈Lx d∈Lz 0<a
        (≤-refl (sym 0≡c))
        0<d q<ab b<c+d
    ... | LinearBase.eq 0≡c | LinearBase.eq 0≡d =
      nonpos-nonpos-absurd b c d 0<b b<c+d
        (≤-refl (sym 0≡c))
        (≤-refl (sym 0≡d))
    ... | LinearBase.eq 0≡c | LinearBase.gt d<0 =
      nonpos-nonpos-absurd b c d 0<b b<c+d
        (≤-refl (sym 0≡c))
        (<-≤-weaken d<0)
    ... | LinearBase.gt c<0 | LinearBase.lt 0<d =
      nonpos-pos a b c d a∈Lx d∈Lz 0<a
        (<-≤-weaken c<0)
        0<d q<ab b<c+d
    ... | LinearBase.gt c<0 | LinearBase.eq 0≡d =
      nonpos-nonpos-absurd b c d 0<b b<c+d
        (<-≤-weaken c<0)
        (≤-refl (sym 0≡d))
    ... | LinearBase.gt c<0 | LinearBase.gt d<0 =
      nonpos-nonpos-absurd b c d 0<b b<c+d
        (<-≤-weaken c<0)
        (<-≤-weaken d<0)

    outer :
      (q < 0r) ⊎ ProductLowerWitness x (y +𝔻 z) q →
      target q
    outer (Sum.inl q<0) =
      +-Pres≥0 xy xz 0≤xy 0≤xz q (lift q<0)
    outer (Sum.inr (a , b , a∈Lx , b∈Ly+z , 0<a , 0<b , q<ab)) =
      Prop.rec squash₁
        (λ (c , d , c∈Ly , d∈Lz , b<c+d) →
          split-cd a b c d a∈Lx c∈Ly d∈Lz 0<a 0<b q<ab b<c+d)
        b∈Ly+z

  nnMul-distribL-≤RL :
    (x y z : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (0≤z : z ≥0) →
    (nnMul x y 0≤x 0≤y) +𝔻 (nnMul x z 0≤x 0≤z)
    ≤D
    nnMul x (y +𝔻 z)
      0≤x
      (+-Pres≥0 y z 0≤y 0≤z)
  nnMul-distribL-≤RL x y z 0≤x 0≤y 0≤z q =
    Prop.rec squash₁ outer
    where
    yz : DedekindCompletion ℓᴾ
    yz = y +𝔻 z

    0≤yz : yz ≥0
    0≤yz = +-Pres≥0 y z 0≤y 0≤z

    xy : DedekindCompletion ℓᴾ
    xy = nnMul x y 0≤x 0≤y

    xz : DedekindCompletion ℓᴾ
    xz = nnMul x z 0≤x 0≤z

    x-yz : DedekindCompletion ℓᴾ
    x-yz = nnMul x yz 0≤x 0≤yz

    y≤yz : y ≤D yz
    y≤yz =
      ≤D-trans y (y +𝔻 0𝔻) yz
        (≡→≤D (sym (+-idR y)))
        (+-monoL-≤ 0𝔻 z y 0≤z)

    z≤yz : z ≤D yz
    z≤yz =
      ≤D-trans z (0𝔻 +𝔻 z) yz
        (≡→≤D (sym (+-idL z)))
        (+-monoR-≤ 0𝔻 y z 0≤y)

    xy≤x-yz : xy ≤D x-yz
    xy≤x-yz =
      nnMul-monoR-≤ x y yz 0≤x 0≤y 0≤yz y≤yz

    xz≤x-yz : xz ≤D x-yz
    xz≤x-yz =
      nnMul-monoR-≤ x z yz 0≤x 0≤z 0≤yz z≤yz

    lower-from-xy :
      (r s : K) →
      r < 0r →
      s ∈ nnMulLower x z →
      q < r + s →
      q ∈ nnMulLower x yz
    lower-from-xy r s r<0 s∈Lxz q<r+s =
      xz≤x-yz q q∈Lxz
      where
      r+s<s : r + s < s
      r+s<s =
        subst (λ v → r + s < v)
          (+IdL s)
          (+-rPres< {z = s} r<0)

      q<s : q < s
      q<s = <-trans q<r+s r+s<s

      q∈Lxz : q ∈ lower xz
      q∈Lxz =
        CompletionBase.lower-closed {𝒦 = baseField} xz q s q<s s∈Lxz

    lower-from-xz :
      (r s : K) →
      r ∈ nnMulLower x y →
      s < 0r →
      q < r + s →
      q ∈ nnMulLower x yz
    lower-from-xz r s r∈Lxy s<0 q<r+s =
      xy≤x-yz q q∈Lxy
      where
      r+s<r : r + s < r
      r+s<r =
        +-rNeg→< s<0

      q<r : q < r
      q<r = <-trans q<r+s r+s<r

      q∈Lxy : q ∈ lower xy
      q∈Lxy =
        CompletionBase.lower-closed {𝒦 = baseField} xy q r q<r r∈Lxy

    sum-lower :
      (b d : K) →
      b ∈ lower y →
      d ∈ lower z →
      (b + d) ∈ lower yz
    sum-lower b d b∈Ly d∈Lz =
      Prop.rec squash₁ step
        (CompletionBase.lower-rounded {𝒦 = baseField} y b b∈Ly)
      where
      step :
        Σ[ b' ∈ K ] (b < b') × (b' ∈ lower y) →
        (b + d) ∈ lower yz
      step (b' , b<b' , b'∈Ly) =
        ∣ b' , d
        , b'∈Ly
        , d∈Lz
        , +-rPres< {z = d} b<b'
        ∣₁

    both-positive :
      (r s a b c d : K) →
      a ∈ lower x →
      b ∈ lower y →
      c ∈ lower x →
      d ∈ lower z →
      0r < a →
      0r < b →
      0r < c →
      0r < d →
      r < a · b →
      s < c · d →
      q < r + s →
      q ∈ nnMulLower x yz
    both-positive r s a b c d a∈Lx b∈Ly c∈Lx d∈Lz
      0<a 0<b 0<c 0<d r<ab s<cd q<r+s
      with ≤-total a c
    ... | Sum.inl a≤c =
      ∣ Sum.inr
          (c , b + d
          , c∈Lx
          , sum-lower b d b∈Ly d∈Lz
          , 0<c
          , +-Pres>0 0<b 0<d
          , q<c[b+d])
      ∣₁
      where
      r+s<ab+cd : r + s < (a · b) + (c · d)
      r+s<ab+cd =
        +-Pres< r<ab s<cd

      q<ab+cd : q < (a · b) + (c · d)
      q<ab+cd =
        <-trans q<r+s r+s<ab+cd

      ab≤cb : a · b ≤ c · b
      ab≤cb =
        ·-rPosPres≤ {x = b} (<-≤-weaken 0<b) a≤c

      ab+cd≤cb+cd :
        (a · b) + (c · d) ≤
        (c · b) + (c · d)
      ab+cd≤cb+cd =
        +-Pres≤ ab≤cb (≤-refl refl)

      q<cb+cd : q < (c · b) + (c · d)
      q<cb+cd =
        <≤-trans q<ab+cd ab+cd≤cb+cd

      q<c[b+d] : q < c · (b + d)
      q<c[b+d] =
        subst (λ v → q < v)
          (sym (mul-distrib-left c b d))
          q<cb+cd
    ... | Sum.inr c≤a =
      ∣ Sum.inr
          (a , b + d
          , a∈Lx
          , sum-lower b d b∈Ly d∈Lz
          , 0<a
          , +-Pres>0 0<b 0<d
          , q<a[b+d])
      ∣₁
      where
      r+s<ab+cd : r + s < (a · b) + (c · d)
      r+s<ab+cd =
        +-Pres< r<ab s<cd

      q<ab+cd : q < (a · b) + (c · d)
      q<ab+cd =
        <-trans q<r+s r+s<ab+cd

      cd≤ad : c · d ≤ a · d
      cd≤ad =
        ·-rPosPres≤ {x = d} (<-≤-weaken 0<d) c≤a

      ab+cd≤ab+ad :
        (a · b) + (c · d) ≤
        (a · b) + (a · d)
      ab+cd≤ab+ad =
        +-Pres≤ (≤-refl refl) cd≤ad

      q<ab+ad : q < (a · b) + (a · d)
      q<ab+ad =
        <≤-trans q<ab+cd ab+cd≤ab+ad

      q<a[b+d] : q < a · (b + d)
      q<a[b+d] =
        subst (λ v → q < v)
          (sym (mul-distrib-left a b d))
          q<ab+ad

    split-products :
      (r s : K) →
      r ∈ nnMulLower x y →
      s ∈ nnMulLower x z →
      q < r + s →
      q ∈ nnMulLower x yz
    split-products r s r∈Lxy s∈Lxz q<r+s =
      Prop.rec (isProp∈ (nnMulLower x yz) q) left-case r∈Lxy
      where
      left-case :
        (r < 0r) ⊎ ProductLowerWitness x y r →
        q ∈ nnMulLower x yz
      left-case (Sum.inl r<0) =
        lower-from-xy r s r<0 s∈Lxz q<r+s
      left-case (Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , r<ab)) =
        Prop.rec (isProp∈ (nnMulLower x yz) q) right-case s∈Lxz
        where
        right-case :
          (s < 0r) ⊎ ProductLowerWitness x z s →
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
      Σ[ r ∈ K ] Σ[ s ∈ K ]
        (r ∈ lower xy) ×
        (s ∈ lower xz) ×
        (q < r + s) →
      q ∈ nnMulLower x yz
    outer (r , s , r∈Lxy , s∈Lxz , q<r+s) =
      split-products r s r∈Lxy s∈Lxz q<r+s

  nnMul-distribL :
    (x y z : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (0≤z : z ≥0) →
    nnMul x (y +𝔻 z)
      0≤x
      (+-Pres≥0 y z 0≤y 0≤z)
    ≡
    (nnMul x y 0≤x 0≤y) +𝔻 (nnMul x z 0≤x 0≤z)
  nnMul-distribL x y z 0≤x 0≤y 0≤z =
    ≤D-antisym
      (nnMul x (y +𝔻 z)
        0≤x
        (+-Pres≥0 y z 0≤y 0≤z))
      ((nnMul x y 0≤x 0≤y) +𝔻 (nnMul x z 0≤x 0≤z))
      (nnMul-distribL-≤LR x y z 0≤x 0≤y 0≤z)
      (nnMul-distribL-≤RL x y z 0≤x 0≤y 0≤z)

  nnMul-distribR :
    (x y z : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (0≤z : z ≥0) →
    nnMul (x +𝔻 y) z
      (+-Pres≥0 x y 0≤x 0≤y)
      0≤z
    ≡
    (nnMul x z 0≤x 0≤z) +𝔻 (nnMul y z 0≤y 0≤z)
  nnMul-distribR x y z 0≤x 0≤y 0≤z =
    nnMul-comm (x +𝔻 y) z (+-Pres≥0 x y 0≤x 0≤y) 0≤z ∙
    nnMul-distribL z x y 0≤z 0≤x 0≤y ∙
    cong₂ _+𝔻_
      (nnMul-comm z x 0≤z 0≤x)
      (nnMul-comm z y 0≤z 0≤y)
