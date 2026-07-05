{-

Additive group of constructive Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindCompletion.Arithmetic.AdditiveGroup where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∣_∣₁ ; squash₁)

open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.DedekindCompletion
open import Constructive.DedekindCompletion.Arithmetic.Base
open import Constructive.DedekindCompletion.Arithmetic.Negation

private
  variable
    ℓ ℓ' ℓᴾ : Level


module AdditiveGroup (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  𝒦 : LinearlyOrderedField ℓ ℓ'
  𝒦 = 𝒜 .fst

  open CompletionBase 𝒦
  module OrdD = CompletionOrder 𝒦
  open LinearlyOrderedFieldStr 𝒦
    renaming (+-Pres≥0 to K+-Pres≥0)

  open ArithmeticBase 𝒜
  open Approximation {ℓᴾ}
  open Addition {ℓᴾ}
  open Negation 𝒜 {ℓᴾ}

  +-invR :
    (x : DedekindCompletion ℓᴾ) →
    x +𝔻 (-𝔻 x) ≡ 0𝔻
  +-invR x =
    completionExt (x +𝔻 (-𝔻 x)) 0𝔻
      lower⊆
      lower⊇
      upper⊆
      upper⊇
    where
    lower⊆ : addLower x (-𝔻 x) ⊆ lower 0𝔻
    lower⊆ q =
      Prop.rec (isProp∈ (lower 0𝔻) q)
        (λ (r , s , r∈Lx , -s∈Ux , q<r+s) →
          let
            r<-s : r < - s
            r<-s = OrdD.lower<upper x r (- s) r∈Lx -s∈Ux

            r+s<-s+s : r + s < (- s) + s
            r+s<-s+s = +-rPres< {z = s} r<-s

            r+s<0 : r + s < 0r
            r+s<0 =
              subst (λ v → r + s < v) (+InvL s) r+s<-s+s

            q<0 : q < 0r
            q<0 = <-trans q<r+s r+s<0
          in
          lift q<0)

    lower⊇ : lower 0𝔻 ⊆ addLower x (-𝔻 x)
    lower⊇ q q<0 =
      Prop.rec squash₁
        (λ (p , u , p∈Lx , u∈Ux , _ , u<p-q) →
          ∣ p , - u
          , p∈Lx
          , subst (λ v → v ∈ upper x) (sym (-Idempotent u)) u∈Ux
          , +-MoveLToR< (-MoveRToL<' u<p-q)
          ∣₁)
        (close-bounds x (- q) (-Reverse<0 (Lift.lower q<0)))

    upper⊆ : addUpper x (-𝔻 x) ⊆ upper 0𝔻
    upper⊆ q =
      Prop.rec (isProp∈ (upper 0𝔻) q)
        (λ (r , s , r∈Ux , -s∈Lx , r+s<q) →
          let
            -s<r : - s < r
            -s<r = OrdD.lower<upper x (- s) r -s∈Lx r∈Ux

            -s+s<r+s : (- s) + s < r + s
            -s+s<r+s = +-rPres< {z = s} -s<r

            0<r+s : 0r < r + s
            0<r+s =
              subst (λ v → v < r + s) (+InvL s) -s+s<r+s

            0<q : 0r < q
            0<q = <-trans 0<r+s r+s<q
          in
          lift 0<q)

    upper⊇ : upper 0𝔻 ⊆ addUpper x (-𝔻 x)
    upper⊇ q 0<q =
      Prop.rec squash₁
        (λ (p , u , p∈Lx , u∈Ux , _ , u<p+q) →
          let
            u<q+p : u < q + p
            u<q+p =
              subst (λ v → u < v) (+Comm p q) u<p+q

            u-p<q : u - p < q
            u-p<q = +-MoveRToL< u<q+p
          in
          ∣ u , - p
          , u∈Ux
          , subst (λ v → v ∈ lower x) (sym (-Idempotent p)) p∈Lx
          , u-p<q
          ∣₁)
        (close-bounds x q (Lift.lower 0<q))

  +-invL :
    (x : DedekindCompletion ℓᴾ) →
    (-𝔻 x) +𝔻 x ≡ 0𝔻
  +-invL x = +-comm (-𝔻 x) x ∙ +-invR x

  DedekindCompletionAbGroup : AbGroup _
  DedekindCompletionAbGroup =
    makeAbGroup 0𝔻 _+𝔻_ -𝔻_ isSetDedekindCompletion
      +-assoc +-idR +-invR +-comm

  module DedekindCompletionAbGroupTheory =
    AbGroupTheory DedekindCompletionAbGroup
  module DedekindCompletionGroupTheory =
    GroupTheory (AbGroup→Group DedekindCompletionAbGroup)

  +-interchange :
    (a b c d : DedekindCompletion ℓᴾ) →
    (a +𝔻 b) +𝔻 (c +𝔻 d) ≡ (a +𝔻 c) +𝔻 (b +𝔻 d)
  +-interchange =
    DedekindCompletionAbGroupTheory.comm-4

  +-cancelR :
    (x y z : DedekindCompletion ℓᴾ) →
    x +𝔻 z ≡ y +𝔻 z →
    x ≡ y
  +-cancelR x y z =
    DedekindCompletionGroupTheory.·CancelR z

  +-cancelL :
    (x y z : DedekindCompletion ℓᴾ) →
    z +𝔻 x ≡ z +𝔻 y →
    x ≡ y
  +-cancelL x y z =
    DedekindCompletionGroupTheory.·CancelL z

  inverse-uniqueR :
    (x y : DedekindCompletion ℓᴾ) →
    x +𝔻 y ≡ 0𝔻 →
    -𝔻 x ≡ y
  inverse-uniqueR x y x+y≡0 =
    sym (DedekindCompletionGroupTheory.invUniqueR x+y≡0)

  inverse-uniqueL :
    (x y : DedekindCompletion ℓᴾ) →
    y +𝔻 x ≡ 0𝔻 →
    -𝔻 x ≡ y
  inverse-uniqueL x y y+x≡0 =
    sym (DedekindCompletionGroupTheory.invUniqueL y+x≡0)

  neg-add :
    (a b : DedekindCompletion ℓᴾ) →
    -𝔻 (a +𝔻 b) ≡ (-𝔻 a) +𝔻 (-𝔻 b)
  neg-add a b =
    DedekindCompletionGroupTheory.invDistr a b ∙
    +-comm (-𝔻 b) (-𝔻 a)

  neg-difference-swap :
    (a b : DedekindCompletion ℓᴾ) →
    -𝔻 (a +𝔻 (-𝔻 b)) ≡ b +𝔻 (-𝔻 a)
  neg-difference-swap a b =
    neg-add a (-𝔻 b) ∙
    cong₂ _+𝔻_ refl (neg-involutive b) ∙
    +-comm (-𝔻 a) b

  difference-neg-swap :
    (a b : DedekindCompletion ℓᴾ) →
    a +𝔻 (-𝔻 b) ≡ -𝔻 (b +𝔻 (-𝔻 a))
  difference-neg-swap a b =
    sym (neg-difference-swap b a)

  plus-minus-cancelR :
    (x n : DedekindCompletion ℓᴾ) →
    (x +𝔻 n) +𝔻 (-𝔻 n) ≡ x
  plus-minus-cancelR x n =
    sym (+-assoc x n (-𝔻 n)) ∙
    cong (x +𝔻_) (+-invR n) ∙
    +-idR x

  minus-plus-cancelR :
    (x n : DedekindCompletion ℓᴾ) →
    (x +𝔻 (-𝔻 n)) +𝔻 n ≡ x
  minus-plus-cancelR x n =
    sym (+-assoc x (-𝔻 n) n) ∙
    cong (x +𝔻_) (+-invL n) ∙
    +-idR x

  sum-differences :
    (a b c d : DedekindCompletion ℓᴾ) →
    (a +𝔻 (-𝔻 b)) +𝔻 (c +𝔻 (-𝔻 d))
    ≡
    (a +𝔻 c) +𝔻 (-𝔻 (b +𝔻 d))
  sum-differences a b c d =
    +-interchange a (-𝔻 b) c (-𝔻 d) ∙
    cong ((a +𝔻 c) +𝔻_) (sym (neg-add b d))

  difference-eq→cross-sum :
    (a b c d : DedekindCompletion ℓᴾ) →
    a +𝔻 (-𝔻 b) ≡ c +𝔻 (-𝔻 d) →
    a +𝔻 d ≡ c +𝔻 b
  difference-eq→cross-sum a b c d diff-path =
    sym left-normal ∙
    cong (_+𝔻 (b +𝔻 d)) diff-path ∙
    right-normal
    where
    left-normal :
      (a +𝔻 (-𝔻 b)) +𝔻 (b +𝔻 d) ≡ a +𝔻 d
    left-normal =
      +-assoc (a +𝔻 (-𝔻 b)) b d ∙
      cong (_+𝔻 d) (minus-plus-cancelR a b)

    right-normal :
      (c +𝔻 (-𝔻 d)) +𝔻 (b +𝔻 d) ≡ c +𝔻 b
    right-normal =
      +-interchange c (-𝔻 d) b d ∙
      cong ((c +𝔻 b) +𝔻_) (+-invL d) ∙
      +-idR (c +𝔻 b)

  cross-sum→difference-eq :
    (a b c d : DedekindCompletion ℓᴾ) →
    a +𝔻 d ≡ c +𝔻 b →
    a +𝔻 (-𝔻 b) ≡ c +𝔻 (-𝔻 d)
  cross-sum→difference-eq a b c d cross-path =
    sym left-normal ∙
    cong (_+𝔻 ((-𝔻 b) +𝔻 (-𝔻 d))) cross-path ∙
    right-normal
    where
    left-normal :
      (a +𝔻 d) +𝔻 ((-𝔻 b) +𝔻 (-𝔻 d)) ≡ a +𝔻 (-𝔻 b)
    left-normal =
      +-interchange a d (-𝔻 b) (-𝔻 d) ∙
      cong ((a +𝔻 (-𝔻 b)) +𝔻_) (+-invR d) ∙
      +-idR (a +𝔻 (-𝔻 b))

    right-normal :
      (c +𝔻 b) +𝔻 ((-𝔻 b) +𝔻 (-𝔻 d)) ≡ c +𝔻 (-𝔻 d)
    right-normal =
      +-assoc (c +𝔻 b) (-𝔻 b) (-𝔻 d) ∙
      cong (_+𝔻 (-𝔻 d)) (plus-minus-cancelR c b)

  +-monoR-≤ :
    (x y z : DedekindCompletion ℓᴾ) →
    OrdD._≤_ x y →
    OrdD._≤_ (x +𝔻 z) (y +𝔻 z)
  +-monoR-≤ x y z x≤y q =
    Prop.rec squash₁
      (λ (r , s , r∈Lx , s∈Lz , q<r+s) →
        ∣ r , s , x≤y r r∈Lx , s∈Lz , q<r+s ∣₁)

  +-monoL-≤ :
    (x y z : DedekindCompletion ℓᴾ) →
    OrdD._≤_ x y →
    OrdD._≤_ (z +𝔻 x) (z +𝔻 y)
  +-monoL-≤ x y z x≤y =
    subst2 OrdD._≤_ (+-comm x z) (+-comm y z)
      (+-monoR-≤ x y z x≤y)

  +-mono-≤ :
    (x y z w : DedekindCompletion ℓᴾ) →
    OrdD._≤_ x y →
    OrdD._≤_ z w →
    OrdD._≤_ (x +𝔻 z) (y +𝔻 w)
  +-mono-≤ x y z w x≤y z≤w =
    OrdD.≤-trans (x +𝔻 z) (y +𝔻 z) (y +𝔻 w)
      (+-monoR-≤ x y z x≤y)
      (+-monoL-≤ z w y z≤w)

  +-Pres≥0 :
    (x y : DedekindCompletion ℓᴾ) →
    OrdD._≤_ 0𝔻 x →
    OrdD._≤_ 0𝔻 y →
    OrdD._≤_ 0𝔻 (x +𝔻 y)
  +-Pres≥0 x y 0≤x 0≤y =
    OrdD.≤-trans 0𝔻 (0𝔻 +𝔻 0𝔻) (x +𝔻 y)
      (OrdD.≡→≤ (sym (+-idR 0𝔻)))
      (+-mono-≤ 0𝔻 x 0𝔻 y 0≤x 0≤y)
