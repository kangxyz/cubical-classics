{-

Order compatibility for constructive Dedekind-completion arithmetic

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindCompletion.Arithmetic.Order where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
import Cubical.Functions.Logic as L

open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedes
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.DedekindCompletion
open import Constructive.DedekindCompletion.Arithmetic.Base
open import Constructive.DedekindCompletion.Arithmetic.Negation
open import Constructive.DedekindCompletion.Arithmetic.AdditiveGroup
open import Constructive.DedekindCompletion.Arithmetic.NonNegative
open import Constructive.DedekindCompletion.Arithmetic.Multiplication
open import Constructive.DedekindCompletion.Arithmetic.Difference
open import Constructive.DedekindCompletion.Arithmetic.Distributivity

private
  variable
    ℓ ℓ' ℓᴾ : Level


module OrderProperties
  (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  orderedBaseField : LinearlyOrderedField ℓ ℓ'
  orderedBaseField = 𝒜 .fst

  open CompletionBase orderedBaseField
  module CutOrder = CompletionOrder orderedBaseField
  open CutOrder
    using
      ( lower→K< ; <→≤ ; basis-located
      ; isStrictOrder< ; isProp≤ ; ≤→¬> ; ¬>→≤
      ; <-≤-trans ; ≤-<-trans ; DedekindCompletion≤Pseudolattice
      )
    renaming
      ( _≤_ to _≤D_
      ; _<_ to _<D_
      ; ≡→≤ to ≡→≤D
      ; <-trans to <D-trans
      )
  open LinearlyOrderedFieldStr orderedBaseField

  open ArithmeticBase 𝒜
  open Approximation {ℓᴾ}
  open Addition {ℓᴾ}
  open Negation 𝒜 {ℓᴾ}
  open AdditiveGroup 𝒜 {ℓᴾ}
  open NonNegativeMultiplication 𝒜 {ℓᴾ}
  open Multiplication 𝒜 {ℓᴾ}
  open MultiplicationNegation 𝒜 {ℓᴾ}
  open DifferenceProperties 𝒜 {ℓᴾ}
  open MultiplicationDistributivity 𝒜 {ℓᴾ}

  private
    K : Type ℓ
    K = Carrier

  K→<-pres :
    (p q : K) →
    p < q →
    K→𝔻 ℓᴾ p <D K→𝔻 ℓᴾ q
  K→<-pres p q p<q =
    ∣ middle p q
    , lift (middle>l p<q)
    , lift (middle<r p<q)
    ∣₁

  0𝔻<1𝔻 : 0𝔻 <D 1𝔻
  0𝔻<1𝔻 =
    K→<-pres 0r 1r 1>0

  +-monoR-< :
    (x y z : DedekindCompletion ℓᴾ) →
    x <D y →
    (x +𝔻 z) <D (y +𝔻 z)
  +-monoR-< x y z =
    Prop.rec squash₁
      (λ (p , p∈Ux , p∈Ly) →
        Prop.rec squash₁
          (λ (r , p<r , r∈Ly) →
            Prop.rec squash₁
              (λ (l , u , l∈Lz , u∈Uz , _ , u<l+r-p) →
                let
                  p+u<r+l : p + u < r + l
                  p+u<r+l =
                    subst (λ v → p + u < v)
                      (sum-left-close-path p l r)
                      (+-lPres< {z = p} u<l+r-p)
                  q = middle (p + u) (r + l)
                  p+u<q = middle>l p+u<r+l
                  q<r+l = middle<r p+u<r+l
                in
                ∣ q
                , ∣ p , u , p∈Ux , u∈Uz , p+u<q ∣₁
                , ∣ r , l , r∈Ly , l∈Lz , q<r+l ∣₁
                ∣₁)
              (close-bounds z (r - p) (<→Diff>0 p<r)))
          (CompletionBase.lower-rounded {𝒦 = orderedBaseField} y p p∈Ly))

  +-monoL-< :
    (x y z : DedekindCompletion ℓᴾ) →
    x <D y →
    (z +𝔻 x) <D (z +𝔻 y)
  +-monoL-< x y z x<y =
    subst2 _<D_ (+-comm x z) (+-comm y z)
      (+-monoR-< x y z x<y)

  _>0𝔻 : DedekindCompletion ℓᴾ → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  x >0𝔻 = 0𝔻 <D x

  infix 4 _>0𝔻

  >0→≥0 :
    (x : DedekindCompletion ℓᴾ) →
    x >0𝔻 →
    x ≥0
  >0→≥0 x =
    <→≤ 0𝔻 x

  ∃lower>0 :
    (x : DedekindCompletion ℓᴾ) →
    x >0𝔻 →
    ∥ Σ[ q ∈ K ] (0r < q) × (q ∈ lower x) ∥₁
  ∃lower>0 x =
    Prop.rec squash₁
      (λ (q , 0<q , q∈Lx) →
        ∣ q , Lift.lower 0<q , q∈Lx ∣₁)

  nnMul-Pres>0 :
    (x y : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    x >0𝔻 →
    y >0𝔻 →
    (nnMul x y 0≤x 0≤y) >0𝔻
  nnMul-Pres>0 x y 0≤x 0≤y 0<x 0<y =
    Prop.rec2 squash₁
      (λ (a , 0<a , a∈Lx) (b , 0<b , b∈Ly) →
        let
          ab = a · b
          0<ab = ·-Pres>0 0<a 0<b
          q = middle 0r ab
          0<q = middle>l 0<ab
          q<ab = middle<r 0<ab
        in
        ∣ q
        , lift 0<q
        , nnMul-lower-from-product x y q
            (a , b , a∈Lx , b∈Ly , 0<a , 0<b , q<ab)
        ∣₁)
      (∃lower>0 x 0<x)
      (∃lower>0 y 0<y)

  *𝔻-Pres>0 :
    (x y : DedekindCompletion ℓᴾ) →
    x >0𝔻 →
    y >0𝔻 →
    (x *𝔻 y) >0𝔻
  *𝔻-Pres>0 x y 0<x 0<y =
    subst _>0𝔻 (sym (*𝔻-of-≥0 x y 0≤x 0≤y))
      (nnMul-Pres>0 x y 0≤x 0≤y 0<x 0<y)
    where
    0≤x : x ≥0
    0≤x = >0→≥0 x 0<x

    0≤y : y ≥0
    0≤y = >0→≥0 y 0<y

  Diff>0𝔻 :
    (x y : DedekindCompletion ℓᴾ) →
    x <D y →
    (y +𝔻 (-𝔻 x)) >0𝔻
  Diff>0𝔻 x y x<y =
    transport
      (λ i → +-invR x i <D y +𝔻 (-𝔻 x))
      (+-monoR-< x y (-𝔻 x) x<y)

  Diff>0𝔻→< :
    (x y : DedekindCompletion ℓᴾ) →
    (y +𝔻 (-𝔻 x)) >0𝔻 →
    x <D y
  Diff>0𝔻→< x y 0<y-x =
    subst2 _<D_
      (+-idL x)
      (minus-plus-cancelR y x)
      (+-monoR-< 0𝔻 (y +𝔻 (-𝔻 x)) x 0<y-x)

  *𝔻-right-difference :
    (x y z : DedekindCompletion ℓᴾ) →
    (y +𝔻 (-𝔻 x)) *𝔻 z ≡ (y *𝔻 z) +𝔻 (-𝔻 (x *𝔻 z))
  *𝔻-right-difference x y z =
    *𝔻-distribR y (-𝔻 x) z ∙
    cong₂ _+𝔻_ refl (*𝔻-negL x z)

  *𝔻-rPosPres< :
    (x y z : DedekindCompletion ℓᴾ) →
    z >0𝔻 →
    x <D y →
    (x *𝔻 z) <D (y *𝔻 z)
  *𝔻-rPosPres< x y z 0<z x<y =
    Diff>0𝔻→< (x *𝔻 z) (y *𝔻 z)
      (subst _>0𝔻 (*𝔻-right-difference x y z)
        (*𝔻-Pres>0 (y +𝔻 (-𝔻 x)) z (Diff>0𝔻 x y x<y) 0<z))

  lower>0→>0 :
    (x : DedekindCompletion ℓᴾ) →
    (q : K) →
    0r < q →
    q ∈ lower x →
    x >0𝔻
  lower>0→>0 x q 0<q q∈Lx =
    <D-trans 0𝔻 (K→𝔻 ℓᴾ q) x
      (K→<-pres 0r q 0<q)
      (lower→K< x q q∈Lx)

  posSum→pos∨pos :
    (x y : DedekindCompletion ℓᴾ) →
    (x +𝔻 y) >0𝔻 →
    (x >0𝔻) L.⊔′ (y >0𝔻)
  posSum→pos∨pos x y =
    Prop.rec squash₁
      (λ (q , 0<q , q∈Lxy) →
        Prop.rec squash₁
          (λ (r , s , r∈Lx , s∈Ly , q<r+s) →
            let
              0<r+s : 0r < r + s
              0<r+s =
                <-trans (Lift.lower 0<q) q<r+s
            in
            Sum.elim
              (λ 0<r → ∣ Sum.inl (lower>0→>0 x r 0<r r∈Lx) ∣₁)
              (λ 0<s → ∣ Sum.inr (lower>0→>0 y s 0<s s∈Ly) ∣₁)
              (positive-sum-split r s 0<r+s))
          q∈Lxy)
