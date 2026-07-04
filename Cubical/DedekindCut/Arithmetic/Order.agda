{-

Order compatibility for constructive Dedekind-cut arithmetic.

These lemmas are the remaining non-classical order facts needed to package
Dedekind cuts as an ordered commutative ring.  The proofs use the located cut
structure and propositional truncation, but no trichotomy for reals.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.DedekindCut.Arithmetic.Order where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Rationals using (ℚ)
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

import Cubical.Functions.Logic as L

open import Cubical.DedekindCut
open import Cubical.DedekindCut.Arithmetic
open import Cubical.DedekindCut.Arithmetic.AdditiveGroup
open import Cubical.DedekindCut.Arithmetic.Distributivity
open import Cubical.DedekindCut.Arithmetic.Negation
import Cubical.Rationals as ℚExtra


module SignedOrder {ℓ : Level} where
  open Order {ℓ}
  open RationalEmbeddingAt {ℓ}
  open Algebra {ℓ}
  open Addition {ℓ}
  open NonnegativeMultiplication {ℓ}
  open SignedMultiplication {ℓ}
  open AdditiveGroup {ℓ}
  open MultiplicationNegation {ℓ}
  open SignedDistributivity {ℓ}

  Positive : DedekindCut ℓ → Type ℓ
  Positive x = 0D < x

  positive→nonnegative :
    (x : DedekindCut ℓ) →
    Positive x →
    Nonnegative x
  positive→nonnegative x = <→≤ 0D x

  positive-rational-lower :
    (x : DedekindCut ℓ) →
    Positive x →
    ∥ Σ[ q ∈ ℚ ] (ℚExtra.0ℚ ℚOrder.< q) × (q ∈ lower x) ∥₁
  positive-rational-lower x =
    Prop.rec squash₁
      (λ (q , 0<q , q∈Lx) →
        ∣ q , Lift.lower 0<q , q∈Lx ∣₁)

  nnMul-positive :
    (x y : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    (0≤y : Nonnegative y) →
    Positive x →
    Positive y →
    Positive (nnMul x y 0≤x 0≤y)
  nnMul-positive x y 0≤x 0≤y 0<x 0<y =
    Prop.rec2 squash₁
      (λ (a , 0<a , a∈Lx) (b , 0<b , b∈Ly) →
        let
          ab = a ℚ.· b
          0<ab = ℚExtra.mul-positive {a = a} {b = b} 0<a 0<b
          q = ℚExtra.middle ℚExtra.0ℚ ab
          0<q = ℚExtra.middle>l {p = ℚExtra.0ℚ} {q = ab} 0<ab
          q<ab = ℚExtra.middle<r {p = ℚExtra.0ℚ} {q = ab} 0<ab
        in
        ∣ q
        , lift 0<q
        , nnMul-lower-from-product x y q
            (a , b , a∈Lx , b∈Ly , 0<a , 0<b , q<ab)
        ∣₁)
      (positive-rational-lower x 0<x)
      (positive-rational-lower y 0<y)

  *-positive :
    (x y : DedekindCut ℓ) →
    Positive x →
    Positive y →
    Positive (x * y)
  *-positive x y 0<x 0<y =
    subst Positive (sym (*-of-nonnegative x y 0≤x 0≤y))
      (nnMul-positive x y 0≤x 0≤y 0<x 0<y)
    where
    0≤x : Nonnegative x
    0≤x = positive→nonnegative x 0<x

    0≤y : Nonnegative y
    0≤y = positive→nonnegative y 0<y

  difference-positive :
    (x y : DedekindCut ℓ) →
    x < y →
    Positive (y + (- x))
  difference-positive x y x<y =
    transport
      (λ i → +-invR x i < y + (- x))
      (+-monoR-< x y (- x) x<y)

  positive-difference→< :
    (x y : DedekindCut ℓ) →
    Positive (y + (- x)) →
    x < y
  positive-difference→< x y 0<y-x =
    subst2 _<_
      (+-idL x)
      (minus-plus-cancelR y x)
      (+-monoR-< 0D (y + (- x)) x 0<y-x)

  *-right-difference :
    (x y z : DedekindCut ℓ) →
    (y + (- x)) * z ≡ (y * z) + (- (x * z))
  *-right-difference x y z =
    *-distribR y (- x) z ∙
    cong₂ _+_ refl (*-negL x z)

  *-monoR-<-positive :
    (x y z : DedekindCut ℓ) →
    Positive z →
    x < y →
    (x * z) < (y * z)
  *-monoR-<-positive x y z 0<z x<y =
    positive-difference→< (x * z) (y * z)
      (subst Positive (*-right-difference x y z)
        (*-positive (y + (- x)) z (difference-positive x y x<y) 0<z))

  positive-of-rational-lower :
    (x : DedekindCut ℓ) →
    (q : ℚ) →
    ℚExtra.0ℚ ℚOrder.< q →
    q ∈ lower x →
    Positive x
  positive-of-rational-lower x q 0<q q∈Lx =
    <-trans 0D (ℚ→DedekindCutAt ℓ q) x
      (ℚ→<-pres ℚExtra.0ℚ q 0<q)
      (lower→ℚ< x q q∈Lx)

  positive-sum-split :
    (x y : DedekindCut ℓ) →
    Positive (x + y) →
    Positive x L.⊔′ Positive y
  positive-sum-split x y =
    Prop.rec squash₁
      (λ (q , 0<q , q∈Lxy) →
        Prop.rec squash₁
          (λ (r , s , r∈Lx , s∈Ly , q<r+s) →
            let
              0<r+s : ℚExtra.0ℚ ℚOrder.< r ℚ.+ s
              0<r+s =
                ℚOrder.isTrans< ℚExtra.0ℚ q (r ℚ.+ s)
                  (Lift.lower 0<q)
                  q<r+s
            in
            Sum.elim
              (λ 0<r → ∣ Sum.inl (positive-of-rational-lower x r 0<r r∈Lx) ∣₁)
              (λ 0<s → ∣ Sum.inr (positive-of-rational-lower y s 0<s s∈Ly) ∣₁)
              (ℚOrder.0<+ r s 0<r+s))
          q∈Lxy)
