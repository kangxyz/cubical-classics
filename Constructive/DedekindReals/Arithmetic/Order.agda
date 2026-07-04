{-

Order compatibility for constructive Dedekind-real arithmetic.

These lemmas are the remaining non-classical order facts needed to package
Dedekind reals as an ordered commutative ring.  The proofs use the located cut
structure and propositional truncation, but no trichotomy for reals.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindReals.Arithmetic.Order where

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

open import Constructive.DedekindReals
open import Constructive.DedekindReals.Arithmetic.Base
open import Constructive.DedekindReals.Arithmetic.AdditiveGroup
open import Constructive.DedekindReals.Arithmetic.Distributivity
open import Constructive.DedekindReals.Arithmetic.Negation
import Constructive.Rationals as ℚExtra


module OrderProperties {ℓ : Level} where
  open Order {ℓ}
  open RationalEmbedding {ℓ}
  open Algebra {ℓ}
  open Addition {ℓ}
  open NonNegativeMultiplication {ℓ}
  open Multiplication {ℓ}
  open AdditiveGroup {ℓ}
  open NegationProperties {ℓ}
  open MultiplicationDistributivity {ℓ}

  _>0 : DedekindReal ℓ → Type ℓ
  x >0 = 0𝔻 < x

  infix 4 _>0

  >0→≥0 :
    (x : DedekindReal ℓ) →
    x >0 →
    x ≥0
  >0→≥0 x = <→≤ 0𝔻 x

  ∃lower>0 :
    (x : DedekindReal ℓ) →
    x >0 →
    ∥ Σ[ q ∈ ℚ ] (ℚExtra.0ℚ ℚOrder.< q) × (q ∈ lower x) ∥₁
  ∃lower>0 x =
    Prop.rec squash₁
      (λ (q , 0<q , q∈Lx) →
        ∣ q , Lift.lower 0<q , q∈Lx ∣₁)

  nnMul-Pres>0 :
    (x y : DedekindReal ℓ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    x >0 →
    y >0 →
    (nnMul x y 0≤x 0≤y) >0
  nnMul-Pres>0 x y 0≤x 0≤y 0<x 0<y =
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
      (∃lower>0 x 0<x)
      (∃lower>0 y 0<y)

  *-Pres>0 :
    (x y : DedekindReal ℓ) →
    x >0 →
    y >0 →
    (x * y) >0
  *-Pres>0 x y 0<x 0<y =
    subst _>0 (sym (*-of-≥0 x y 0≤x 0≤y))
      (nnMul-Pres>0 x y 0≤x 0≤y 0<x 0<y)
    where
    0≤x : x ≥0
    0≤x = >0→≥0 x 0<x

    0≤y : y ≥0
    0≤y = >0→≥0 y 0<y

  Diff>0 :
    (x y : DedekindReal ℓ) →
    x < y →
    (y + (- x)) >0
  Diff>0 x y x<y =
    transport
      (λ i → +-invR x i < y + (- x))
      (+-monoR-< x y (- x) x<y)

  Diff>0→< :
    (x y : DedekindReal ℓ) →
    (y + (- x)) >0 →
    x < y
  Diff>0→< x y 0<y-x =
    subst2 _<_
      (+-idL x)
      (minus-plus-cancelR y x)
      (+-monoR-< 0𝔻 (y + (- x)) x 0<y-x)

  *-right-difference :
    (x y z : DedekindReal ℓ) →
    (y + (- x)) * z ≡ (y * z) + (- (x * z))
  *-right-difference x y z =
    *-distribR y (- x) z ∙
    cong₂ _+_ refl (*-negL x z)

  *-rPosPres< :
    (x y z : DedekindReal ℓ) →
    z >0 →
    x < y →
    (x * z) < (y * z)
  *-rPosPres< x y z 0<z x<y =
    Diff>0→< (x * z) (y * z)
      (subst _>0 (*-right-difference x y z)
        (*-Pres>0 (y + (- x)) z (Diff>0 x y x<y) 0<z))

  lower>0→>0 :
    (x : DedekindReal ℓ) →
    (q : ℚ) →
    ℚExtra.0ℚ ℚOrder.< q →
    q ∈ lower x →
    x >0
  lower>0→>0 x q 0<q q∈Lx =
    <-trans 0𝔻 (ℚ→𝔻 ℓ q) x
      (ℚ→<-pres ℚExtra.0ℚ q 0<q)
      (lower→ℚ< x q q∈Lx)

  posSum→pos∨pos :
    (x y : DedekindReal ℓ) →
    (x + y) >0 →
    (x >0) L.⊔′ (y >0)
  posSum→pos∨pos x y =
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
              (λ 0<r → ∣ Sum.inl (lower>0→>0 x r 0<r r∈Lx) ∣₁)
              (λ 0<s → ∣ Sum.inr (lower>0→>0 y s 0<s s∈Ly) ∣₁)
              (ℚOrder.0<+ r s 0<r+s))
          q∈Lxy)
