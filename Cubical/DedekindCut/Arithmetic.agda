{-

Constructive arithmetic operations on Dedekind cuts.

This file is the beginning of the ordered-field structure.  It currently
contains addition as a Dedekind cut; group and field laws are added
incrementally.

-}
{-# OPTIONS --safe #-}
module Cubical.DedekindCut.Arithmetic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Rationals using (ℚ)
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Cubical.DedekindCut
import Cubical.Rationals as ℚExtra


module Addition {ℓ : Level} where
  open Order {ℓ}
  open Approximation {ℓ}
  open Algebra {ℓ}

  0D : DedekindCut ℓ
  0D = ℚ→DedekindCutAt ℓ ℚExtra.0ℚ

  1D : DedekindCut ℓ
  1D = ℚ→DedekindCutAt ℓ ℚExtra.1ℚ

  addLower : DedekindCut ℓ → DedekindCut ℓ → ℚPred ℓ
  addLower x y q =
    ∥ Σ[ r ∈ ℚ ] Σ[ s ∈ ℚ ]
      (r ∈ lower x) ×
      (s ∈ lower y) ×
      (q ℚOrder.< r ℚ.+ s) ∥₁ ,
    squash₁

  addUpper : DedekindCut ℓ → DedekindCut ℓ → ℚPred ℓ
  addUpper x y q =
    ∥ Σ[ r ∈ ℚ ] Σ[ s ∈ ℚ ]
      (r ∈ upper x) ×
      (s ∈ upper y) ×
      (r ℚ.+ s ℚOrder.< q) ∥₁ ,
    squash₁

  add-is-cut :
    (x y : DedekindCut ℓ) →
    isDedekindCut (addLower x y) (addUpper x y)
  add-is-cut x y .isDedekindCut.lower-inhabited =
    Prop.rec2 squash₁
      (λ (p , p∈Lx) (q , q∈Ly) →
        ∣ (p ℚ.+ q) ℚ.- ℚExtra.1ℚ
        , ∣ p , q , p∈Lx , q∈Ly , ℚExtra.q-1<q (p ℚ.+ q) ∣₁
        ∣₁)
      (lower-inhabited x)
      (lower-inhabited y)
  add-is-cut x y .isDedekindCut.upper-inhabited =
    Prop.rec2 squash₁
      (λ (p , p∈Ux) (q , q∈Uy) →
        ∣ (p ℚ.+ q) ℚ.+ ℚExtra.1ℚ
        , ∣ p , q , p∈Ux , q∈Uy , ℚExtra.q<q+1 (p ℚ.+ q) ∣₁
        ∣₁)
      (upper-inhabited x)
      (upper-inhabited y)
  add-is-cut x y .isDedekindCut.lower-closed =
    λ p q p<q →
      Prop.rec squash₁
        (λ (r , s , r∈Lx , s∈Ly , q<r+s) →
          ∣ r , s , r∈Lx , s∈Ly
          , ℚOrder.isTrans< p q (r ℚ.+ s) p<q q<r+s
          ∣₁)
  add-is-cut x y .isDedekindCut.upper-closed =
    λ p q p<q →
      Prop.rec squash₁
        (λ (r , s , r∈Ux , s∈Uy , r+s<p) →
          ∣ r , s , r∈Ux , s∈Uy
          , ℚOrder.isTrans< (r ℚ.+ s) p q r+s<p p<q
          ∣₁)
  add-is-cut x y .isDedekindCut.lower-rounded =
    λ q →
      Prop.rec squash₁
        (λ (r , s , r∈Lx , s∈Ly , q<r+s) →
          Prop.rec squash₁
            (λ (m , q<m , m<r+s) →
              ∣ m , q<m , ∣ r , s , r∈Lx , s∈Ly , m<r+s ∣₁ ∣₁)
            (ℚExtra.dense {p = q} {q = r ℚ.+ s} q<r+s))
  add-is-cut x y .isDedekindCut.upper-rounded =
    λ q →
      Prop.rec squash₁
        (λ (r , s , r∈Ux , s∈Uy , r+s<q) →
          Prop.rec squash₁
            (λ (m , r+s<m , m<q) →
              ∣ m , m<q , ∣ r , s , r∈Ux , s∈Uy , r+s<m ∣₁ ∣₁)
            (ℚExtra.dense {p = r ℚ.+ s} {q = q} r+s<q))
  add-is-cut x y .isDedekindCut.disjoint =
    λ q →
      Prop.rec2 Empty.isProp⊥
        (λ (lx , ly , lx∈Lx , ly∈Ly , q<lx+ly)
           (ux , uy , ux∈Ux , uy∈Uy , ux+uy<q) →
          let
            lx<ux : lx ℚOrder.< ux
            lx<ux = lower<upper x lx ux lx∈Lx ux∈Ux

            ly<uy : ly ℚOrder.< uy
            ly<uy = lower<upper y ly uy ly∈Ly uy∈Uy

            lx+ly<ux+uy : lx ℚ.+ ly ℚOrder.< ux ℚ.+ uy
            lx+ly<ux+uy =
              ℚOrder.<Monotone+ lx ux ly uy lx<ux ly<uy

            q<q : q ℚOrder.< q
            q<q =
              ℚOrder.isTrans< q (lx ℚ.+ ly) q q<lx+ly
                (ℚOrder.isTrans< (lx ℚ.+ ly) (ux ℚ.+ uy) q
                  lx+ly<ux+uy ux+uy<q)
          in
          ℚOrder.isIrrefl< q q<q)
  add-is-cut x y .isDedekindCut.located =
    located-add
    where
    q-p : ℚ → ℚ → ℚ
    q-p p q = q ℚ.- p

    0<q-p :
      (p q : ℚ) →
      p ℚOrder.< q →
      ℚExtra.0ℚ ℚOrder.< q-p p q
    0<q-p p q p<q =
      ℚExtra.diff-positive {p = p} {q = q} p<q

    η : ℚ → ℚ → ℚ
    η p q = q-p p q ℚ.· ℚExtra.1/2

    0<η :
      (p q : ℚ) →
      p ℚOrder.< q →
      ℚExtra.0ℚ ℚOrder.< η p q
    0<η p q p<q =
      ℚExtra.positive-half {ε = q-p p q} (0<q-p p q p<q)

    η+η≡q-p :
      (p q : ℚ) →
      η p q ℚ.+ η p q ≡ q-p p q
    η+η≡q-p p q = ℚExtra.half+half (q-p p q)

    located-from-close :
      (p q : ℚ) →
      p ℚOrder.< q →
      CloseBounds x (η p q) →
      CloseBounds y (η p q) →
      ∥ (p ∈ addLower x y) ⊎ (q ∈ addUpper x y) ∥₁
    located-from-close p q p<q
      (lx , ux , lx∈Lx , ux∈Ux , _ , ux<lx+η)
      (ly , uy , ly∈Ly , uy∈Uy , _ , uy<ly+η)
      with p ℚOrder.≟ (lx ℚ.+ ly)
    ... | ℚOrder.lt p<lx+ly =
      ∣ Sum.inl ∣ lx , ly , lx∈Lx , ly∈Ly , p<lx+ly ∣₁ ∣₁
    ... | ℚOrder.eq p≡lx+ly =
      ∣ Sum.inr
          ∣ ux , uy , ux∈Ux , uy∈Uy
          , ℚExtra.sum-close-upper<
              lx ly ux uy (η p q) p q
              ux<lx+η
              uy<ly+η
              (ℚOrder.≡Weaken≤ (lx ℚ.+ ly) p (sym p≡lx+ly))
              (η+η≡q-p p q)
          ∣₁
      ∣₁
    ... | ℚOrder.gt lx+ly<p =
      ∣ Sum.inr
          ∣ ux , uy , ux∈Ux , uy∈Uy
          , ℚExtra.sum-close-upper<
              lx ly ux uy (η p q) p q
              ux<lx+η
              uy<ly+η
              (ℚOrder.<Weaken≤ (lx ℚ.+ ly) p lx+ly<p)
              (η+η≡q-p p q)
          ∣₁
      ∣₁

    located-add :
      (p q : ℚ) →
      p ℚOrder.< q →
      ∥ (p ∈ addLower x y) ⊎ (q ∈ addUpper x y) ∥₁
    located-add p q p<q =
      Prop.rec2 squash₁ (located-from-close p q p<q)
        (close-bounds x (η p q) (0<η p q p<q))
        (close-bounds y (η p q) (0<η p q p<q))

  _+_ : DedekindCut ℓ → DedekindCut ℓ → DedekindCut ℓ
  (x + y) .lower = addLower x y
  (x + y) .upper = addUpper x y
  (x + y) .is-cut = add-is-cut x y

  infixl 6 _+_

  +-comm : (x y : DedekindCut ℓ) → x + y ≡ y + x
  +-comm x y =
    cutExt (x + y) (y + x)
      (lower⊆ x y)
      (lower⊆ y x)
      (upper⊆ x y)
      (upper⊆ y x)
    where
    lower⊆ :
      (x y : DedekindCut ℓ) →
      addLower x y ⊆ addLower y x
    lower⊆ x y q =
      Prop.rec squash₁
        (λ (r , s , r∈Lx , s∈Ly , q<r+s) →
          ∣ s , r , s∈Ly , r∈Lx
          , subst (λ t → q ℚOrder.< t) (ℚ.+Comm r s) q<r+s
          ∣₁)

    upper⊆ :
      (x y : DedekindCut ℓ) →
      addUpper x y ⊆ addUpper y x
    upper⊆ x y q =
      Prop.rec squash₁
        (λ (r , s , r∈Ux , s∈Uy , r+s<q) →
          ∣ s , r , s∈Uy , r∈Ux
          , subst (λ t → t ℚOrder.< q) (ℚ.+Comm r s) r+s<q
          ∣₁)

  +-assoc :
    (x y z : DedekindCut ℓ) →
    x + (y + z) ≡ (x + y) + z
  +-assoc x y z =
    cutExt (x + (y + z)) ((x + y) + z)
      (lower⊆₁ x y z)
      (lower⊆₂ x y z)
      (upper⊆₁ x y z)
      (upper⊆₂ x y z)
    where
    lower⊆₁ :
      (x y z : DedekindCut ℓ) →
      addLower x (y + z) ⊆ addLower (x + y) z
    lower⊆₁ x y z q =
      Prop.rec squash₁
        (λ (r , s , r∈Lx , s∈Ly+z , q<r+s) →
          Prop.rec squash₁
            (λ (t , u , t∈Ly , u∈Lz , s<t+u) →
              let
                r+s<r+tu : r ℚ.+ s ℚOrder.< r ℚ.+ (t ℚ.+ u)
                r+s<r+tu = ℚOrder.<-o+ s (t ℚ.+ u) r s<t+u

                q<r+tu : q ℚOrder.< r ℚ.+ (t ℚ.+ u)
                q<r+tu =
                  ℚOrder.isTrans< q (r ℚ.+ s) (r ℚ.+ (t ℚ.+ u))
                    q<r+s r+s<r+tu

                q<rt+u : q ℚOrder.< (r ℚ.+ t) ℚ.+ u
                q<rt+u =
                  subst (λ v → q ℚOrder.< v) (ℚ.+Assoc r t u) q<r+tu

                q-u<rt : q ℚ.- u ℚOrder.< r ℚ.+ t
                q-u<rt = ℚExtra.<+→diff< q (r ℚ.+ t) u q<rt+u
              in
              Prop.rec squash₁
                (λ (a , q-u<a , a<rt) →
                  ∣ a , u
                  , ∣ r , t , r∈Lx , t∈Ly , a<rt ∣₁
                  , u∈Lz
                  , ℚExtra.diff<→right+< q a u q-u<a
                  ∣₁)
                (ℚExtra.dense {p = q ℚ.- u} {q = r ℚ.+ t} q-u<rt))
            s∈Ly+z)

    lower⊆₂ :
      (x y z : DedekindCut ℓ) →
      addLower (x + y) z ⊆ addLower x (y + z)
    lower⊆₂ x y z q =
      Prop.rec squash₁
        (λ (a , u , a∈Lx+y , u∈Lz , q<a+u) →
          Prop.rec squash₁
            (λ (r , t , r∈Lx , t∈Ly , a<rt) →
              let
                a+u<rt+u : a ℚ.+ u ℚOrder.< (r ℚ.+ t) ℚ.+ u
                a+u<rt+u = ℚOrder.<-+o a (r ℚ.+ t) u a<rt

                q<rt+u : q ℚOrder.< (r ℚ.+ t) ℚ.+ u
                q<rt+u =
                  ℚOrder.isTrans< q (a ℚ.+ u) ((r ℚ.+ t) ℚ.+ u)
                    q<a+u a+u<rt+u

                q<r+tu : q ℚOrder.< r ℚ.+ (t ℚ.+ u)
                q<r+tu =
                  subst (λ v → q ℚOrder.< v) (sym (ℚ.+Assoc r t u)) q<rt+u

                q<tu+r : q ℚOrder.< (t ℚ.+ u) ℚ.+ r
                q<tu+r =
                  subst (λ v → q ℚOrder.< v) (ℚ.+Comm r (t ℚ.+ u)) q<r+tu

                q-r<tu : q ℚ.- r ℚOrder.< t ℚ.+ u
                q-r<tu = ℚExtra.<+→diff< q (t ℚ.+ u) r q<tu+r
              in
              Prop.rec squash₁
                (λ (s , q-r<s , s<tu) →
                  ∣ r , s
                  , r∈Lx
                  , ∣ t , u , t∈Ly , u∈Lz , s<tu ∣₁
                  , ℚExtra.diff<→shift< r q s q-r<s
                  ∣₁)
                (ℚExtra.dense {p = q ℚ.- r} {q = t ℚ.+ u} q-r<tu))
            a∈Lx+y)

    upper⊆₁ :
      (x y z : DedekindCut ℓ) →
      addUpper x (y + z) ⊆ addUpper (x + y) z
    upper⊆₁ x y z q =
      Prop.rec squash₁
        (λ (r , s , r∈Ux , s∈Uy+z , r+s<q) →
          Prop.rec squash₁
            (λ (t , u , t∈Uy , u∈Uz , t+u<s) →
              let
                r+tu<r+s : r ℚ.+ (t ℚ.+ u) ℚOrder.< r ℚ.+ s
                r+tu<r+s = ℚOrder.<-o+ (t ℚ.+ u) s r t+u<s

                rt+u<r+s : (r ℚ.+ t) ℚ.+ u ℚOrder.< r ℚ.+ s
                rt+u<r+s =
                  subst (λ v → v ℚOrder.< r ℚ.+ s) (ℚ.+Assoc r t u) r+tu<r+s

                rt+u<q : (r ℚ.+ t) ℚ.+ u ℚOrder.< q
                rt+u<q =
                  ℚOrder.isTrans< ((r ℚ.+ t) ℚ.+ u) (r ℚ.+ s) q
                    rt+u<r+s r+s<q

                rt<q-u : r ℚ.+ t ℚOrder.< q ℚ.- u
                rt<q-u = ℚExtra.right+<→diff< (r ℚ.+ t) u q rt+u<q
              in
              Prop.rec squash₁
                (λ (a , rt<a , a<q-u) →
                  ∣ a , u
                  , ∣ r , t , r∈Ux , t∈Uy , rt<a ∣₁
                  , u∈Uz
                  , ℚExtra.diff-right<→+< a u q a<q-u
                  ∣₁)
                (ℚExtra.dense {p = r ℚ.+ t} {q = q ℚ.- u} rt<q-u))
            s∈Uy+z)

    upper⊆₂ :
      (x y z : DedekindCut ℓ) →
      addUpper (x + y) z ⊆ addUpper x (y + z)
    upper⊆₂ x y z q =
      Prop.rec squash₁
        (λ (a , u , a∈Ux+y , u∈Uz , a+u<q) →
          Prop.rec squash₁
            (λ (r , t , r∈Ux , t∈Uy , r+t<a) →
              let
                rt+u<a+u : (r ℚ.+ t) ℚ.+ u ℚOrder.< a ℚ.+ u
                rt+u<a+u = ℚOrder.<-+o (r ℚ.+ t) a u r+t<a

                rt+u<q : (r ℚ.+ t) ℚ.+ u ℚOrder.< q
                rt+u<q =
                  ℚOrder.isTrans< ((r ℚ.+ t) ℚ.+ u) (a ℚ.+ u) q
                    rt+u<a+u a+u<q

                r+tu<q : r ℚ.+ (t ℚ.+ u) ℚOrder.< q
                r+tu<q =
                  subst (λ v → v ℚOrder.< q) (sym (ℚ.+Assoc r t u)) rt+u<q

                tu+r<q : (t ℚ.+ u) ℚ.+ r ℚOrder.< q
                tu+r<q =
                  subst (λ v → v ℚOrder.< q) (ℚ.+Comm r (t ℚ.+ u)) r+tu<q

                tu<q-r : t ℚ.+ u ℚOrder.< q ℚ.- r
                tu<q-r = ℚExtra.right+<→diff< (t ℚ.+ u) r q tu+r<q
              in
              Prop.rec squash₁
                (λ (s , tu<s , s<q-r) →
                  ∣ r , s
                  , r∈Ux
                  , ∣ t , u , t∈Uy , u∈Uz , tu<s ∣₁
                  , subst (λ v → v ℚOrder.< q)
                      (ℚ.+Comm s r)
                      (ℚExtra.diff-right<→+< s r q s<q-r)
                  ∣₁)
                (ℚExtra.dense {p = t ℚ.+ u} {q = q ℚ.- r} tu<q-r))
            a∈Ux+y)

  +-idR : (x : DedekindCut ℓ) → x + 0D ≡ x
  +-idR x =
    cutExt (x + 0D) x
      lower⊆
      lower⊇
      upper⊆
      upper⊇
    where
    lower⊆ : addLower x 0D ⊆ lower x
    lower⊆ q =
      Prop.rec (isProp∈ (lower x) q)
        (λ (r , s , r∈Lx , s<0 , q<r+s) →
          let
            r+s<r+0 : r ℚ.+ s ℚOrder.< r ℚ.+ ℚExtra.0ℚ
            r+s<r+0 = ℚOrder.<-o+ s ℚExtra.0ℚ r (Lift.lower s<0)

            r+s<r : r ℚ.+ s ℚOrder.< r
            r+s<r =
              subst (λ v → r ℚ.+ s ℚOrder.< v)
                (ℚ.+IdR r)
                r+s<r+0

            q<r : q ℚOrder.< r
            q<r = ℚOrder.isTrans< q (r ℚ.+ s) r q<r+s r+s<r
          in
          lower-closed x q r q<r r∈Lx)

    lower⊇ : lower x ⊆ addLower x 0D
    lower⊇ q q∈Lx =
      Prop.rec squash₁
        (λ (r , q<r , r∈Lx) →
          let
            q<0+r : q ℚOrder.< ℚExtra.0ℚ ℚ.+ r
            q<0+r =
              subst (λ v → q ℚOrder.< v)
                (sym (ℚ.+IdL r))
                q<r

            q-r<0 : q ℚ.- r ℚOrder.< ℚExtra.0ℚ
            q-r<0 = ℚExtra.<+→diff< q ℚExtra.0ℚ r q<0+r
          in
          Prop.rec squash₁
            (λ (s , q-r<s , s<0) →
              ∣ r , s
              , r∈Lx
              , lift s<0
              , ℚExtra.diff<→shift< r q s q-r<s
              ∣₁)
            (ℚExtra.dense {p = q ℚ.- r} {q = ℚExtra.0ℚ} q-r<0))
        (lower-rounded x q q∈Lx)

    upper⊆ : addUpper x 0D ⊆ upper x
    upper⊆ q =
      Prop.rec (isProp∈ (upper x) q)
        (λ (r , s , r∈Ux , 0<s , r+s<q) →
          let
            r+0<r+s : r ℚ.+ ℚExtra.0ℚ ℚOrder.< r ℚ.+ s
            r+0<r+s = ℚOrder.<-o+ ℚExtra.0ℚ s r (Lift.lower 0<s)

            r<r+s : r ℚOrder.< r ℚ.+ s
            r<r+s =
              subst (λ v → v ℚOrder.< r ℚ.+ s)
                (ℚ.+IdR r)
                r+0<r+s

            r<q : r ℚOrder.< q
            r<q = ℚOrder.isTrans< r (r ℚ.+ s) q r<r+s r+s<q
          in
          upper-closed x r q r<q r∈Ux)

    upper⊇ : upper x ⊆ addUpper x 0D
    upper⊇ q q∈Ux =
      Prop.rec squash₁
        (λ (r , r<q , r∈Ux) →
          Prop.rec squash₁
            (λ (s , 0<s , s<q-r) →
              ∣ r , s
              , r∈Ux
              , lift 0<s
              , subst (λ v → v ℚOrder.< q)
                  (ℚ.+Comm s r)
                  (ℚExtra.diff-right<→+< s r q s<q-r)
              ∣₁)
            (ℚExtra.dense
              {p = ℚExtra.0ℚ}
              {q = q ℚ.- r}
              (ℚExtra.diff-positive {p = r} {q = q} r<q)))
        (upper-rounded x q q∈Ux)

  +-idL : (x : DedekindCut ℓ) → 0D + x ≡ x
  +-idL x = +-comm 0D x ∙ +-idR x

  +-invR : (x : DedekindCut ℓ) → x + (- x) ≡ 0D
  +-invR x =
    cutExt (x + (- x)) 0D
      lower⊆
      lower⊇
      upper⊆
      upper⊇
    where
    lower⊆ : addLower x (- x) ⊆ lower 0D
    lower⊆ q =
      Prop.rec (isProp∈ (lower 0D) q)
        (λ (r , s , r∈Lx , -s∈Ux , q<r+s) →
          let
            r<-s : r ℚOrder.< ℚ.- s
            r<-s = lower<upper x r (ℚ.- s) r∈Lx -s∈Ux

            r+s<-s+s : r ℚ.+ s ℚOrder.< (ℚ.- s) ℚ.+ s
            r+s<-s+s = ℚOrder.<-+o r (ℚ.- s) s r<-s

            r+s<0 : r ℚ.+ s ℚOrder.< ℚExtra.0ℚ
            r+s<0 =
              subst (λ v → r ℚ.+ s ℚOrder.< v)
                (ℚ.+InvL s)
                r+s<-s+s

            q<0 : q ℚOrder.< ℚExtra.0ℚ
            q<0 =
              ℚOrder.isTrans< q (r ℚ.+ s) ℚExtra.0ℚ q<r+s r+s<0
          in
          lift q<0)

    lower⊇ : lower 0D ⊆ addLower x (- x)
    lower⊇ q q<0 =
      Prop.rec squash₁
        (λ (p , u , p∈Lx , u∈Ux , _ , u<p-q) →
          ∣ p , ℚ.- u
          , p∈Lx
          , subst (λ v → v ∈ upper x) (sym (ℚ.-Invol u)) u∈Ux
          , ℚExtra.swap-sub< p q u u<p-q
          ∣₁)
        (close-bounds x (ℚ.- q) (ℚExtra.neg-positive {q = q} (Lift.lower q<0)))

    upper⊆ : addUpper x (- x) ⊆ upper 0D
    upper⊆ q =
      Prop.rec (isProp∈ (upper 0D) q)
        (λ (r , s , r∈Ux , -s∈Lx , r+s<q) →
          let
            -s<r : ℚ.- s ℚOrder.< r
            -s<r = lower<upper x (ℚ.- s) r -s∈Lx r∈Ux

            -s+s<r+s : (ℚ.- s) ℚ.+ s ℚOrder.< r ℚ.+ s
            -s+s<r+s = ℚOrder.<-+o (ℚ.- s) r s -s<r

            0<r+s : ℚExtra.0ℚ ℚOrder.< r ℚ.+ s
            0<r+s =
              subst (λ v → v ℚOrder.< r ℚ.+ s)
                (ℚ.+InvL s)
                -s+s<r+s

            0<q : ℚExtra.0ℚ ℚOrder.< q
            0<q =
              ℚOrder.isTrans< ℚExtra.0ℚ (r ℚ.+ s) q 0<r+s r+s<q
          in
          lift 0<q)

    upper⊇ : upper 0D ⊆ addUpper x (- x)
    upper⊇ q 0<q =
      Prop.rec squash₁
        (λ (p , u , p∈Lx , u∈Ux , _ , u<p+q) →
          let
            u<q+p : u ℚOrder.< q ℚ.+ p
            u<q+p =
              subst (λ v → u ℚOrder.< v)
                (ℚ.+Comm p q)
                u<p+q

            u-p<q : u ℚ.- p ℚOrder.< q
            u-p<q = ℚExtra.<+→diff< u q p u<q+p
          in
          ∣ u , ℚ.- p
          , u∈Ux
          , subst (λ v → v ∈ lower x) (sym (ℚ.-Invol p)) p∈Lx
          , u-p<q
          ∣₁)
        (close-bounds x q (Lift.lower 0<q))

  +-invL : (x : DedekindCut ℓ) → (- x) + x ≡ 0D
  +-invL x = +-comm (- x) x ∙ +-invR x

  +-monoR-≤ :
    (x y z : DedekindCut ℓ) →
    x ≤ y →
    x + z ≤ y + z
  +-monoR-≤ x y z x≤y q =
    Prop.rec squash₁
      (λ (r , s , r∈Lx , s∈Lz , q<r+s) →
        ∣ r , s , x≤y r r∈Lx , s∈Lz , q<r+s ∣₁)

  +-monoL-≤ :
    (x y z : DedekindCut ℓ) →
    x ≤ y →
    z + x ≤ z + y
  +-monoL-≤ x y z x≤y =
    subst2 _≤_ (+-comm x z) (+-comm y z)
      (+-monoR-≤ x y z x≤y)

  +-mono-≤ :
    (x y z w : DedekindCut ℓ) →
    x ≤ y →
    z ≤ w →
    x + z ≤ y + w
  +-mono-≤ x y z w x≤y z≤w =
    ≤-trans (x + z) (y + z) (y + w)
      (+-monoR-≤ x y z x≤y)
      (+-monoL-≤ z w y z≤w)

  +-nonnegative :
    (x y : DedekindCut ℓ) →
    0D ≤ x →
    0D ≤ y →
    0D ≤ x + y
  +-nonnegative x y 0≤x 0≤y =
    ≤-trans 0D (0D + 0D) (x + y)
      (≡→≤ (sym (+-idR 0D)))
      (+-mono-≤ 0D x 0D y 0≤x 0≤y)

  +-monoR-< :
    (x y z : DedekindCut ℓ) →
    x < y →
    x + z < y + z
  +-monoR-< x y z =
    Prop.rec squash₁
      (λ (p , p∈Ux , p∈Ly) →
        Prop.rec squash₁
          (λ (r , p<r , r∈Ly) →
            Prop.rec squash₁
              (λ (l , u , l∈Lz , u∈Uz , _ , u<l+r-p) →
                let
                  p+u<r+l : p ℚ.+ u ℚOrder.< r ℚ.+ l
                  p+u<r+l =
                    ℚExtra.sum-left-close< p l u r u<l+r-p
                in
                Prop.rec squash₁
                  (λ (q , p+u<q , q<r+l) →
                    ∣ q
                    , ∣ p , u , p∈Ux , u∈Uz , p+u<q ∣₁
                    , ∣ r , l , r∈Ly , l∈Lz , q<r+l ∣₁
                    ∣₁)
                  (ℚExtra.dense {p = p ℚ.+ u} {q = r ℚ.+ l} p+u<r+l))
              (close-bounds z (r ℚ.- p)
                (ℚExtra.diff-positive {p = p} {q = r} p<r)))
          (lower-rounded y p p∈Ly))

  +-monoL-< :
    (x y z : DedekindCut ℓ) →
    x < y →
    z + x < z + y
  +-monoL-< x y z x<y =
    subst2 _<_ (+-comm x z) (+-comm y z)
      (+-monoR-< x y z x<y)


module NonnegativeMultiplication {ℓ : Level} where
  open Order {ℓ}
  open Archimedean {ℓ}
  open Approximation {ℓ}
  open Addition {ℓ}

  Nonnegative : DedekindCut ℓ → Type ℓ
  Nonnegative x = 0D ≤ x

  0D-nonnegative : Nonnegative 0D
  0D-nonnegative = ≤-refl 0D

  1D-nonnegative : Nonnegative 1D
  1D-nonnegative q q∈L0 =
    lift
      (ℚOrder.isTrans< q ℚExtra.0ℚ ℚExtra.1ℚ
        (Lift.lower q∈L0)
        ℚExtra.0<1)

  nonnegative-upper-positive :
    (x : DedekindCut ℓ) →
    Nonnegative x →
    (q : ℚ) →
    q ∈ upper x →
    ℚExtra.0ℚ ℚOrder.< q
  nonnegative-upper-positive x 0≤x q q∈Ux
    with ℚExtra.0ℚ ℚOrder.≟ q
  ... | ℚOrder.lt 0<q = 0<q
  ... | ℚOrder.eq 0≡q =
    Empty.rec
      (Prop.rec Empty.isProp⊥
        (λ (r , r<q , r∈Ux) →
          let
            r<0 : r ℚOrder.< ℚExtra.0ℚ
            r<0 =
              subst (λ v → r ℚOrder.< v)
                (sym 0≡q)
                r<q
          in
          disjoint x r (0≤x r (lift r<0)) r∈Ux)
        (upper-rounded x q q∈Ux))
  ... | ℚOrder.gt q<0 =
    Empty.rec (disjoint x q (0≤x q (lift q<0)) q∈Ux)

  ProductLowerWitness :
    DedekindCut ℓ → DedekindCut ℓ → ℚ → Type ℓ
  ProductLowerWitness x y q =
    Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ]
      (a ∈ lower x) ×
      (b ∈ lower y) ×
      (ℚExtra.0ℚ ℚOrder.< a) ×
      (ℚExtra.0ℚ ℚOrder.< b) ×
      (q ℚOrder.< a ℚ.· b)

  ProductUpperWitness :
    DedekindCut ℓ → DedekindCut ℓ → ℚ → Type ℓ
  ProductUpperWitness x y q =
    Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ]
      (a ∈ upper x) ×
      (b ∈ upper y) ×
      (ℚExtra.0ℚ ℚOrder.< a) ×
      (ℚExtra.0ℚ ℚOrder.< b) ×
      (a ℚ.· b ℚOrder.< q)

  NonnegativeCloseBounds : DedekindCut ℓ → ℚ → Type ℓ
  NonnegativeCloseBounds x ε =
    Σ[ p ∈ ℚ ] Σ[ q ∈ ℚ ]
      (p ∈ lower x) ×
      (q ∈ upper x) ×
      (p ℚOrder.< q) ×
      (q ℚOrder.< p ℚ.+ ε) ×
      (ℚExtra.0ℚ ℚOrder.< q)

  NonnegativeBoundedCloseBounds : DedekindCut ℓ → ℚ → ℚ → Type ℓ
  NonnegativeBoundedCloseBounds x ε u =
    Σ[ p ∈ ℚ ] Σ[ q ∈ ℚ ]
      (p ∈ lower x) ×
      (q ∈ upper x) ×
      (p ℚOrder.< q) ×
      (q ℚOrder.< p ℚ.+ ε) ×
      (ℚExtra.0ℚ ℚOrder.< q) ×
      (q ℚOrder.≤ u)

  nonnegative-close-bounds :
    (x : DedekindCut ℓ) →
    Nonnegative x →
    (ε : ℚ) →
    ℚExtra.0ℚ ℚOrder.< ε →
    ∥ NonnegativeCloseBounds x ε ∥₁
  nonnegative-close-bounds x 0≤x ε 0<ε =
    Prop.rec squash₁
      (λ (p , q , p∈Lx , q∈Ux , p<q , q<p+ε) →
        ∣ p , q
        , p∈Lx
        , q∈Ux
        , p<q
        , q<p+ε
        , nonnegative-upper-positive x 0≤x q q∈Ux
        ∣₁)
      (close-bounds x ε 0<ε)

  nonnegative-bounded-close-bounds :
    (x : DedekindCut ℓ) →
    Nonnegative x →
    (ε u : ℚ) →
    ℚExtra.0ℚ ℚOrder.< ε →
    u ∈ upper x →
    ∥ NonnegativeBoundedCloseBounds x ε u ∥₁
  nonnegative-bounded-close-bounds x 0≤x ε u 0<ε u∈Ux =
    Prop.rec squash₁
      (λ (p , q , p∈Lx , q∈Ux , p<q , q<p+ε , q≤u) →
        ∣ p , q
        , p∈Lx
        , q∈Ux
        , p<q
        , q<p+ε
        , nonnegative-upper-positive x 0≤x q q∈Ux
        , q≤u
        ∣₁)
      (bounded-close-bounds x ε u 0<ε u∈Ux)

  MultiplicationCloseBounds :
    DedekindCut ℓ → DedekindCut ℓ → ℚ → ℚ → ℚ → Type ℓ
  MultiplicationCloseBounds x y δ U V =
    Σ[ lx ∈ ℚ ] Σ[ ux ∈ ℚ ] Σ[ ly ∈ ℚ ] Σ[ uy ∈ ℚ ]
      (lx ∈ lower x) ×
      (ux ∈ upper x) ×
      (lx ℚOrder.< ux) ×
      (ux ℚOrder.< lx ℚ.+ δ) ×
      (ℚExtra.0ℚ ℚOrder.< ux) ×
      (ux ℚOrder.≤ U) ×
      (ly ∈ lower y) ×
      (uy ∈ upper y) ×
      (ly ℚOrder.< uy) ×
      (uy ℚOrder.< ly ℚ.+ δ) ×
      (ℚExtra.0ℚ ℚOrder.< uy) ×
      (uy ℚOrder.≤ V)

  multiplication-close-bounds :
    (x y : DedekindCut ℓ) →
    Nonnegative x →
    Nonnegative y →
    (δ U V : ℚ) →
    ℚExtra.0ℚ ℚOrder.< δ →
    U ∈ upper x →
    V ∈ upper y →
    ∥ MultiplicationCloseBounds x y δ U V ∥₁
  multiplication-close-bounds x y 0≤x 0≤y δ U V 0<δ U∈Ux V∈Uy =
    Prop.rec2 squash₁
      (λ (lx , ux , lx∈Lx , ux∈Ux , lx<ux , ux<lx+δ , 0<ux , ux≤U)
         (ly , uy , ly∈Ly , uy∈Uy , ly<uy , uy<ly+δ , 0<uy , uy≤V) →
        ∣ lx , ux , ly , uy
        , lx∈Lx
        , ux∈Ux
        , lx<ux
        , ux<lx+δ
        , 0<ux
        , ux≤U
        , ly∈Ly
        , uy∈Uy
        , ly<uy
        , uy<ly+δ
        , 0<uy
        , uy≤V
        ∣₁)
      (nonnegative-bounded-close-bounds x 0≤x δ U 0<δ U∈Ux)
      (nonnegative-bounded-close-bounds y 0≤y δ V 0<δ V∈Uy)

  located-multiplication-scale :
    (p q U V : ℚ) →
    p ℚOrder.< q →
    ℚExtra.0ℚ ℚOrder.< U →
    ℚExtra.0ℚ ℚOrder.< V →
    ℚ
  located-multiplication-scale p q U V p<q 0<U 0<V =
    ℚExtra.mulErrorScale
      (q ℚ.- p)
      U
      V
      0<U
      0<V
      (ℚExtra.diff-positive {p = p} {q = q} p<q)

  located-multiplication-scale-positive :
    (p q U V : ℚ) →
    (p<q : p ℚOrder.< q) →
    (0<U : ℚExtra.0ℚ ℚOrder.< U) →
    (0<V : ℚExtra.0ℚ ℚOrder.< V) →
    ℚExtra.0ℚ ℚOrder.< located-multiplication-scale p q U V p<q 0<U 0<V
  located-multiplication-scale-positive p q U V p<q 0<U 0<V =
    ℚExtra.mulErrorScale-positive
      {gap = q ℚ.- p}
      {U = U}
      {V = V}
      0<U 0<V
      (ℚExtra.diff-positive {p = p} {q = q} p<q)

  nnMulLower : DedekindCut ℓ → DedekindCut ℓ → ℚPred ℓ
  nnMulLower x y q =
    ∥ (q ℚOrder.< ℚExtra.0ℚ) ⊎ ProductLowerWitness x y q ∥₁ ,
    squash₁

  nnMulUpper : DedekindCut ℓ → DedekindCut ℓ → ℚPred ℓ
  nnMulUpper x y q =
    (ℚExtra.0ℚ ℚOrder.< q) × ∥ ProductUpperWitness x y q ∥₁ ,
    isProp× (ℚOrder.isProp< ℚExtra.0ℚ q) squash₁

  positive-upper-bound :
    (x : DedekindCut ℓ) →
    ∥ Σ[ u ∈ ℚ ] (u ∈ upper x) × (ℚExtra.0ℚ ℚOrder.< u) ∥₁
  positive-upper-bound x =
    Prop.rec squash₁
      (λ (n , x<n) →
        let
          u = ℚExtra.natMul (suc n) ℚExtra.1ℚ

          nℚ : ℚ
          nℚ = ℚExtra.natMul n ℚExtra.1ℚ

          n∈Ux : nℚ ∈ upper x
          n∈Ux = <ℚ→upper x nℚ x<n

          n<u : nℚ ℚOrder.< u
          n<u = ℚExtra.natMul-step< n {ε = ℚExtra.1ℚ} ℚExtra.0<1
        in
        ∣ u
        , upper-closed x nℚ u n<u n∈Ux
        , ℚExtra.natMul-suc-positive n {ε = ℚExtra.1ℚ} ℚExtra.0<1
        ∣₁)
      (upper-rational-bound x)

  nnMul-lower-inhabited :
    (x y : DedekindCut ℓ) →
    ∥ Σ[ q ∈ ℚ ] q ∈ nnMulLower x y ∥₁
  nnMul-lower-inhabited x y =
    ∣ ℚExtra.-1ℚ , ∣ Sum.inl ℚExtra.-1<0 ∣₁ ∣₁

  nnMul-upper-inhabited :
    (x y : DedekindCut ℓ) →
    ∥ Σ[ q ∈ ℚ ] q ∈ nnMulUpper x y ∥₁
  nnMul-upper-inhabited x y =
    Prop.rec2 squash₁
      (λ (a , a∈Ux , 0<a) (b , b∈Uy , 0<b) →
        let
          ab : ℚ
          ab = a ℚ.· b

          q : ℚ
          q = ab ℚ.+ ℚExtra.1ℚ

          0<ab : ℚExtra.0ℚ ℚOrder.< ab
          0<ab = ℚExtra.mul-positive {a = a} {b = b} 0<a 0<b

          ab<q : ab ℚOrder.< q
          ab<q = ℚExtra.q<q+1 ab

          0<q : ℚExtra.0ℚ ℚOrder.< q
          0<q = ℚOrder.isTrans< ℚExtra.0ℚ ab q 0<ab ab<q
        in
        ∣ q , 0<q , ∣ a , b , a∈Ux , b∈Uy , 0<a , 0<b , ab<q ∣₁ ∣₁)
      (positive-upper-bound x)
      (positive-upper-bound y)

  nnMul-lower-closed :
    (x y : DedekindCut ℓ) (p q : ℚ) →
    p ℚOrder.< q →
    q ∈ nnMulLower x y →
    p ∈ nnMulLower x y
  nnMul-lower-closed x y p q p<q =
    Prop.rec squash₁
      (λ where
        (Sum.inl q<0) →
          ∣ Sum.inl
              (ℚOrder.isTrans< p q ℚExtra.0ℚ p<q q<0)
          ∣₁
        (Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , q<ab)) →
          ∣ Sum.inr
              (a , b , a∈Lx , b∈Ly , 0<a , 0<b
              , ℚOrder.isTrans< p q (a ℚ.· b) p<q q<ab)
          ∣₁)

  nnMul-upper-closed :
    (x y : DedekindCut ℓ) (p q : ℚ) →
    p ℚOrder.< q →
    p ∈ nnMulUpper x y →
    q ∈ nnMulUpper x y
  nnMul-upper-closed x y p q p<q (0<p , p∈U) =
    ℚOrder.isTrans< ℚExtra.0ℚ p q 0<p p<q ,
    Prop.rec squash₁
      (λ (a , b , a∈Ux , b∈Uy , 0<a , 0<b , ab<p) →
        ∣ a , b , a∈Ux , b∈Uy , 0<a , 0<b
        , ℚOrder.isTrans< (a ℚ.· b) p q ab<p p<q
        ∣₁)
      p∈U

  nnMul-lower-rounded :
    (x y : DedekindCut ℓ) (q : ℚ) →
    q ∈ nnMulLower x y →
    ∥ Σ[ r ∈ ℚ ] (q ℚOrder.< r) × (r ∈ nnMulLower x y) ∥₁
  nnMul-lower-rounded x y q =
    Prop.rec squash₁
      (λ where
        (Sum.inl q<0) →
          Prop.rec squash₁
            (λ (r , q<r , r<0) →
              ∣ r , q<r , ∣ Sum.inl r<0 ∣₁ ∣₁)
            (ℚExtra.dense {p = q} {q = ℚExtra.0ℚ} q<0)
        (Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , q<ab)) →
          Prop.rec squash₁
            (λ (r , q<r , r<ab) →
              ∣ r , q<r
              , ∣ Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , r<ab) ∣₁
              ∣₁)
            (ℚExtra.dense {p = q} {q = a ℚ.· b} q<ab))

  nnMul-upper-rounded :
    (x y : DedekindCut ℓ) (q : ℚ) →
    q ∈ nnMulUpper x y →
    ∥ Σ[ r ∈ ℚ ] (r ℚOrder.< q) × (r ∈ nnMulUpper x y) ∥₁
  nnMul-upper-rounded x y q (0<q , q∈U) =
    Prop.rec squash₁
      (λ (a , b , a∈Ux , b∈Uy , 0<a , 0<b , ab<q) →
        Prop.rec squash₁
          (λ (r , ab<r , r<q) →
            ∣ r , r<q
            , ℚOrder.isTrans< ℚExtra.0ℚ (a ℚ.· b) r
                (ℚExtra.mul-positive {a = a} {b = b} 0<a 0<b)
                ab<r
            , ∣ a , b , a∈Ux , b∈Uy , 0<a , 0<b , ab<r ∣₁
            ∣₁)
          (ℚExtra.dense {p = a ℚ.· b} {q = q} ab<q))
      q∈U

  nnMul-disjoint :
    (x y : DedekindCut ℓ) (q : ℚ) →
    q ∈ nnMulLower x y →
    q ∈ nnMulUpper x y →
    ⊥
  nnMul-disjoint x y q q∈L (0<q , q∈U) =
    Prop.rec Empty.isProp⊥ lower-case q∈L
    where
    lower-case :
      (q ℚOrder.< ℚExtra.0ℚ) ⊎ ProductLowerWitness x y q →
      ⊥
    lower-case (Sum.inl q<0) =
      ℚOrder.isIrrefl< q
        (ℚOrder.isTrans< q ℚExtra.0ℚ q q<0 0<q)
    lower-case (Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , q<ab)) =
      Prop.rec Empty.isProp⊥
        (λ (c , d , c∈Ux , d∈Uy , 0<c , 0<d , cd<q) →
          let
            a<c : a ℚOrder.< c
            a<c = lower<upper x a c a∈Lx c∈Ux

            b<d : b ℚOrder.< d
            b<d = lower<upper y b d b∈Ly d∈Uy

            ab<cd : a ℚ.· b ℚOrder.< c ℚ.· d
            ab<cd =
              ℚExtra.mul-mono-positive-<
                {a = a} {b = b} {c = c} {d = d}
                a<c b<d 0<b 0<c

            q<q : q ℚOrder.< q
            q<q =
              ℚOrder.isTrans< q (a ℚ.· b) q
                q<ab
                (ℚOrder.isTrans< (a ℚ.· b) (c ℚ.· d) q ab<cd cd<q)
          in
          ℚOrder.isIrrefl< q q<q)
        q∈U

  nnMulLower-comm :
    (x y : DedekindCut ℓ) →
    nnMulLower x y ⊆ nnMulLower y x
  nnMulLower-comm x y q =
    Prop.rec squash₁
      (λ where
        (Sum.inl q<0) → ∣ Sum.inl q<0 ∣₁
        (Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , q<ab)) →
          ∣ Sum.inr
              (b , a
              , b∈Ly
              , a∈Lx
              , 0<b
              , 0<a
              , subst (λ v → q ℚOrder.< v) (ℚ.·Comm a b) q<ab)
          ∣₁)

  nnMulUpper-comm :
    (x y : DedekindCut ℓ) →
    nnMulUpper x y ⊆ nnMulUpper y x
  nnMulUpper-comm x y q (0<q , q∈U) =
    0<q ,
    Prop.rec squash₁
      (λ (a , b , a∈Ux , b∈Uy , 0<a , 0<b , ab<q) →
        ∣ b , a
        , b∈Uy
        , a∈Ux
        , 0<b
        , 0<a
        , subst (λ v → v ℚOrder.< q) (ℚ.·Comm a b) ab<q
        ∣₁)
      q∈U

  nnMul-lower-from-negative :
    (x y : DedekindCut ℓ) →
    (q : ℚ) →
    q ℚOrder.< ℚExtra.0ℚ →
    q ∈ nnMulLower x y
  nnMul-lower-from-negative x y q q<0 =
    ∣ Sum.inl q<0 ∣₁

  nnMul-lower-from-product :
    (x y : DedekindCut ℓ) →
    (q : ℚ) →
    ProductLowerWitness x y q →
    q ∈ nnMulLower x y
  nnMul-lower-from-product x y q witness =
    ∣ Sum.inr witness ∣₁

  nnMul-upper-from-product :
    (x y : DedekindCut ℓ) →
    (q : ℚ) →
    ℚExtra.0ℚ ℚOrder.< q →
    ProductUpperWitness x y q →
    q ∈ nnMulUpper x y
  nnMul-upper-from-product x y q 0<q witness =
    0<q , ∣ witness ∣₁

  nnMulLocated :
    DedekindCut ℓ → DedekindCut ℓ → Type ℓ
  nnMulLocated x y =
    (p q : ℚ) →
    p ℚOrder.< q →
    ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁

  nnMul-located-negative-left :
    (x y : DedekindCut ℓ) →
    (p q : ℚ) →
    p ℚOrder.< ℚExtra.0ℚ →
    ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁
  nnMul-located-negative-left x y p q p<0 =
    ∣ Sum.inl (nnMul-lower-from-negative x y p p<0) ∣₁

  nnMul-located-lower-product :
    (x y : DedekindCut ℓ) →
    (p q : ℚ) →
    ProductLowerWitness x y p →
    ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁
  nnMul-located-lower-product x y p q witness =
    ∣ Sum.inl (nnMul-lower-from-product x y p witness) ∣₁

  nnMul-located-upper-product :
    (x y : DedekindCut ℓ) →
    (p q : ℚ) →
    ℚExtra.0ℚ ℚOrder.< q →
    ProductUpperWitness x y q →
    ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁
  nnMul-located-upper-product x y p q 0<q witness =
    ∣ Sum.inr (nnMul-upper-from-product x y q 0<q witness) ∣₁

  nnMul-located-by-p-sign :
    (x y : DedekindCut ℓ) →
    (p q : ℚ) →
    p ℚOrder.< q →
    ((0≤p : ℚExtra.0ℚ ℚOrder.≤ p) →
      ℚExtra.0ℚ ℚOrder.< q →
      ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁) →
    ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁
  nnMul-located-by-p-sign x y p q p<q nonnegative-case
    with ℚExtra.negative-or-nonnegative p
  ... | Sum.inl p<0 =
    nnMul-located-negative-left x y p q p<0
  ... | Sum.inr 0≤p =
    nonnegative-case
      0≤p
      (ℚExtra.nonnegative-right-of-< {p = p} {q = q} 0≤p p<q)

  nnMul-upper-witness-left-nonpositive :
    (x y : DedekindCut ℓ) →
    (p q U V lx ux uy : ℚ) →
    (p<q : p ℚOrder.< q) →
    ℚExtra.0ℚ ℚOrder.≤ p →
    (0<U : ℚExtra.0ℚ ℚOrder.< U) →
    (0<V : ℚExtra.0ℚ ℚOrder.< V) →
    lx ℚOrder.≤ ℚExtra.0ℚ →
    ux ∈ upper x →
    uy ∈ upper y →
    ux ℚOrder.< lx ℚ.+ located-multiplication-scale p q U V p<q 0<U 0<V →
    ℚExtra.0ℚ ℚOrder.< ux →
    ℚExtra.0ℚ ℚOrder.< uy →
    uy ℚOrder.≤ V →
    ProductUpperWitness x y q
  nnMul-upper-witness-left-nonpositive
    x y p q U V lx ux uy p<q 0≤p 0<U 0<V
    lx≤0 ux∈Ux uy∈Uy ux<lx+δ 0<ux 0<uy uy≤V =
    ux , uy
    , ux∈Ux
    , uy∈Uy
    , 0<ux
    , 0<uy
    , uxuy<q
    where
    gap : ℚ
    gap = q ℚ.- p

    0<gap : ℚExtra.0ℚ ℚOrder.< gap
    0<gap = ℚExtra.diff-positive {p = p} {q = q} p<q

    δ : ℚ
    δ = located-multiplication-scale p q U V p<q 0<U 0<V

    δV<gap : δ ℚ.· V ℚOrder.< gap
    δV<gap =
      ℚExtra.mulErrorScale-times-V<gap
        {gap = gap} {U = U} {V = V}
        0<U 0<V 0<gap

    gap≤q : gap ℚOrder.≤ q
    gap≤q = ℚExtra.diff≤right {p = p} {q = q} 0≤p

    uxuy<q : ux ℚ.· uy ℚOrder.< q
    uxuy<q =
      ℚExtra.mul-close-left-nonpositive-upper<
        {q = q} {gap = gap} {δ = δ} {V = V}
        {lx = lx} {ux = ux} {uy = uy}
        lx≤0 ux<lx+δ 0<ux 0<uy uy≤V δV<gap gap≤q

  nnMul-upper-witness-right-nonpositive :
    (x y : DedekindCut ℓ) →
    (p q U V ly ux uy : ℚ) →
    (p<q : p ℚOrder.< q) →
    ℚExtra.0ℚ ℚOrder.≤ p →
    (0<U : ℚExtra.0ℚ ℚOrder.< U) →
    (0<V : ℚExtra.0ℚ ℚOrder.< V) →
    ly ℚOrder.≤ ℚExtra.0ℚ →
    ux ∈ upper x →
    uy ∈ upper y →
    uy ℚOrder.< ly ℚ.+ located-multiplication-scale p q U V p<q 0<U 0<V →
    ℚExtra.0ℚ ℚOrder.< ux →
    ℚExtra.0ℚ ℚOrder.< uy →
    ux ℚOrder.≤ U →
    ProductUpperWitness x y q
  nnMul-upper-witness-right-nonpositive
    x y p q U V ly ux uy p<q 0≤p 0<U 0<V
    ly≤0 ux∈Ux uy∈Uy uy<ly+δ 0<ux 0<uy ux≤U =
    ux , uy
    , ux∈Ux
    , uy∈Uy
    , 0<ux
    , 0<uy
    , uxuy<q
    where
    gap : ℚ
    gap = q ℚ.- p

    0<gap : ℚExtra.0ℚ ℚOrder.< gap
    0<gap = ℚExtra.diff-positive {p = p} {q = q} p<q

    δ : ℚ
    δ = located-multiplication-scale p q U V p<q 0<U 0<V

    δU<gap : δ ℚ.· U ℚOrder.< gap
    δU<gap =
      ℚExtra.mulErrorScale-times-U<gap
        {gap = gap} {U = U} {V = V}
        0<U 0<V 0<gap

    gap≤q : gap ℚOrder.≤ q
    gap≤q = ℚExtra.diff≤right {p = p} {q = q} 0≤p

    uxuy<q : ux ℚ.· uy ℚOrder.< q
    uxuy<q =
      ℚExtra.mul-close-right-nonpositive-upper<
        {q = q} {gap = gap} {δ = δ} {U = U}
        {ly = ly} {ux = ux} {uy = uy}
        ly≤0 uy<ly+δ 0<ux 0<uy ux≤U δU<gap gap≤q

  nnMul-upper-witness-positive :
    (x y : DedekindCut ℓ) →
    (p q U V lx ux ly uy : ℚ) →
    (p<q : p ℚOrder.< q) →
    (0<U : ℚExtra.0ℚ ℚOrder.< U) →
    (0<V : ℚExtra.0ℚ ℚOrder.< V) →
    lx ℚOrder.< ux →
    ly ℚOrder.< uy →
    ℚExtra.0ℚ ℚOrder.< lx →
    ℚExtra.0ℚ ℚOrder.< ly →
    ux ∈ upper x →
    uy ∈ upper y →
    ux ℚOrder.< lx ℚ.+ located-multiplication-scale p q U V p<q 0<U 0<V →
    uy ℚOrder.< ly ℚ.+ located-multiplication-scale p q U V p<q 0<U 0<V →
    ux ℚOrder.≤ U →
    uy ℚOrder.≤ V →
    lx ℚ.· ly ℚOrder.≤ p →
    ProductUpperWitness x y q
  nnMul-upper-witness-positive
    x y p q U V lx ux ly uy p<q 0<U 0<V
    lx<ux ly<uy 0<lx 0<ly ux∈Ux uy∈Uy
    ux<lx+δ uy<ly+δ ux≤U uy≤V lxly≤p =
    ux , uy
    , ux∈Ux
    , uy∈Uy
    , 0<ux
    , 0<uy
    , uxuy<q
    where
    gap : ℚ
    gap = q ℚ.- p

    0<gap : ℚExtra.0ℚ ℚOrder.< gap
    0<gap = ℚExtra.diff-positive {p = p} {q = q} p<q

    δ : ℚ
    δ = located-multiplication-scale p q U V p<q 0<U 0<V

    0<ux : ℚExtra.0ℚ ℚOrder.< ux
    0<ux = ℚOrder.isTrans< ℚExtra.0ℚ lx ux 0<lx lx<ux

    0<uy : ℚExtra.0ℚ ℚOrder.< uy
    0<uy = ℚOrder.isTrans< ℚExtra.0ℚ ly uy 0<ly ly<uy

    δUV<gap : δ ℚ.· (U ℚ.+ V) ℚOrder.< gap
    δUV<gap =
      ℚExtra.mulErrorScale-times-sum<gap
        {gap = gap} {U = U} {V = V}
        0<U 0<V 0<gap

    uxuy<q : ux ℚ.· uy ℚOrder.< q
    uxuy<q =
      ℚExtra.mul-close-positive-upper<
        {p = p} {q = q} {gap = gap} {δ = δ}
        {U = U} {V = V} {lx = lx} {ux = ux} {ly = ly} {uy = uy}
        lx<ux ly<uy 0<lx 0<ly
        ux<lx+δ
        uy<ly+δ
        ux≤U uy≤V lxly≤p δUV<gap
        (ℚExtra.p+[q-p]≡q p q)

  nnMul-located :
    (x y : DedekindCut ℓ) →
    Nonnegative x →
    Nonnegative y →
    nnMulLocated x y
  nnMul-located x y 0≤x 0≤y p q p<q =
    nnMul-located-by-p-sign x y p q p<q located-nonnegative-p
    where
    located-nonnegative-p :
      (0≤p : ℚExtra.0ℚ ℚOrder.≤ p) →
      ℚExtra.0ℚ ℚOrder.< q →
      ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁
    located-nonnegative-p 0≤p 0<q =
      Prop.rec2 squash₁
        (λ (U , U∈Ux , 0<U) (V , V∈Uy , 0<V) →
          let
            δ : ℚ
            δ = located-multiplication-scale p q U V p<q 0<U 0<V

            0<δ : ℚExtra.0ℚ ℚOrder.< δ
            0<δ =
              located-multiplication-scale-positive p q U V p<q 0<U 0<V
          in
          Prop.rec squash₁
            (located-from-bounds U V 0<U 0<V)
            (multiplication-close-bounds x y 0≤x 0≤y δ U V 0<δ U∈Ux V∈Uy))
        (positive-upper-bound x)
        (positive-upper-bound y)
      where
      located-from-bounds :
        (U V : ℚ) →
        (0<U : ℚExtra.0ℚ ℚOrder.< U) →
        (0<V : ℚExtra.0ℚ ℚOrder.< V) →
        MultiplicationCloseBounds x y
          (located-multiplication-scale p q U V p<q 0<U 0<V) U V →
        ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁
      located-from-bounds U V 0<U 0<V
        (lx , ux , ly , uy
        , lx∈Lx
        , ux∈Ux
        , lx<ux
        , ux<lx+δ
        , 0<ux
        , ux≤U
        , ly∈Ly
        , uy∈Uy
        , ly<uy
        , uy<ly+δ
        , 0<uy
        , uy≤V) =
        case-lx (ℚExtra.0ℚ ℚOrder.≟ lx)
        where
        Result : Type ℓ
        Result = ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁

        δ : ℚ
        δ = located-multiplication-scale p q U V p<q 0<U 0<V

        case-prod :
          ℚExtra.0ℚ ℚOrder.< lx →
          ℚExtra.0ℚ ℚOrder.< ly →
          ℚOrder.Trichotomy p (lx ℚ.· ly) →
          Result
        case-prod 0<lx 0<ly (ℚOrder.lt p<lxly) =
          nnMul-located-lower-product x y p q
            (lx , ly , lx∈Lx , ly∈Ly , 0<lx , 0<ly , p<lxly)
        case-prod 0<lx 0<ly (ℚOrder.eq p≡lxly) =
          nnMul-located-upper-product x y p q 0<q
            (nnMul-upper-witness-positive
              x y p q U V lx ux ly uy p<q 0<U 0<V
              lx<ux ly<uy 0<lx 0<ly
              ux∈Ux uy∈Uy
              ux<lx+δ
              uy<ly+δ
              ux≤U uy≤V
              (ℚOrder.≡Weaken≤ (lx ℚ.· ly) p (sym p≡lxly)))
        case-prod 0<lx 0<ly (ℚOrder.gt lxly<p) =
          nnMul-located-upper-product x y p q 0<q
            (nnMul-upper-witness-positive
              x y p q U V lx ux ly uy p<q 0<U 0<V
              lx<ux ly<uy 0<lx 0<ly
              ux∈Ux uy∈Uy
              ux<lx+δ
              uy<ly+δ
              ux≤U uy≤V
              (ℚExtra.<→≤ {p = lx ℚ.· ly} {q = p} lxly<p))

        case-ly :
          ℚExtra.0ℚ ℚOrder.< lx →
          ℚOrder.Trichotomy ℚExtra.0ℚ ly →
          Result
        case-ly 0<lx (ℚOrder.lt 0<ly) =
          case-prod 0<lx 0<ly (p ℚOrder.≟ (lx ℚ.· ly))
        case-ly 0<lx (ℚOrder.eq 0≡ly) =
          nnMul-located-upper-product x y p q 0<q
            (nnMul-upper-witness-right-nonpositive
              x y p q U V ly ux uy p<q 0≤p 0<U 0<V
              (ℚOrder.≡Weaken≤ ly ℚExtra.0ℚ (sym 0≡ly))
              ux∈Ux uy∈Uy
              uy<ly+δ
              0<ux 0<uy ux≤U)
        case-ly 0<lx (ℚOrder.gt ly<0) =
          nnMul-located-upper-product x y p q 0<q
            (nnMul-upper-witness-right-nonpositive
              x y p q U V ly ux uy p<q 0≤p 0<U 0<V
              (ℚExtra.<→≤ {p = ly} {q = ℚExtra.0ℚ} ly<0)
              ux∈Ux uy∈Uy
              uy<ly+δ
              0<ux 0<uy ux≤U)

        case-lx :
          ℚOrder.Trichotomy ℚExtra.0ℚ lx →
          Result
        case-lx (ℚOrder.lt 0<lx) =
          case-ly 0<lx (ℚExtra.0ℚ ℚOrder.≟ ly)
        case-lx (ℚOrder.eq 0≡lx) =
          nnMul-located-upper-product x y p q 0<q
            (nnMul-upper-witness-left-nonpositive
              x y p q U V lx ux uy p<q 0≤p 0<U 0<V
              (ℚOrder.≡Weaken≤ lx ℚExtra.0ℚ (sym 0≡lx))
              ux∈Ux uy∈Uy
              ux<lx+δ
              0<ux 0<uy uy≤V)
        case-lx (ℚOrder.gt lx<0) =
          nnMul-located-upper-product x y p q 0<q
            (nnMul-upper-witness-left-nonpositive
              x y p q U V lx ux uy p<q 0≤p 0<U 0<V
              (ℚExtra.<→≤ {p = lx} {q = ℚExtra.0ℚ} lx<0)
              ux∈Ux uy∈Uy
              ux<lx+δ
              0<ux 0<uy uy≤V)

  nnMul-is-cut :
    (x y : DedekindCut ℓ) →
    nnMulLocated x y →
    isDedekindCut (nnMulLower x y) (nnMulUpper x y)
  nnMul-is-cut x y located .isDedekindCut.lower-inhabited =
    nnMul-lower-inhabited x y
  nnMul-is-cut x y located .isDedekindCut.upper-inhabited =
    nnMul-upper-inhabited x y
  nnMul-is-cut x y located .isDedekindCut.lower-closed =
    nnMul-lower-closed x y
  nnMul-is-cut x y located .isDedekindCut.upper-closed =
    nnMul-upper-closed x y
  nnMul-is-cut x y located .isDedekindCut.lower-rounded =
    nnMul-lower-rounded x y
  nnMul-is-cut x y located .isDedekindCut.upper-rounded =
    nnMul-upper-rounded x y
  nnMul-is-cut x y located .isDedekindCut.disjoint =
    nnMul-disjoint x y
  nnMul-is-cut x y located .isDedekindCut.located =
    located

  nnMulCut :
    (x y : DedekindCut ℓ) →
    nnMulLocated x y →
    DedekindCut ℓ
  nnMulCut x y located .lower = nnMulLower x y
  nnMulCut x y located .upper = nnMulUpper x y
  nnMulCut x y located .is-cut = nnMul-is-cut x y located

  nnMul :
    (x y : DedekindCut ℓ) →
    Nonnegative x →
    Nonnegative y →
    DedekindCut ℓ
  nnMul x y 0≤x 0≤y =
    nnMulCut x y (nnMul-located x y 0≤x 0≤y)

  nnMul-comm :
    (x y : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    (0≤y : Nonnegative y) →
    nnMul x y 0≤x 0≤y ≡ nnMul y x 0≤y 0≤x
  nnMul-comm x y 0≤x 0≤y =
    cutExt
      (nnMul x y 0≤x 0≤y)
      (nnMul y x 0≤y 0≤x)
      (nnMulLower-comm x y)
      (nnMulLower-comm y x)
      (nnMulUpper-comm x y)
      (nnMulUpper-comm y x)

  nnMul-zeroR :
    (x : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    nnMul x 0D 0≤x 0D-nonnegative ≡ 0D
  nnMul-zeroR x 0≤x =
    cutExt
      (nnMul x 0D 0≤x 0D-nonnegative)
      0D
      lower⊆
      lower⊇
      upper⊆
      upper⊇
    where
    lower⊆ : nnMulLower x 0D ⊆ lower 0D
    lower⊆ q =
      Prop.rec (isProp∈ (lower 0D) q)
        (λ where
          (Sum.inl q<0) → lift q<0
          (Sum.inr (a , b , a∈Lx , b∈L0 , 0<a , 0<b , q<ab)) →
            Empty.rec (ℚOrder.isAsym< ℚExtra.0ℚ b 0<b (Lift.lower b∈L0)))

    lower⊇ : lower 0D ⊆ nnMulLower x 0D
    lower⊇ q q∈L0 =
      ∣ Sum.inl (Lift.lower q∈L0) ∣₁

    upper⊆ : nnMulUpper x 0D ⊆ upper 0D
    upper⊆ q (0<q , q∈U) =
      lift 0<q

    upper⊇ : upper 0D ⊆ nnMulUpper x 0D
    upper⊇ q q∈U0 =
      0<q ,
      Prop.rec squash₁
        (λ (a , a∈Ux , 0<a) →
          let
            b : ℚ
            b = ℚExtra.scaleByPositive ε a 0<a

            0<b : ℚExtra.0ℚ ℚOrder.< b
            0<b =
              ℚExtra.scaleByPositive-positive
                {ε = ε} {M = a}
                0<ε
                0<a

            ab≡ε : a ℚ.· b ≡ ε
            ab≡ε =
              ℚExtra.scaleByPositive-cancelL ε a 0<a

            ab<q : a ℚ.· b ℚOrder.< q
            ab<q =
              subst (λ r → r ℚOrder.< q) (sym ab≡ε) ε<q
          in
          ∣ a , b , a∈Ux , lift 0<b , 0<a , 0<b , ab<q ∣₁)
        (positive-upper-bound x)
      where
      0<q : ℚExtra.0ℚ ℚOrder.< q
      0<q = Lift.lower q∈U0

      ε : ℚ
      ε = ℚExtra.middle ℚExtra.0ℚ q

      0<ε : ℚExtra.0ℚ ℚOrder.< ε
      0<ε = ℚExtra.middle>l {p = ℚExtra.0ℚ} {q = q} 0<q

      ε<q : ε ℚOrder.< q
      ε<q = ℚExtra.middle<r {p = ℚExtra.0ℚ} {q = q} 0<q

  nnMul-zeroL :
    (x : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    nnMul 0D x 0D-nonnegative 0≤x ≡ 0D
  nnMul-zeroL x 0≤x =
    nnMul-comm 0D x 0D-nonnegative 0≤x ∙
    nnMul-zeroR x 0≤x

  nnMul-nonnegative :
    (x y : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    (0≤y : Nonnegative y) →
    Nonnegative (nnMul x y 0≤x 0≤y)
  nnMul-nonnegative x y 0≤x 0≤y q q∈L0 =
    ∣ Sum.inl (Lift.lower q∈L0) ∣₁

  nnMul-monoL-≤ :
    (x x' y : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    (0≤x' : Nonnegative x') →
    (0≤y : Nonnegative y) →
    x ≤ x' →
    nnMul x y 0≤x 0≤y ≤ nnMul x' y 0≤x' 0≤y
  nnMul-monoL-≤ x x' y 0≤x 0≤x' 0≤y x≤x' q =
    Prop.rec squash₁
      (λ where
        (Sum.inl q<0) → ∣ Sum.inl q<0 ∣₁
        (Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , q<ab)) →
          ∣ Sum.inr
              (a , b
              , x≤x' a a∈Lx
              , b∈Ly
              , 0<a
              , 0<b
              , q<ab)
          ∣₁)

  nnMul-monoR-≤ :
    (x y y' : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    (0≤y : Nonnegative y) →
    (0≤y' : Nonnegative y') →
    y ≤ y' →
    nnMul x y 0≤x 0≤y ≤ nnMul x y' 0≤x 0≤y'
  nnMul-monoR-≤ x y y' 0≤x 0≤y 0≤y' y≤y' q =
    Prop.rec squash₁
      (λ where
        (Sum.inl q<0) → ∣ Sum.inl q<0 ∣₁
        (Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , q<ab)) →
          ∣ Sum.inr
              (a , b
              , a∈Lx
              , y≤y' b b∈Ly
              , 0<a
              , 0<b
              , q<ab)
          ∣₁)

  nnMul-mono-≤ :
    (x x' y y' : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    (0≤x' : Nonnegative x') →
    (0≤y : Nonnegative y) →
    (0≤y' : Nonnegative y') →
    x ≤ x' →
    y ≤ y' →
    nnMul x y 0≤x 0≤y ≤ nnMul x' y' 0≤x' 0≤y'
  nnMul-mono-≤ x x' y y' 0≤x 0≤x' 0≤y 0≤y' x≤x' y≤y' =
    ≤-trans
      (nnMul x y 0≤x 0≤y)
      (nnMul x' y 0≤x' 0≤y)
      (nnMul x' y' 0≤x' 0≤y')
      (nnMul-monoL-≤ x x' y 0≤x 0≤x' 0≤y x≤x')
      (nnMul-monoR-≤ x' y y' 0≤x' 0≤y 0≤y' y≤y')

  nnMul-proof-irrelevant :
    (x y : DedekindCut ℓ) →
    (0≤x 0≤x' : Nonnegative x) →
    (0≤y 0≤y' : Nonnegative y) →
    nnMul x y 0≤x 0≤y ≡ nnMul x y 0≤x' 0≤y'
  nnMul-proof-irrelevant x y 0≤x 0≤x' 0≤y 0≤y' =
    cutExt
      (nnMul x y 0≤x 0≤y)
      (nnMul x y 0≤x' 0≤y')
      (λ q q∈L → q∈L)
      (λ q q∈L → q∈L)
      (λ q q∈U → q∈U)
      (λ q q∈U → q∈U)

  nnMul-congR :
    (x y y' : DedekindCut ℓ) →
    y ≡ y' →
    (0≤x 0≤x' : Nonnegative x) →
    (0≤y : Nonnegative y) →
    (0≤y' : Nonnegative y') →
    nnMul x y 0≤x 0≤y ≡ nnMul x y' 0≤x' 0≤y'
  nnMul-congR x y y' y≡y' 0≤x 0≤x' 0≤y 0≤y' =
    cutExt
      (nnMul x y 0≤x 0≤y)
      (nnMul x y' 0≤x' 0≤y')
      (lower-map y y' y≡y')
      (lower-map y' y (sym y≡y'))
      (upper-map y y' y≡y')
      (upper-map y' y (sym y≡y'))
    where
    lower-map :
      (z z' : DedekindCut ℓ) →
      z ≡ z' →
      nnMulLower x z ⊆ nnMulLower x z'
    lower-map z z' z≡z' q =
      Prop.rec squash₁
        (λ where
          (Sum.inl q<0) → ∣ Sum.inl q<0 ∣₁
          (Sum.inr (a , b , a∈Lx , b∈Lz , 0<a , 0<b , q<ab)) →
            ∣ Sum.inr
                (a , b
                , a∈Lx
                , subst (λ w → b ∈ lower w) z≡z' b∈Lz
                , 0<a
                , 0<b
                , q<ab)
            ∣₁)

    upper-map :
      (z z' : DedekindCut ℓ) →
      z ≡ z' →
      nnMulUpper x z ⊆ nnMulUpper x z'
    upper-map z z' z≡z' q (0<q , q∈U) =
      0<q ,
      Prop.rec squash₁
        (λ (a , b , a∈Ux , b∈Uz , 0<a , 0<b , ab<q) →
          ∣ a , b
          , a∈Ux
          , subst (λ w → b ∈ upper w) z≡z' b∈Uz
          , 0<a
          , 0<b
          , ab<q
          ∣₁)
        q∈U

  nnMul-congL :
    (x x' y : DedekindCut ℓ) →
    x ≡ x' →
    (0≤x : Nonnegative x) →
    (0≤x' : Nonnegative x') →
    (0≤y 0≤y' : Nonnegative y) →
    nnMul x y 0≤x 0≤y ≡ nnMul x' y 0≤x' 0≤y'
  nnMul-congL x x' y x≡x' 0≤x 0≤x' 0≤y 0≤y' =
    cutExt
      (nnMul x y 0≤x 0≤y)
      (nnMul x' y 0≤x' 0≤y')
      (lower-map x x' x≡x')
      (lower-map x' x (sym x≡x'))
      (upper-map x x' x≡x')
      (upper-map x' x (sym x≡x'))
    where
    lower-map :
      (z z' : DedekindCut ℓ) →
      z ≡ z' →
      nnMulLower z y ⊆ nnMulLower z' y
    lower-map z z' z≡z' q =
      Prop.rec squash₁
        (λ where
          (Sum.inl q<0) → ∣ Sum.inl q<0 ∣₁
          (Sum.inr (a , b , a∈Lz , b∈Ly , 0<a , 0<b , q<ab)) →
            ∣ Sum.inr
                (a , b
                , subst (λ w → a ∈ lower w) z≡z' a∈Lz
                , b∈Ly
                , 0<a
                , 0<b
                , q<ab)
            ∣₁)

    upper-map :
      (z z' : DedekindCut ℓ) →
      z ≡ z' →
      nnMulUpper z y ⊆ nnMulUpper z' y
    upper-map z z' z≡z' q (0<q , q∈U) =
      0<q ,
      Prop.rec squash₁
        (λ (a , b , a∈Uz , b∈Uy , 0<a , 0<b , ab<q) →
          ∣ a , b
          , subst (λ w → a ∈ upper w) z≡z' a∈Uz
          , b∈Uy
          , 0<a
          , 0<b
          , ab<q
          ∣₁)
        q∈U

  nnMul-cong₂ :
    (x x' y y' : DedekindCut ℓ) →
    x ≡ x' →
    y ≡ y' →
    (0≤x : Nonnegative x) →
    (0≤x' : Nonnegative x') →
    (0≤y : Nonnegative y) →
    (0≤y' : Nonnegative y') →
    nnMul x y 0≤x 0≤y ≡ nnMul x' y' 0≤x' 0≤y'
  nnMul-cong₂ x x' y y' x≡x' y≡y' 0≤x 0≤x' 0≤y 0≤y' =
    nnMul-congL x x' y x≡x' 0≤x 0≤x' 0≤y 0≤y ∙
    nnMul-congR x' y y' y≡y' 0≤x' 0≤x' 0≤y 0≤y'

  nnMulLocated-comm :
    (x y : DedekindCut ℓ) →
    nnMulLocated x y →
    nnMulLocated y x
  nnMulLocated-comm x y located p q p<q =
    Prop.rec squash₁
      (λ where
        (Sum.inl p∈Lxy) →
          ∣ Sum.inl (nnMulLower-comm x y p p∈Lxy) ∣₁
        (Sum.inr q∈Uxy) →
          ∣ Sum.inr (nnMulUpper-comm x y q q∈Uxy) ∣₁)
      (located p q p<q)

  nnMulCut-comm :
    (x y : DedekindCut ℓ) →
    (located : nnMulLocated x y) →
    nnMulCut x y located ≡ nnMulCut y x (nnMulLocated-comm x y located)
  nnMulCut-comm x y located =
    cutExt
      (nnMulCut x y located)
      (nnMulCut y x (nnMulLocated-comm x y located))
      (nnMulLower-comm x y)
      (nnMulLower-comm y x)
      (nnMulUpper-comm x y)
      (nnMulUpper-comm y x)


module SignedMultiplication {ℓ : Level} where
  open Order {ℓ}
  open Algebra {ℓ}
  open Lattice {ℓ}
  open Addition {ℓ}
  open NonnegativeMultiplication {ℓ}

  positivePart : DedekindCut ℓ → DedekindCut ℓ
  positivePart x = x ⊔ 0D

  negativePart : DedekindCut ℓ → DedekindCut ℓ
  negativePart x = (- x) ⊔ 0D

  positivePart-nonnegative :
    (x : DedekindCut ℓ) →
    Nonnegative (positivePart x)
  positivePart-nonnegative x =
    right≤⊔ x 0D

  negativePart-nonnegative :
    (x : DedekindCut ℓ) →
    Nonnegative (negativePart x)
  negativePart-nonnegative x =
    right≤⊔ (- x) 0D

  neg-0D : - 0D ≡ 0D
  neg-0D =
    neg-rational ℚExtra.0ℚ ∙
    cong (ℚ→DedekindCutAt ℓ) ℚExtra.neg-zero

  positivePart-0D : positivePart 0D ≡ 0D
  positivePart-0D = ⊔-idem 0D

  negativePart-0D : negativePart 0D ≡ 0D
  negativePart-0D =
    cong (λ z → z ⊔ 0D) neg-0D ∙
    ⊔-idem 0D

  positivePart-of-nonnegative :
    (x : DedekindCut ℓ) →
    Nonnegative x →
    positivePart x ≡ x
  positivePart-of-nonnegative x 0≤x =
    ≤-antisym (positivePart x) x
      (⊔≤ x 0D x (≤-refl x) 0≤x)
      (left≤⊔ x 0D)

  negativePart-of-nonnegative :
    (x : DedekindCut ℓ) →
    Nonnegative x →
    negativePart x ≡ 0D
  negativePart-of-nonnegative x 0≤x =
    ≤-antisym (negativePart x) 0D
      (⊔≤ (- x) 0D 0D -x≤0 (≤-refl 0D))
      (right≤⊔ (- x) 0D)
    where
    -x≤-0 : (- x) ≤ (- 0D)
    -x≤-0 =
      neg-≤-reverse 0D x 0≤x

    -0≤0 : (- 0D) ≤ 0D
    -0≤0 =
      ≡→≤ neg-0D

    -x≤0 : (- x) ≤ 0D
    -x≤0 =
      ≤-trans (- x) (- 0D) 0D -x≤-0 -0≤0

  positivePart-mono-≤ :
    (x y : DedekindCut ℓ) →
    x ≤ y →
    positivePart x ≤ positivePart y
  positivePart-mono-≤ x y x≤y =
    ⊔≤ x 0D (positivePart y)
      (≤-trans x y (positivePart y) x≤y (left≤⊔ y 0D))
      (right≤⊔ y 0D)

  negativePart-antitone-≤ :
    (x y : DedekindCut ℓ) →
    x ≤ y →
    negativePart y ≤ negativePart x
  negativePart-antitone-≤ x y x≤y =
    ⊔≤ (- y) 0D (negativePart x)
      (≤-trans (- y) (- x) (negativePart x)
        (neg-≤-reverse x y x≤y)
        (left≤⊔ (- x) 0D))
      (right≤⊔ (- x) 0D)

  positiveProducts : DedekindCut ℓ → DedekindCut ℓ → DedekindCut ℓ
  positiveProducts x y =
    nnMul (positivePart x) (positivePart y)
      (positivePart-nonnegative x)
      (positivePart-nonnegative y)
    +
    nnMul (negativePart x) (negativePart y)
      (negativePart-nonnegative x)
      (negativePart-nonnegative y)

  negativeProducts : DedekindCut ℓ → DedekindCut ℓ → DedekindCut ℓ
  negativeProducts x y =
    nnMul (positivePart x) (negativePart y)
      (positivePart-nonnegative x)
      (negativePart-nonnegative y)
    +
    nnMul (negativePart x) (positivePart y)
      (negativePart-nonnegative x)
      (positivePart-nonnegative y)

  _*_ : DedekindCut ℓ → DedekindCut ℓ → DedekindCut ℓ
  x * y = positiveProducts x y + (- negativeProducts x y)

  infixl 7 _*_

  positiveProducts-comm :
    (x y : DedekindCut ℓ) →
    positiveProducts x y ≡ positiveProducts y x
  positiveProducts-comm x y =
    cong₂ _+_
      (nnMul-comm
        (positivePart x) (positivePart y)
        (positivePart-nonnegative x)
        (positivePart-nonnegative y))
      (nnMul-comm
        (negativePart x) (negativePart y)
        (negativePart-nonnegative x)
        (negativePart-nonnegative y))

  negativeProducts-comm :
    (x y : DedekindCut ℓ) →
    negativeProducts x y ≡ negativeProducts y x
  negativeProducts-comm x y =
    cong₂ _+_
      (nnMul-comm
        (positivePart x) (negativePart y)
        (positivePart-nonnegative x)
        (negativePart-nonnegative y))
      (nnMul-comm
        (negativePart x) (positivePart y)
        (negativePart-nonnegative x)
        (positivePart-nonnegative y))
    ∙
    +-comm
      (nnMul (negativePart y) (positivePart x)
        (negativePart-nonnegative y)
        (positivePart-nonnegative x))
      (nnMul (positivePart y) (negativePart x)
        (positivePart-nonnegative y)
        (negativePart-nonnegative x))

  *-comm :
    (x y : DedekindCut ℓ) →
    x * y ≡ y * x
  *-comm x y =
    cong₂ _+_
      (positiveProducts-comm x y)
      (cong -_ (negativeProducts-comm x y))

  positiveProducts-nonnegative :
    (x y : DedekindCut ℓ) →
    Nonnegative (positiveProducts x y)
  positiveProducts-nonnegative x y =
    +-nonnegative
      (nnMul (positivePart x) (positivePart y)
        (positivePart-nonnegative x)
        (positivePart-nonnegative y))
      (nnMul (negativePart x) (negativePart y)
        (negativePart-nonnegative x)
        (negativePart-nonnegative y))
      (nnMul-nonnegative
        (positivePart x)
        (positivePart y)
        (positivePart-nonnegative x)
        (positivePart-nonnegative y))
      (nnMul-nonnegative
        (negativePart x)
        (negativePart y)
        (negativePart-nonnegative x)
        (negativePart-nonnegative y))

  negativeProducts-nonnegative :
    (x y : DedekindCut ℓ) →
    Nonnegative (negativeProducts x y)
  negativeProducts-nonnegative x y =
    +-nonnegative
      (nnMul (positivePart x) (negativePart y)
        (positivePart-nonnegative x)
        (negativePart-nonnegative y))
      (nnMul (negativePart x) (positivePart y)
        (negativePart-nonnegative x)
        (positivePart-nonnegative y))
      (nnMul-nonnegative
        (positivePart x)
        (negativePart y)
        (positivePart-nonnegative x)
        (negativePart-nonnegative y))
      (nnMul-nonnegative
        (negativePart x)
        (positivePart y)
        (negativePart-nonnegative x)
        (positivePart-nonnegative y))

  positiveProducts-of-nonnegative :
    (x y : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    (0≤y : Nonnegative y) →
    positiveProducts x y ≡ nnMul x y 0≤x 0≤y
  positiveProducts-of-nonnegative x y 0≤x 0≤y =
    cong₂ _+_ main-product zero-product ∙
    +-idR (nnMul x y 0≤x 0≤y)
    where
    main-product :
      nnMul (positivePart x) (positivePart y)
        (positivePart-nonnegative x)
        (positivePart-nonnegative y)
      ≡ nnMul x y 0≤x 0≤y
    main-product =
      nnMul-cong₂
        (positivePart x)
        x
        (positivePart y)
        y
        (positivePart-of-nonnegative x 0≤x)
        (positivePart-of-nonnegative y 0≤y)
        (positivePart-nonnegative x)
        0≤x
        (positivePart-nonnegative y)
        0≤y

    zero-product :
      nnMul (negativePart x) (negativePart y)
        (negativePart-nonnegative x)
        (negativePart-nonnegative y)
      ≡ 0D
    zero-product =
      nnMul-cong₂
        (negativePart x)
        0D
        (negativePart y)
        0D
        (negativePart-of-nonnegative x 0≤x)
        (negativePart-of-nonnegative y 0≤y)
        (negativePart-nonnegative x)
        0D-nonnegative
        (negativePart-nonnegative y)
        0D-nonnegative
      ∙ nnMul-zeroR 0D 0D-nonnegative

  negativeProducts-of-nonnegative :
    (x y : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    (0≤y : Nonnegative y) →
    negativeProducts x y ≡ 0D
  negativeProducts-of-nonnegative x y 0≤x 0≤y =
    cong₂ _+_ left-zero right-zero ∙
    +-idR 0D
    where
    left-zero :
      nnMul (positivePart x) (negativePart y)
        (positivePart-nonnegative x)
        (negativePart-nonnegative y)
      ≡ 0D
    left-zero =
      nnMul-cong₂
        (positivePart x)
        x
        (negativePart y)
        0D
        (positivePart-of-nonnegative x 0≤x)
        (negativePart-of-nonnegative y 0≤y)
        (positivePart-nonnegative x)
        0≤x
        (negativePart-nonnegative y)
        0D-nonnegative
      ∙ nnMul-zeroR x 0≤x

    right-zero :
      nnMul (negativePart x) (positivePart y)
        (negativePart-nonnegative x)
        (positivePart-nonnegative y)
      ≡ 0D
    right-zero =
      nnMul-cong₂
        (negativePart x)
        0D
        (positivePart y)
        y
        (negativePart-of-nonnegative x 0≤x)
        (positivePart-of-nonnegative y 0≤y)
        (negativePart-nonnegative x)
        0D-nonnegative
        (positivePart-nonnegative y)
        0≤y
      ∙ nnMul-zeroL y 0≤y

  *-of-nonnegative :
    (x y : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    (0≤y : Nonnegative y) →
    x * y ≡ nnMul x y 0≤x 0≤y
  *-of-nonnegative x y 0≤x 0≤y =
    cong₂ _+_
      (positiveProducts-of-nonnegative x y 0≤x 0≤y)
      (cong -_ (negativeProducts-of-nonnegative x y 0≤x 0≤y) ∙ neg-0D)
    ∙
    +-idR (nnMul x y 0≤x 0≤y)

  *-nonnegative :
    (x y : DedekindCut ℓ) →
    (0≤x : Nonnegative x) →
    (0≤y : Nonnegative y) →
    Nonnegative (x * y)
  *-nonnegative x y 0≤x 0≤y =
    ≤-trans
      0D
      (nnMul x y 0≤x 0≤y)
      (x * y)
      (nnMul-nonnegative x y 0≤x 0≤y)
      (≡→≤ (sym (*-of-nonnegative x y 0≤x 0≤y)))

  rightNonnegativeProduct :
    (x z : DedekindCut ℓ) →
    Nonnegative z →
    DedekindCut ℓ
  rightNonnegativeProduct x z 0≤z =
    nnMul (positivePart x) z
      (positivePart-nonnegative x)
      0≤z
    +
    (- nnMul (negativePart x) z
      (negativePart-nonnegative x)
      0≤z)

  positiveProducts-right-nonnegative :
    (x z : DedekindCut ℓ) →
    (0≤z : Nonnegative z) →
    positiveProducts x z ≡
      nnMul (positivePart x) z (positivePart-nonnegative x) 0≤z
  positiveProducts-right-nonnegative x z 0≤z =
    cong₂ _+_ first-product second-zero ∙
    +-idR (nnMul (positivePart x) z (positivePart-nonnegative x) 0≤z)
    where
    first-product :
      nnMul (positivePart x) (positivePart z)
        (positivePart-nonnegative x)
        (positivePart-nonnegative z)
      ≡ nnMul (positivePart x) z (positivePart-nonnegative x) 0≤z
    first-product =
      nnMul-congR
        (positivePart x)
        (positivePart z)
        z
        (positivePart-of-nonnegative z 0≤z)
        (positivePart-nonnegative x)
        (positivePart-nonnegative x)
        (positivePart-nonnegative z)
        0≤z

    second-zero :
      nnMul (negativePart x) (negativePart z)
        (negativePart-nonnegative x)
        (negativePart-nonnegative z)
      ≡ 0D
    second-zero =
      nnMul-congR
        (negativePart x)
        (negativePart z)
        0D
        (negativePart-of-nonnegative z 0≤z)
        (negativePart-nonnegative x)
        (negativePart-nonnegative x)
        (negativePart-nonnegative z)
        0D-nonnegative
      ∙ nnMul-zeroR (negativePart x) (negativePart-nonnegative x)

  negativeProducts-right-nonnegative :
    (x z : DedekindCut ℓ) →
    (0≤z : Nonnegative z) →
    negativeProducts x z ≡
      nnMul (negativePart x) z (negativePart-nonnegative x) 0≤z
  negativeProducts-right-nonnegative x z 0≤z =
    cong₂ _+_ first-zero second-product ∙
    +-idL (nnMul (negativePart x) z (negativePart-nonnegative x) 0≤z)
    where
    first-zero :
      nnMul (positivePart x) (negativePart z)
        (positivePart-nonnegative x)
        (negativePart-nonnegative z)
      ≡ 0D
    first-zero =
      nnMul-congR
        (positivePart x)
        (negativePart z)
        0D
        (negativePart-of-nonnegative z 0≤z)
        (positivePart-nonnegative x)
        (positivePart-nonnegative x)
        (negativePart-nonnegative z)
        0D-nonnegative
      ∙ nnMul-zeroR (positivePart x) (positivePart-nonnegative x)

    second-product :
      nnMul (negativePart x) (positivePart z)
        (negativePart-nonnegative x)
        (positivePart-nonnegative z)
      ≡ nnMul (negativePart x) z (negativePart-nonnegative x) 0≤z
    second-product =
      nnMul-congR
        (negativePart x)
        (positivePart z)
        z
        (positivePart-of-nonnegative z 0≤z)
        (negativePart-nonnegative x)
        (negativePart-nonnegative x)
        (positivePart-nonnegative z)
        0≤z

  *-right-nonnegative-form :
    (x z : DedekindCut ℓ) →
    (0≤z : Nonnegative z) →
    x * z ≡ rightNonnegativeProduct x z 0≤z
  *-right-nonnegative-form x z 0≤z =
    cong₂ _+_
      (positiveProducts-right-nonnegative x z 0≤z)
      (cong -_ (negativeProducts-right-nonnegative x z 0≤z))

  *-monoR-≤-nonnegative :
    (x y z : DedekindCut ℓ) →
    x ≤ y →
    (0≤z : Nonnegative z) →
    x * z ≤ y * z
  *-monoR-≤-nonnegative x y z x≤y 0≤z =
    ≤-trans (x * z) xz-form (y * z)
      (≡→≤ (*-right-nonnegative-form x z 0≤z))
      (≤-trans xz-form yz-form (y * z)
        form≤
        (≡→≤ (sym (*-right-nonnegative-form y z 0≤z))))
    where
    xz-form : DedekindCut ℓ
    xz-form = rightNonnegativeProduct x z 0≤z

    yz-form : DedekindCut ℓ
    yz-form = rightNonnegativeProduct y z 0≤z

    pos≤ :
      nnMul (positivePart x) z
        (positivePart-nonnegative x)
        0≤z
      ≤
      nnMul (positivePart y) z
        (positivePart-nonnegative y)
        0≤z
    pos≤ =
      nnMul-monoL-≤
        (positivePart x)
        (positivePart y)
        z
        (positivePart-nonnegative x)
        (positivePart-nonnegative y)
        0≤z
        (positivePart-mono-≤ x y x≤y)

    neg-prod≤ :
      nnMul (negativePart y) z
        (negativePart-nonnegative y)
        0≤z
      ≤
      nnMul (negativePart x) z
        (negativePart-nonnegative x)
        0≤z
    neg-prod≤ =
      nnMul-monoL-≤
        (negativePart y)
        (negativePart x)
        z
        (negativePart-nonnegative y)
        (negativePart-nonnegative x)
        0≤z
        (negativePart-antitone-≤ x y x≤y)

    neg≤ :
      (- nnMul (negativePart x) z
        (negativePart-nonnegative x)
        0≤z)
      ≤
      (- nnMul (negativePart y) z
        (negativePart-nonnegative y)
        0≤z)
    neg≤ =
      neg-≤-reverse
        (nnMul (negativePart y) z
          (negativePart-nonnegative y)
          0≤z)
        (nnMul (negativePart x) z
          (negativePart-nonnegative x)
          0≤z)
        neg-prod≤

    form≤ : xz-form ≤ yz-form
    form≤ =
      +-mono-≤
        (nnMul (positivePart x) z
          (positivePart-nonnegative x)
          0≤z)
        (nnMul (positivePart y) z
          (positivePart-nonnegative y)
          0≤z)
        (- nnMul (negativePart x) z
          (negativePart-nonnegative x)
          0≤z)
        (- nnMul (negativePart y) z
          (negativePart-nonnegative y)
          0≤z)
        pos≤
        neg≤

  *-monoL-≤-nonnegative :
    (x y z : DedekindCut ℓ) →
    x ≤ y →
    (0≤z : Nonnegative z) →
    z * x ≤ z * y
  *-monoL-≤-nonnegative x y z x≤y 0≤z =
    ≤-trans (z * x) (x * z) (z * y)
      (≡→≤ (*-comm z x))
      (≤-trans (x * z) (y * z) (z * y)
        (*-monoR-≤-nonnegative x y z x≤y 0≤z)
        (≡→≤ (sym (*-comm z y))))

  positiveProducts-zeroR :
    (x : DedekindCut ℓ) →
    positiveProducts x 0D ≡ 0D
  positiveProducts-zeroR x =
    cong₂ _+_ first-zero second-zero ∙
    +-idR 0D
    where
    first-zero :
      nnMul (positivePart x) (positivePart 0D)
        (positivePart-nonnegative x)
        (positivePart-nonnegative 0D)
      ≡ 0D
    first-zero =
      nnMul-congR
        (positivePart x)
        (positivePart 0D)
        0D
        positivePart-0D
        (positivePart-nonnegative x)
        (positivePart-nonnegative x)
        (positivePart-nonnegative 0D)
        0D-nonnegative
      ∙ nnMul-zeroR (positivePart x) (positivePart-nonnegative x)

    second-zero :
      nnMul (negativePart x) (negativePart 0D)
        (negativePart-nonnegative x)
        (negativePart-nonnegative 0D)
      ≡ 0D
    second-zero =
      nnMul-congR
        (negativePart x)
        (negativePart 0D)
        0D
        negativePart-0D
        (negativePart-nonnegative x)
        (negativePart-nonnegative x)
        (negativePart-nonnegative 0D)
        0D-nonnegative
      ∙ nnMul-zeroR (negativePart x) (negativePart-nonnegative x)

  negativeProducts-zeroR :
    (x : DedekindCut ℓ) →
    negativeProducts x 0D ≡ 0D
  negativeProducts-zeroR x =
    cong₂ _+_ first-zero second-zero ∙
    +-idR 0D
    where
    first-zero :
      nnMul (positivePart x) (negativePart 0D)
        (positivePart-nonnegative x)
        (negativePart-nonnegative 0D)
      ≡ 0D
    first-zero =
      nnMul-congR
        (positivePart x)
        (negativePart 0D)
        0D
        negativePart-0D
        (positivePart-nonnegative x)
        (positivePart-nonnegative x)
        (negativePart-nonnegative 0D)
        0D-nonnegative
      ∙ nnMul-zeroR (positivePart x) (positivePart-nonnegative x)

    second-zero :
      nnMul (negativePart x) (positivePart 0D)
        (negativePart-nonnegative x)
        (positivePart-nonnegative 0D)
      ≡ 0D
    second-zero =
      nnMul-congR
        (negativePart x)
        (positivePart 0D)
        0D
        positivePart-0D
        (negativePart-nonnegative x)
        (negativePart-nonnegative x)
        (positivePart-nonnegative 0D)
        0D-nonnegative
      ∙ nnMul-zeroR (negativePart x) (negativePart-nonnegative x)

  *-zeroR :
    (x : DedekindCut ℓ) →
    x * 0D ≡ 0D
  *-zeroR x =
    cong₂ _+_
      (positiveProducts-zeroR x)
      (cong -_ (negativeProducts-zeroR x) ∙ neg-0D)
    ∙
    +-idR 0D

  *-zeroL :
    (x : DedekindCut ℓ) →
    0D * x ≡ 0D
  *-zeroL x =
    *-comm 0D x ∙
    *-zeroR x
