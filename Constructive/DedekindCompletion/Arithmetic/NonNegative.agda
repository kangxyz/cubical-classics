{-

Nonnegative multiplication of constructive Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindCompletion.Arithmetic.NonNegative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

import Constructive.Algebra.LinearlyOrderedCommRing.Base as LinearBase
open import Constructive.Algebra.LinearlyOrderedCommRing
open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedes
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.DedekindCompletion
open import Constructive.DedekindCompletion.Arithmetic.Base
open import Constructive.DedekindCompletion.Arithmetic.AdditiveGroup

private
  variable
    ℓ ℓ' ℓᴾ : Level

  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    mul-error-split :
      (lx ux ly uy : 𝓡 .fst) →
      ux · uy ≡ lx · ly + (((ux - lx) · uy) + (lx · (uy - ly)))
    mul-error-split _ _ _ _ = solve! 𝓡

    denom>U-path :
      (U V gap : 𝓡 .fst) →
      U + ((V + gap) + 1r) ≡ ((U + V) + gap) + 1r
    denom>U-path _ _ _ = solve! 𝓡

    denom>V-path :
      (U V gap : 𝓡 .fst) →
      V + ((U + gap) + 1r) ≡ ((U + V) + gap) + 1r
    denom>V-path _ _ _ = solve! 𝓡

    denom>U+V-path :
      (U V gap : 𝓡 .fst) →
      (U + V) + (gap + 1r) ≡ ((U + V) + gap) + 1r
    denom>U+V-path _ _ _ = solve! 𝓡

    scale-cancelR-path :
      (ε M M⁻¹ : 𝓡 .fst) →
      M⁻¹ · M ≡ 1r →
      (ε · M⁻¹) · M ≡ ε
    scale-cancelR-path ε M M⁻¹ M⁻¹M≡1 =
      sym (·Assoc ε M⁻¹ M) ∙
      cong (ε ·_) M⁻¹M≡1 ∙
      ·IdR ε

    p+[q-p]≡q : (p q : 𝓡 .fst) → p + (q - p) ≡ q
    p+[q-p]≡q _ _ = solve! 𝓡

    [p-q]+q≡p : (p q : 𝓡 .fst) → (p - q) + q ≡ p
    [p-q]+q≡p _ _ = solve! 𝓡

    left-diff+ : (p q : 𝓡 .fst) → p + (q - p) ≡ q
    left-diff+ _ _ = solve! 𝓡

    mul-distrib-left :
      (a b c : 𝓡 .fst) →
      a · (b + c) ≡ (a · b) + (a · c)
    mul-distrib-left _ _ _ = solve! 𝓡

    δV+δU≡δUV :
      (δ U V : 𝓡 .fst) →
      (δ · V) + (δ · U) ≡ δ · (U + V)
    δV+δU≡δUV _ _ _ = solve! 𝓡


module NonNegativeMultiplication
  (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  𝒦₀ : LinearlyOrderedField ℓ ℓ'
  𝒦₀ = 𝒜 .fst

  arch : isArchimedean (𝒦₀ .fst)
  arch = 𝒜 .snd

  open CompletionBase 𝒦₀
  module OrdD = CompletionOrder 𝒦₀
  open LinearlyOrderedFieldStr 𝒦₀
  open Helpers (LinearlyOrderedCommRing→CommRing (𝒦₀ .fst))

  open ArithmeticBase 𝒜
  open Approximation {ℓᴾ}
  open Addition {ℓᴾ}

  private
    K : Type ℓ
    K = Carrier

    dense :
      {p q : K} →
      p < q →
      ∥ Σ[ r ∈ K ] (p < r) × (r < q) ∥₁
    dense {p = p} {q = q} p<q =
      ∣ middle p q , middle>l p<q , middle<r p<q ∣₁

    negative-or-nonnegative :
      (q : K) →
      (q < 0r) ⊎ (0r ≤ q)
    negative-or-nonnegative q with trichotomy 0r q
    ... | LinearBase.lt 0<q = Sum.inr (<-≤-weaken 0<q)
    ... | LinearBase.eq 0≡q = Sum.inr (≤-refl 0≡q)
    ... | LinearBase.gt q<0 = Sum.inl q<0

    nonnegative-right-of-< :
      {p q : K} →
      0r ≤ p →
      p < q →
      0r < q
    nonnegative-right-of-< = ≤<-trans

    n⋆1<sn⋆1 : (n : ℕ) → n ⋆ 1r < suc n ⋆ 1r
    n⋆1<sn⋆1 n =
      subst (n ⋆ 1r <_) (sym (sucn⋆q≡n⋆q+q n 1r))
        (subst (_< n ⋆ 1r + 1r) (+IdR (n ⋆ 1r))
          (+-lPres< {z = n ⋆ 1r} 1>0))

    mul-mono-positive-<≤ :
      {a b c d : K} →
      0r < a →
      0r < c →
      a < b →
      c ≤ d →
      a · c < b · d
    mul-mono-positive-<≤ 0<a 0<c a<b c≤d =
      ·-PosPres>≥ 0<a 0<c a<b c≤d

    scaleByPositive : (ε M : K) → 0r < M → K
    scaleByPositive ε M 0<M = ε · inv₊ 0<M

    scaleByPositive-positive :
      {ε M : K} →
      0r < ε →
      (0<M : 0r < M) →
      0r < scaleByPositive ε M 0<M
    scaleByPositive-positive 0<ε 0<M =
      ·-Pres>0 0<ε (p>0→p⁻¹>0 0<M)

    scaleByPositive-cancelR :
      (ε M : K) →
      (0<M : 0r < M) →
      scaleByPositive ε M 0<M · M ≡ ε
    scaleByPositive-cancelR ε M 0<M =
      scale-cancelR-path ε M (inv₊ 0<M) (·-lInv₊ 0<M)

    mulErrorDenom : K → K → K → K
    mulErrorDenom U V gap = ((U + V) + gap) + 1r

    mulErrorDenom-positive :
      {U V gap : K} →
      0r < U →
      0r < V →
      0r < gap →
      0r < mulErrorDenom U V gap
    mulErrorDenom-positive 0<U 0<V 0<gap =
      +-Pres>0 (+-Pres>0 (+-Pres>0 0<U 0<V) 0<gap) 1>0

    mulErrorScale :
      (gap U V : K) →
      0r < U →
      0r < V →
      0r < gap →
      K
    mulErrorScale gap U V 0<U 0<V 0<gap =
      scaleByPositive gap (mulErrorDenom U V gap)
        (mulErrorDenom-positive 0<U 0<V 0<gap)

    mulErrorScale-positive :
      {gap U V : K} →
      (0<U : 0r < U) →
      (0<V : 0r < V) →
      (0<gap : 0r < gap) →
      0r < mulErrorScale gap U V 0<U 0<V 0<gap
    mulErrorScale-positive 0<U 0<V 0<gap =
      scaleByPositive-positive 0<gap
        (mulErrorDenom-positive 0<U 0<V 0<gap)

    mulErrorDenom>U :
      {gap U V : K} →
      0r < V →
      0r < gap →
      U < mulErrorDenom U V gap
    mulErrorDenom>U {gap = gap} {U = U} {V = V} 0<V 0<gap =
      subst (U <_) (denom>U-path U V gap)
        (+-rPos→> (+-Pres>0 (+-Pres>0 0<V 0<gap) 1>0))

    mulErrorDenom>V :
      {gap U V : K} →
      0r < U →
      0r < gap →
      V < mulErrorDenom U V gap
    mulErrorDenom>V {gap = gap} {U = U} {V = V} 0<U 0<gap =
      subst (V <_) (denom>V-path U V gap)
        (+-rPos→> (+-Pres>0 (+-Pres>0 0<U 0<gap) 1>0))

    mulErrorDenom>U+V :
      {gap U V : K} →
      0r < gap →
      U + V < mulErrorDenom U V gap
    mulErrorDenom>U+V {gap = gap} {U = U} {V = V} 0<gap =
      subst (U + V <_) (denom>U+V-path U V gap)
        (+-rPos→> (+-Pres>0 0<gap 1>0))

    mulErrorScale-times-U<gap :
      {gap U V : K} →
      (0<U : 0r < U) →
      (0<V : 0r < V) →
      (0<gap : 0r < gap) →
      mulErrorScale gap U V 0<U 0<V 0<gap · U < gap
    mulErrorScale-times-U<gap {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap =
      subst (λ r → δ · U < r)
        (scaleByPositive-cancelR gap D 0<D)
        (·-lPosPres< 0<δ U<D)
      where
      D : K
      D = mulErrorDenom U V gap

      0<D : 0r < D
      0<D = mulErrorDenom-positive 0<U 0<V 0<gap

      δ : K
      δ = mulErrorScale gap U V 0<U 0<V 0<gap

      0<δ : 0r < δ
      0<δ = mulErrorScale-positive 0<U 0<V 0<gap

      U<D : U < D
      U<D = mulErrorDenom>U 0<V 0<gap

    mulErrorScale-times-V<gap :
      {gap U V : K} →
      (0<U : 0r < U) →
      (0<V : 0r < V) →
      (0<gap : 0r < gap) →
      mulErrorScale gap U V 0<U 0<V 0<gap · V < gap
    mulErrorScale-times-V<gap {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap =
      subst (λ r → δ · V < r)
        (scaleByPositive-cancelR gap D 0<D)
        (·-lPosPres< 0<δ V<D)
      where
      D : K
      D = mulErrorDenom U V gap

      0<D : 0r < D
      0<D = mulErrorDenom-positive 0<U 0<V 0<gap

      δ : K
      δ = mulErrorScale gap U V 0<U 0<V 0<gap

      0<δ : 0r < δ
      0<δ = mulErrorScale-positive 0<U 0<V 0<gap

      V<D : V < D
      V<D = mulErrorDenom>V 0<U 0<gap

    mulErrorScale-times-sum<gap :
      {gap U V : K} →
      (0<U : 0r < U) →
      (0<V : 0r < V) →
      (0<gap : 0r < gap) →
      mulErrorScale gap U V 0<U 0<V 0<gap · (U + V) < gap
    mulErrorScale-times-sum<gap {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap =
      subst (λ r → δ · (U + V) < r)
        (scaleByPositive-cancelR gap D 0<D)
        (·-lPosPres< 0<δ U+V<D)
      where
      D : K
      D = mulErrorDenom U V gap

      0<D : 0r < D
      0<D = mulErrorDenom-positive 0<U 0<V 0<gap

      δ : K
      δ = mulErrorScale gap U V 0<U 0<V 0<gap

      0<δ : 0r < δ
      0<δ = mulErrorScale-positive 0<U 0<V 0<gap

      U+V<D : U + V < D
      U+V<D = mulErrorDenom>U+V 0<gap

    add-nonpositive≤right :
      {p r : K} →
      p ≤ 0r →
      p + r ≤ r
    add-nonpositive≤right {p = p} {r = r} p≤0 =
      subst (_≤ r) (+Comm r p) (+-rNeg→≤ p≤0)

    diff≤right :
      {p q : K} →
      0r ≤ p →
      q - p ≤ q
    diff≤right {p = p} 0≤p =
      +-rNeg→≤
        (subst (- p ≤_) 0Selfinverse (-Reverse≤ 0≤p))

    mul-close-left-nonpositive-upper< :
      {q gap δ V lx ux uy : K} →
      lx ≤ 0r →
      ux < lx + δ →
      0r < ux →
      0r < uy →
      uy ≤ V →
      δ · V < gap →
      gap ≤ q →
      ux · uy < q
    mul-close-left-nonpositive-upper<
      {q = q} {gap = gap} {δ = δ} {V = V} {lx = lx} {ux = ux} {uy = uy}
      lx≤0 ux<lx+δ 0<ux 0<uy uy≤V δV<gap gap≤q =
      <≤-trans (<-trans uxuy<δV δV<gap) gap≤q
      where
      lx+δ≤δ : lx + δ ≤ δ
      lx+δ≤δ = add-nonpositive≤right lx≤0

      ux<δ : ux < δ
      ux<δ = <≤-trans ux<lx+δ lx+δ≤δ

      uxuy<δV : ux · uy < δ · V
      uxuy<δV =
        mul-mono-positive-<≤ 0<ux 0<uy ux<δ uy≤V

    mul-close-right-nonpositive-upper< :
      {q gap δ U ly ux uy : K} →
      ly ≤ 0r →
      uy < ly + δ →
      0r < ux →
      0r < uy →
      ux ≤ U →
      δ · U < gap →
      gap ≤ q →
      ux · uy < q
    mul-close-right-nonpositive-upper<
      {q = q} {gap = gap} {δ = δ} {U = U} {ly = ly} {ux = ux} {uy = uy}
      ly≤0 uy<ly+δ 0<ux 0<uy ux≤U δU<gap gap≤q =
      <≤-trans (<-trans uxuy<δU δU<gap) gap≤q
      where
      ly+δ≤δ : ly + δ ≤ δ
      ly+δ≤δ = add-nonpositive≤right ly≤0

      uy<δ : uy < δ
      uy<δ = <≤-trans uy<ly+δ ly+δ≤δ

      uyux<δU : uy · ux < δ · U
      uyux<δU =
        mul-mono-positive-<≤ 0<uy 0<ux uy<δ ux≤U

      uxuy<δU : ux · uy < δ · U
      uxuy<δU =
        subst (λ r → r < δ · U) (·Comm uy ux) uyux<δU

    mul-close-positive-upper< :
      {p q gap δ U V lx ux ly uy : K} →
      lx < ux →
      ly < uy →
      0r < lx →
      0r < ly →
      ux < lx + δ →
      uy < ly + δ →
      ux ≤ U →
      uy ≤ V →
      lx · ly ≤ p →
      δ · (U + V) < gap →
      p + gap ≡ q →
      ux · uy < q
    mul-close-positive-upper<
      {p = p} {q = q} {gap = gap} {δ = δ} {U = U} {V = V}
      {lx = lx} {ux = ux} {ly = ly} {uy = uy}
      lx<ux ly<uy 0<lx 0<ly ux<lx+δ uy<ly+δ ux≤U uy≤V lxly≤p δUV<gap p+gap≡q =
      subst (λ r → r < q)
        (sym (mul-error-split lx ux ly uy))
        rhs<q
      where
      err₁ : K
      err₁ = (ux - lx) · uy

      err₂ : K
      err₂ = lx · (uy - ly)

      0<uy : 0r < uy
      0<uy = <-trans 0<ly ly<uy

      ux<δ+lx : ux < δ + lx
      ux<δ+lx =
        subst (λ r → ux < r) (+Comm lx δ) ux<lx+δ

      ux-lx<δ : ux - lx < δ
      ux-lx<δ = +-MoveRToL< ux<δ+lx

      0<ux-lx : 0r < ux - lx
      0<ux-lx = <→Diff>0 lx<ux

      err₁<δV : err₁ < δ · V
      err₁<δV =
        mul-mono-positive-<≤ 0<ux-lx 0<uy ux-lx<δ uy≤V

      uy<δ+ly : uy < δ + ly
      uy<δ+ly =
        subst (λ r → uy < r) (+Comm ly δ) uy<ly+δ

      uy-ly<δ : uy - ly < δ
      uy-ly<δ = +-MoveRToL< uy<δ+ly

      0<uy-ly : 0r < uy - ly
      0<uy-ly = <→Diff>0 ly<uy

      lx≤ux : lx ≤ ux
      lx≤ux = <-≤-weaken lx<ux

      lx≤U : lx ≤ U
      lx≤U = ≤-trans lx≤ux ux≤U

      uy-ly*lx<δU : (uy - ly) · lx < δ · U
      uy-ly*lx<δU =
        mul-mono-positive-<≤ 0<uy-ly 0<lx uy-ly<δ lx≤U

      err₂<δU : err₂ < δ · U
      err₂<δU =
        subst (λ r → r < δ · U) (·Comm (uy - ly) lx) uy-ly*lx<δU

      err₁+err₂<δV+δU : err₁ + err₂ < (δ · V) + (δ · U)
      err₁+err₂<δV+δU =
        +-Pres< err₁<δV err₂<δU

      err₁+err₂<δUV : err₁ + err₂ < δ · (U + V)
      err₁+err₂<δUV =
        subst (λ r → err₁ + err₂ < r)
          (δV+δU≡δUV δ U V)
          err₁+err₂<δV+δU

      err₁+err₂<gap : err₁ + err₂ < gap
      err₁+err₂<gap = <-trans err₁+err₂<δUV δUV<gap

      base+err≤p+err :
        (lx · ly) + (err₁ + err₂) ≤ p + (err₁ + err₂)
      base+err≤p+err =
        +-rPres≤ lxly≤p

      p+err<p+gap : p + (err₁ + err₂) < p + gap
      p+err<p+gap =
        +-lPres< {z = p} err₁+err₂<gap

      rhs<p+gap :
        (lx · ly) + (err₁ + err₂) < p + gap
      rhs<p+gap =
        ≤<-trans base+err≤p+err p+err<p+gap

      rhs<q :
        (lx · ly) + (err₁ + err₂) < q
      rhs<q =
        subst (λ r → (lx · ly) + (err₁ + err₂) < r)
          p+gap≡q
          rhs<p+gap

  _≥0 : DedekindCompletion ℓᴾ → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  x ≥0 = OrdD._≤_ 0𝔻 x

  infix 4 _≥0

  0𝔻≥0 : 0𝔻 ≥0
  0𝔻≥0 = OrdD.≤-refl 0𝔻

  1𝔻≥0 : 1𝔻 ≥0
  1𝔻≥0 q q∈L0 =
    lift (<-trans (Lift.lower q∈L0) 1>0)

  ≥0+upper→>0 :
    (x : DedekindCompletion ℓᴾ) →
    x ≥0 →
    (q : K) →
    q ∈ upper x →
    0r < q
  ≥0+upper→>0 x 0≤x q q∈Ux with trichotomy 0r q
  ... | LinearBase.lt 0<q = 0<q
  ... | LinearBase.eq 0≡q =
    Empty.rec
      (Prop.rec Empty.isProp⊥
        (λ (r , r<q , r∈Ux) →
          let
            r<0 : r < 0r
            r<0 =
              subst (λ v → r < v) (sym 0≡q) r<q
          in
          CompletionBase.disjoint {𝒦 = 𝒦₀} x r (0≤x r (lift r<0)) r∈Ux)
        (CompletionBase.upper-rounded {𝒦 = 𝒦₀} x q q∈Ux))
  ... | LinearBase.gt q<0 =
    Empty.rec
      (CompletionBase.disjoint {𝒦 = 𝒦₀} x q (0≤x q (lift q<0)) q∈Ux)

  ProductLowerWitness :
    DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → K → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  ProductLowerWitness x y q =
    Σ[ a ∈ K ] Σ[ b ∈ K ]
      (a ∈ lower x) ×
      (b ∈ lower y) ×
      (0r < a) ×
      (0r < b) ×
      (q < a · b)

  ProductUpperWitness :
    DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → K → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  ProductUpperWitness x y q =
    Σ[ a ∈ K ] Σ[ b ∈ K ]
      (a ∈ upper x) ×
      (b ∈ upper y) ×
      (0r < a) ×
      (0r < b) ×
      (a · b < q)

  CloseBounds≥0 : DedekindCompletion ℓᴾ → K → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  CloseBounds≥0 x ε =
    Σ[ p ∈ K ] Σ[ q ∈ K ]
      (p ∈ lower x) ×
      (q ∈ upper x) ×
      (p < q) ×
      (q < p + ε) ×
      (0r < q)

  BoundedCloseBounds≥0 :
    DedekindCompletion ℓᴾ → K → K → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  BoundedCloseBounds≥0 x ε u =
    Σ[ p ∈ K ] Σ[ q ∈ K ]
      (p ∈ lower x) ×
      (q ∈ upper x) ×
      (p < q) ×
      (q < p + ε) ×
      (0r < q) ×
      (q ≤ u)

  close-bounds≥0 :
    (x : DedekindCompletion ℓᴾ) →
    x ≥0 →
    (ε : K) →
    0r < ε →
    ∥ CloseBounds≥0 x ε ∥₁
  close-bounds≥0 x 0≤x ε 0<ε =
    Prop.rec squash₁
      (λ (p , q , p∈Lx , q∈Ux , p<q , q<p+ε) →
        ∣ p , q
        , p∈Lx
        , q∈Ux
        , p<q
        , q<p+ε
        , ≥0+upper→>0 x 0≤x q q∈Ux
        ∣₁)
      (close-bounds x ε 0<ε)

  bounded-close-bounds≥0 :
    (x : DedekindCompletion ℓᴾ) →
    x ≥0 →
    (ε u : K) →
    0r < ε →
    u ∈ upper x →
    ∥ BoundedCloseBounds≥0 x ε u ∥₁
  bounded-close-bounds≥0 x 0≤x ε u 0<ε u∈Ux =
    Prop.rec squash₁
      (λ (p , q , p∈Lx , q∈Ux , p<q , q<p+ε , q≤u) →
        ∣ p , q
        , p∈Lx
        , q∈Ux
        , p<q
        , q<p+ε
        , ≥0+upper→>0 x 0≤x q q∈Ux
        , q≤u
        ∣₁)
      (bounded-close-bounds x ε u 0<ε u∈Ux)

  MultiplicationCloseBounds :
    DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → K → K → K →
    Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  MultiplicationCloseBounds x y δ U V =
    Σ[ lx ∈ K ] Σ[ ux ∈ K ] Σ[ ly ∈ K ] Σ[ uy ∈ K ]
      (lx ∈ lower x) ×
      (ux ∈ upper x) ×
      (lx < ux) ×
      (ux < lx + δ) ×
      (0r < ux) ×
      (ux ≤ U) ×
      (ly ∈ lower y) ×
      (uy ∈ upper y) ×
      (ly < uy) ×
      (uy < ly + δ) ×
      (0r < uy) ×
      (uy ≤ V)

  multiplication-close-bounds :
    (x y : DedekindCompletion ℓᴾ) →
    x ≥0 →
    y ≥0 →
    (δ U V : K) →
    0r < δ →
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
      (bounded-close-bounds≥0 x 0≤x δ U 0<δ U∈Ux)
      (bounded-close-bounds≥0 y 0≤y δ V 0<δ V∈Uy)

  nnMulLower : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → Pred ℓᴾ
  nnMulLower x y q =
    ∥ (q < 0r) ⊎ ProductLowerWitness x y q ∥₁ ,
    squash₁

  nnMulUpper : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → Pred ℓᴾ
  nnMulUpper x y q =
    (0r < q) × ∥ ProductUpperWitness x y q ∥₁ ,
    isProp× isProp< squash₁

  ∃upper>0 :
    (x : DedekindCompletion ℓᴾ) →
    ∥ Σ[ u ∈ K ] (u ∈ upper x) × (0r < u) ∥₁
  ∃upper>0 x =
    Prop.rec squash₁
      (λ (q , q∈Ux) →
        let
          n : ℕ
          n = fst (arch q 1r 1>0)

          q<n : q < n ⋆ 1r
          q<n = snd (arch q 1r 1>0)

          u : K
          u = suc n ⋆ 1r

          q<u : q < u
          q<u = <-trans q<n (n⋆1<sn⋆1 n)
        in
        ∣ u
        , CompletionBase.upper-closed {𝒦 = 𝒦₀} x q u q<u q∈Ux
        , sucn⋆q>0 n 1r 1>0
        ∣₁)
      (CompletionBase.upper-inhabited {𝒦 = 𝒦₀} x)

  nnMul-lower-inhabited :
    (x y : DedekindCompletion ℓᴾ) →
    ∥ Σ[ q ∈ K ] q ∈ nnMulLower x y ∥₁
  nnMul-lower-inhabited x y =
    ∣ - 1r , ∣ Sum.inl (-Reverse>0 1>0) ∣₁ ∣₁

  nnMul-upper-inhabited :
    (x y : DedekindCompletion ℓᴾ) →
    ∥ Σ[ q ∈ K ] q ∈ nnMulUpper x y ∥₁
  nnMul-upper-inhabited x y =
    Prop.rec2 squash₁
      (λ (a , a∈Ux , 0<a) (b , b∈Uy , 0<b) →
        let
          ab : K
          ab = a · b

          q : K
          q = ab + 1r

          0<ab : 0r < ab
          0<ab = ·-Pres>0 0<a 0<b

          ab<q : ab < q
          ab<q = q+1>q

          0<q : 0r < q
          0<q = <-trans 0<ab ab<q
        in
        ∣ q , 0<q , ∣ a , b , a∈Ux , b∈Uy , 0<a , 0<b , ab<q ∣₁ ∣₁)
      (∃upper>0 x)
      (∃upper>0 y)

  nnMul-lower-closed :
    (x y : DedekindCompletion ℓᴾ) (p q : K) →
    p < q →
    q ∈ nnMulLower x y →
    p ∈ nnMulLower x y
  nnMul-lower-closed x y p q p<q =
    Prop.rec squash₁
      (λ where
        (Sum.inl q<0) →
          ∣ Sum.inl (<-trans p<q q<0) ∣₁
        (Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , q<ab)) →
          ∣ Sum.inr
              (a , b , a∈Lx , b∈Ly , 0<a , 0<b , <-trans p<q q<ab)
          ∣₁)

  nnMul-upper-closed :
    (x y : DedekindCompletion ℓᴾ) (p q : K) →
    p < q →
    p ∈ nnMulUpper x y →
    q ∈ nnMulUpper x y
  nnMul-upper-closed x y p q p<q (0<p , p∈U) =
    <-trans 0<p p<q ,
    Prop.rec squash₁
      (λ (a , b , a∈Ux , b∈Uy , 0<a , 0<b , ab<p) →
        ∣ a , b , a∈Ux , b∈Uy , 0<a , 0<b
        , <-trans ab<p p<q
        ∣₁)
      p∈U

  nnMul-lower-rounded :
    (x y : DedekindCompletion ℓᴾ) (q : K) →
    q ∈ nnMulLower x y →
    ∥ Σ[ r ∈ K ] (q < r) × (r ∈ nnMulLower x y) ∥₁
  nnMul-lower-rounded x y q =
    Prop.rec squash₁
      (λ where
        (Sum.inl q<0) →
          Prop.rec squash₁
            (λ (r , q<r , r<0) →
              ∣ r , q<r , ∣ Sum.inl r<0 ∣₁ ∣₁)
            (dense q<0)
        (Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , q<ab)) →
          Prop.rec squash₁
            (λ (r , q<r , r<ab) →
              ∣ r , q<r
              , ∣ Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , r<ab) ∣₁
              ∣₁)
            (dense q<ab))

  nnMul-upper-rounded :
    (x y : DedekindCompletion ℓᴾ) (q : K) →
    q ∈ nnMulUpper x y →
    ∥ Σ[ r ∈ K ] (r < q) × (r ∈ nnMulUpper x y) ∥₁
  nnMul-upper-rounded x y q (0<q , q∈U) =
    Prop.rec squash₁
      (λ (a , b , a∈Ux , b∈Uy , 0<a , 0<b , ab<q) →
        Prop.rec squash₁
          (λ (r , ab<r , r<q) →
            ∣ r , r<q
            , <-trans (·-Pres>0 0<a 0<b) ab<r
            , ∣ a , b , a∈Ux , b∈Uy , 0<a , 0<b , ab<r ∣₁
            ∣₁)
          (dense ab<q))
      q∈U

  nnMul-disjoint :
    (x y : DedekindCompletion ℓᴾ) (q : K) →
    q ∈ nnMulLower x y →
    q ∈ nnMulUpper x y →
    ⊥
  nnMul-disjoint x y q q∈L (0<q , q∈U) =
    Prop.rec Empty.isProp⊥ lower-case q∈L
    where
    lower-case :
      (q < 0r) ⊎ ProductLowerWitness x y q →
      ⊥
    lower-case (Sum.inl q<0) =
      <-arefl (<-trans q<0 0<q) refl
    lower-case (Sum.inr (a , b , a∈Lx , b∈Ly , 0<a , 0<b , q<ab)) =
      Prop.rec Empty.isProp⊥
        (λ (c , d , c∈Ux , d∈Uy , 0<c , 0<d , cd<q) →
          let
            a<c : a < c
            a<c = OrdD.lower<upper x a c a∈Lx c∈Ux

            b<d : b < d
            b<d = OrdD.lower<upper y b d b∈Ly d∈Uy

            ab<cd : a · b < c · d
            ab<cd = ·-PosPres> 0<a 0<b a<c b<d

            q<q : q < q
            q<q = <-trans q<ab (<-trans ab<cd cd<q)
          in
          <-arefl q<q refl)
        q∈U

  nnMulLower-comm :
    (x y : DedekindCompletion ℓᴾ) →
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
              , subst (λ v → q < v) (·Comm a b) q<ab)
          ∣₁)

  nnMulUpper-comm :
    (x y : DedekindCompletion ℓᴾ) →
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
        , subst (λ v → v < q) (·Comm a b) ab<q
        ∣₁)
      q∈U

  located-multiplication-scale :
    (p q U V : K) →
    p < q →
    0r < U →
    0r < V →
    K
  located-multiplication-scale p q U V p<q 0<U 0<V =
    mulErrorScale (q - p) U V 0<U 0<V (<→Diff>0 p<q)

  located-multiplication-scale-positive :
    (p q U V : K) →
    (p<q : p < q) →
    (0<U : 0r < U) →
    (0<V : 0r < V) →
    0r < located-multiplication-scale p q U V p<q 0<U 0<V
  located-multiplication-scale-positive p q U V p<q 0<U 0<V =
    mulErrorScale-positive 0<U 0<V (<→Diff>0 p<q)

  nnMul-lower-from-negative :
    (x y : DedekindCompletion ℓᴾ) →
    (q : K) →
    q < 0r →
    q ∈ nnMulLower x y
  nnMul-lower-from-negative x y q q<0 =
    ∣ Sum.inl q<0 ∣₁

  nnMul-lower-from-product :
    (x y : DedekindCompletion ℓᴾ) →
    (q : K) →
    ProductLowerWitness x y q →
    q ∈ nnMulLower x y
  nnMul-lower-from-product x y q witness =
    ∣ Sum.inr witness ∣₁

  nnMul-upper-from-product :
    (x y : DedekindCompletion ℓᴾ) →
    (q : K) →
    0r < q →
    ProductUpperWitness x y q →
    q ∈ nnMulUpper x y
  nnMul-upper-from-product x y q 0<q witness =
    0<q , ∣ witness ∣₁

  nnMulLocated :
    DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ →
    Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  nnMulLocated x y =
    (p q : K) →
    p < q →
    ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁

  nnMul-located-negative-left :
    (x y : DedekindCompletion ℓᴾ) →
    (p q : K) →
    p < 0r →
    ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁
  nnMul-located-negative-left x y p q p<0 =
    ∣ Sum.inl (nnMul-lower-from-negative x y p p<0) ∣₁

  nnMul-located-lower-product :
    (x y : DedekindCompletion ℓᴾ) →
    (p q : K) →
    ProductLowerWitness x y p →
    ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁
  nnMul-located-lower-product x y p q witness =
    ∣ Sum.inl (nnMul-lower-from-product x y p witness) ∣₁

  nnMul-located-upper-product :
    (x y : DedekindCompletion ℓᴾ) →
    (p q : K) →
    0r < q →
    ProductUpperWitness x y q →
    ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁
  nnMul-located-upper-product x y p q 0<q witness =
    ∣ Sum.inr (nnMul-upper-from-product x y q 0<q witness) ∣₁

  nnMul-located-by-p-sign :
    (x y : DedekindCompletion ℓᴾ) →
    (p q : K) →
    p < q →
    ((0≤p : 0r ≤ p) →
      0r < q →
      ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁) →
    ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁
  nnMul-located-by-p-sign x y p q p<q nonnegative-case
    with negative-or-nonnegative p
  ... | Sum.inl p<0 =
    nnMul-located-negative-left x y p q p<0
  ... | Sum.inr 0≤p =
    nonnegative-case 0≤p (nonnegative-right-of-< 0≤p p<q)

  nnMul-upper-witness-left-nonpositive :
    (x y : DedekindCompletion ℓᴾ) →
    (p q U V lx ux uy : K) →
    (p<q : p < q) →
    0r ≤ p →
    (0<U : 0r < U) →
    (0<V : 0r < V) →
    lx ≤ 0r →
    ux ∈ upper x →
    uy ∈ upper y →
    ux < lx + located-multiplication-scale p q U V p<q 0<U 0<V →
    0r < ux →
    0r < uy →
    uy ≤ V →
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
    gap : K
    gap = q - p

    0<gap : 0r < gap
    0<gap = <→Diff>0 p<q

    δ : K
    δ = located-multiplication-scale p q U V p<q 0<U 0<V

    δV<gap : δ · V < gap
    δV<gap = mulErrorScale-times-V<gap 0<U 0<V 0<gap

    gap≤q : gap ≤ q
    gap≤q = diff≤right 0≤p

    uxuy<q : ux · uy < q
    uxuy<q =
      mul-close-left-nonpositive-upper<
        {q = q} {gap = gap} {δ = δ} {V = V}
        {lx = lx} {ux = ux} {uy = uy}
        lx≤0 ux<lx+δ 0<ux 0<uy uy≤V δV<gap gap≤q

  nnMul-upper-witness-right-nonpositive :
    (x y : DedekindCompletion ℓᴾ) →
    (p q U V ly ux uy : K) →
    (p<q : p < q) →
    0r ≤ p →
    (0<U : 0r < U) →
    (0<V : 0r < V) →
    ly ≤ 0r →
    ux ∈ upper x →
    uy ∈ upper y →
    uy < ly + located-multiplication-scale p q U V p<q 0<U 0<V →
    0r < ux →
    0r < uy →
    ux ≤ U →
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
    gap : K
    gap = q - p

    0<gap : 0r < gap
    0<gap = <→Diff>0 p<q

    δ : K
    δ = located-multiplication-scale p q U V p<q 0<U 0<V

    δU<gap : δ · U < gap
    δU<gap = mulErrorScale-times-U<gap 0<U 0<V 0<gap

    gap≤q : gap ≤ q
    gap≤q = diff≤right 0≤p

    uxuy<q : ux · uy < q
    uxuy<q =
      mul-close-right-nonpositive-upper<
        {q = q} {gap = gap} {δ = δ} {U = U}
        {ly = ly} {ux = ux} {uy = uy}
        ly≤0 uy<ly+δ 0<ux 0<uy ux≤U δU<gap gap≤q

  nnMul-upper-witness-positive :
    (x y : DedekindCompletion ℓᴾ) →
    (p q U V lx ux ly uy : K) →
    (p<q : p < q) →
    (0<U : 0r < U) →
    (0<V : 0r < V) →
    lx < ux →
    ly < uy →
    0r < lx →
    0r < ly →
    ux ∈ upper x →
    uy ∈ upper y →
    ux < lx + located-multiplication-scale p q U V p<q 0<U 0<V →
    uy < ly + located-multiplication-scale p q U V p<q 0<U 0<V →
    ux ≤ U →
    uy ≤ V →
    lx · ly ≤ p →
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
    gap : K
    gap = q - p

    0<gap : 0r < gap
    0<gap = <→Diff>0 p<q

    δ : K
    δ = located-multiplication-scale p q U V p<q 0<U 0<V

    0<ux : 0r < ux
    0<ux = <-trans 0<lx lx<ux

    0<uy : 0r < uy
    0<uy = <-trans 0<ly ly<uy

    δUV<gap : δ · (U + V) < gap
    δUV<gap = mulErrorScale-times-sum<gap 0<U 0<V 0<gap

    uxuy<q : ux · uy < q
    uxuy<q =
      mul-close-positive-upper<
        {p = p} {q = q} {gap = gap} {δ = δ}
        {U = U} {V = V} {lx = lx} {ux = ux} {ly = ly} {uy = uy}
        lx<ux ly<uy 0<lx 0<ly
        ux<lx+δ
        uy<ly+δ
        ux≤U uy≤V lxly≤p δUV<gap
        (p+[q-p]≡q p q)

  nnMul-located :
    (x y : DedekindCompletion ℓᴾ) →
    x ≥0 →
    y ≥0 →
    nnMulLocated x y
  nnMul-located x y 0≤x 0≤y p q p<q =
    nnMul-located-by-p-sign x y p q p<q located-nonnegative-p
    where
    located-nonnegative-p :
      (0≤p : 0r ≤ p) →
      0r < q →
      ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁
    located-nonnegative-p 0≤p 0<q =
      Prop.rec2 squash₁
        (λ (U , U∈Ux , 0<U) (V , V∈Uy , 0<V) →
          let
            δ : K
            δ = located-multiplication-scale p q U V p<q 0<U 0<V

            0<δ : 0r < δ
            0<δ =
              located-multiplication-scale-positive p q U V p<q 0<U 0<V
          in
          Prop.rec squash₁
            (located-from-bounds U V 0<U 0<V)
            (multiplication-close-bounds x y 0≤x 0≤y δ U V 0<δ U∈Ux V∈Uy))
        (∃upper>0 x)
        (∃upper>0 y)
      where
      located-from-bounds :
        (U V : K) →
        (0<U : 0r < U) →
        (0<V : 0r < V) →
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
        case-lx (trichotomy 0r lx)
        where
        Result : Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
        Result = ∥ (p ∈ nnMulLower x y) ⊎ (q ∈ nnMulUpper x y) ∥₁

        δ : K
        δ = located-multiplication-scale p q U V p<q 0<U 0<V

        case-prod :
          0r < lx →
          0r < ly →
          LinearBase.Trichotomy (𝒦₀ .fst .fst) p (lx · ly) →
          Result
        case-prod 0<lx 0<ly (LinearBase.lt p<lxly) =
          nnMul-located-lower-product x y p q
            (lx , ly , lx∈Lx , ly∈Ly , 0<lx , 0<ly , p<lxly)
        case-prod 0<lx 0<ly (LinearBase.eq p≡lxly) =
          nnMul-located-upper-product x y p q 0<q
            (nnMul-upper-witness-positive
              x y p q U V lx ux ly uy p<q 0<U 0<V
              lx<ux ly<uy 0<lx 0<ly
              ux∈Ux uy∈Uy
              ux<lx+δ
              uy<ly+δ
              ux≤U uy≤V
              (≤-refl (sym p≡lxly)))
        case-prod 0<lx 0<ly (LinearBase.gt lxly<p) =
          nnMul-located-upper-product x y p q 0<q
            (nnMul-upper-witness-positive
              x y p q U V lx ux ly uy p<q 0<U 0<V
              lx<ux ly<uy 0<lx 0<ly
              ux∈Ux uy∈Uy
              ux<lx+δ
              uy<ly+δ
              ux≤U uy≤V
              (<-≤-weaken lxly<p))

        case-ly :
          0r < lx →
          LinearBase.Trichotomy (𝒦₀ .fst .fst) 0r ly →
          Result
        case-ly 0<lx (LinearBase.lt 0<ly) =
          case-prod 0<lx 0<ly (trichotomy p (lx · ly))
        case-ly 0<lx (LinearBase.eq 0≡ly) =
          nnMul-located-upper-product x y p q 0<q
            (nnMul-upper-witness-right-nonpositive
              x y p q U V ly ux uy p<q 0≤p 0<U 0<V
              (≤-refl (sym 0≡ly))
              ux∈Ux uy∈Uy
              uy<ly+δ
              0<ux 0<uy ux≤U)
        case-ly 0<lx (LinearBase.gt ly<0) =
          nnMul-located-upper-product x y p q 0<q
            (nnMul-upper-witness-right-nonpositive
              x y p q U V ly ux uy p<q 0≤p 0<U 0<V
              (<-≤-weaken ly<0)
              ux∈Ux uy∈Uy
              uy<ly+δ
              0<ux 0<uy ux≤U)

        case-lx :
          LinearBase.Trichotomy (𝒦₀ .fst .fst) 0r lx →
          Result
        case-lx (LinearBase.lt 0<lx) =
          case-ly 0<lx (trichotomy 0r ly)
        case-lx (LinearBase.eq 0≡lx) =
          nnMul-located-upper-product x y p q 0<q
            (nnMul-upper-witness-left-nonpositive
              x y p q U V lx ux uy p<q 0≤p 0<U 0<V
              (≤-refl (sym 0≡lx))
              ux∈Ux uy∈Uy
              ux<lx+δ
              0<ux 0<uy uy≤V)
        case-lx (LinearBase.gt lx<0) =
          nnMul-located-upper-product x y p q 0<q
            (nnMul-upper-witness-left-nonpositive
              x y p q U V lx ux uy p<q 0≤p 0<U 0<V
              (<-≤-weaken lx<0)
              ux∈Ux uy∈Uy
              ux<lx+δ
              0<ux 0<uy uy≤V)

  isDedekindCutNNMul :
    (x y : DedekindCompletion ℓᴾ) →
    nnMulLocated x y →
    IsDedekindCut (nnMulLower x y) (nnMulUpper x y)
  isDedekindCutNNMul x y located .IsDedekindCut.lower-inhabited =
    nnMul-lower-inhabited x y
  isDedekindCutNNMul x y located .IsDedekindCut.upper-inhabited =
    nnMul-upper-inhabited x y
  isDedekindCutNNMul x y located .IsDedekindCut.lower-closed =
    nnMul-lower-closed x y
  isDedekindCutNNMul x y located .IsDedekindCut.upper-closed =
    nnMul-upper-closed x y
  isDedekindCutNNMul x y located .IsDedekindCut.lower-rounded =
    nnMul-lower-rounded x y
  isDedekindCutNNMul x y located .IsDedekindCut.upper-rounded =
    nnMul-upper-rounded x y
  isDedekindCutNNMul x y located .IsDedekindCut.disjoint =
    nnMul-disjoint x y
  isDedekindCutNNMul x y located .IsDedekindCut.located =
    located

  nnMulCut :
    (x y : DedekindCompletion ℓᴾ) →
    nnMulLocated x y →
    DedekindCompletion ℓᴾ
  nnMulCut x y located .lower = nnMulLower x y
  nnMulCut x y located .upper = nnMulUpper x y
  nnMulCut x y located .isDedekindCut = isDedekindCutNNMul x y located

  nnMul :
    (x y : DedekindCompletion ℓᴾ) →
    x ≥0 →
    y ≥0 →
    DedekindCompletion ℓᴾ
  nnMul x y 0≤x 0≤y =
    nnMulCut x y (nnMul-located x y 0≤x 0≤y)

  nnMul-comm :
    (x y : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    nnMul x y 0≤x 0≤y ≡ nnMul y x 0≤y 0≤x
  nnMul-comm x y 0≤x 0≤y =
    completionExt
      (nnMul x y 0≤x 0≤y)
      (nnMul y x 0≤y 0≤x)
      (nnMulLower-comm x y)
      (nnMulLower-comm y x)
      (nnMulUpper-comm x y)
      (nnMulUpper-comm y x)

  nnMul-zeroR :
    (x : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    nnMul x 0𝔻 0≤x 0𝔻≥0 ≡ 0𝔻
  nnMul-zeroR x 0≤x =
    completionExt
      (nnMul x 0𝔻 0≤x 0𝔻≥0)
      0𝔻
      lower⊆
      lower⊇
      upper⊆
      upper⊇
    where
    lower⊆ : nnMulLower x 0𝔻 ⊆ lower 0𝔻
    lower⊆ q =
      Prop.rec (isProp∈ (lower 0𝔻) q)
        (λ where
          (Sum.inl q<0) → lift q<0
          (Sum.inr (a , b , a∈Lx , b∈L0 , 0<a , 0<b , q<ab)) →
            Empty.rec (<-asym 0<b (Lift.lower b∈L0)))

    lower⊇ : lower 0𝔻 ⊆ nnMulLower x 0𝔻
    lower⊇ q q∈L0 =
      ∣ Sum.inl (Lift.lower q∈L0) ∣₁

    upper⊆ : nnMulUpper x 0𝔻 ⊆ upper 0𝔻
    upper⊆ q (0<q , _) =
      lift 0<q

    upper⊇ : upper 0𝔻 ⊆ nnMulUpper x 0𝔻
    upper⊇ q q∈U0 =
      0<q ,
      Prop.rec squash₁
        (λ (a , a∈Ux , 0<a) →
          let
            b : K
            b = scaleByPositive ε a 0<a

            0<b : 0r < b
            0<b = scaleByPositive-positive 0<ε 0<a

            ab≡ε : a · b ≡ ε
            ab≡ε =
              ·Comm a b ∙ scaleByPositive-cancelR ε a 0<a

            ab<q : a · b < q
            ab<q =
              subst (λ r → r < q) (sym ab≡ε) ε<q
          in
          ∣ a , b , a∈Ux , lift 0<b , 0<a , 0<b , ab<q ∣₁)
        (∃upper>0 x)
      where
      0<q : 0r < q
      0<q = Lift.lower q∈U0

      ε : K
      ε = middle 0r q

      0<ε : 0r < ε
      0<ε = middle>l 0<q

      ε<q : ε < q
      ε<q = middle<r 0<q

  nnMul-zeroL :
    (x : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    nnMul 0𝔻 x 0𝔻≥0 0≤x ≡ 0𝔻
  nnMul-zeroL x 0≤x =
    nnMul-comm 0𝔻 x 0𝔻≥0 0≤x ∙
    nnMul-zeroR x 0≤x

  nnMul-Pres≥0 :
    (x y : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (nnMul x y 0≤x 0≤y) ≥0
  nnMul-Pres≥0 x y 0≤x 0≤y q q∈L0 =
    ∣ Sum.inl (Lift.lower q∈L0) ∣₁

  nnMul-monoL-≤ :
    (x x' y : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤x' : x' ≥0) →
    (0≤y : y ≥0) →
    OrdD._≤_ x x' →
    OrdD._≤_ (nnMul x y 0≤x 0≤y) (nnMul x' y 0≤x' 0≤y)
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
    (x y y' : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (0≤y' : y' ≥0) →
    OrdD._≤_ y y' →
    OrdD._≤_ (nnMul x y 0≤x 0≤y) (nnMul x y' 0≤x 0≤y')
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
    (x x' y y' : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤x' : x' ≥0) →
    (0≤y : y ≥0) →
    (0≤y' : y' ≥0) →
    OrdD._≤_ x x' →
    OrdD._≤_ y y' →
    OrdD._≤_ (nnMul x y 0≤x 0≤y) (nnMul x' y' 0≤x' 0≤y')
  nnMul-mono-≤ x x' y y' 0≤x 0≤x' 0≤y 0≤y' x≤x' y≤y' =
    OrdD.≤-trans
      (nnMul x y 0≤x 0≤y)
      (nnMul x' y 0≤x' 0≤y)
      (nnMul x' y' 0≤x' 0≤y')
      (nnMul-monoL-≤ x x' y 0≤x 0≤x' 0≤y x≤x')
      (nnMul-monoR-≤ x' y y' 0≤x' 0≤y 0≤y' y≤y')

  nnMul-proof-irrelevant :
    (x y : DedekindCompletion ℓᴾ) →
    (0≤x 0≤x' : x ≥0) →
    (0≤y 0≤y' : y ≥0) →
    nnMul x y 0≤x 0≤y ≡ nnMul x y 0≤x' 0≤y'
  nnMul-proof-irrelevant x y 0≤x 0≤x' 0≤y 0≤y' =
    completionExt
      (nnMul x y 0≤x 0≤y)
      (nnMul x y 0≤x' 0≤y')
      (λ q q∈L → q∈L)
      (λ q q∈L → q∈L)
      (λ q q∈U → q∈U)
      (λ q q∈U → q∈U)

  nnMul-congR :
    (x y y' : DedekindCompletion ℓᴾ) →
    y ≡ y' →
    (0≤x 0≤x' : x ≥0) →
    (0≤y : y ≥0) →
    (0≤y' : y' ≥0) →
    nnMul x y 0≤x 0≤y ≡ nnMul x y' 0≤x' 0≤y'
  nnMul-congR x y y' y≡y' 0≤x 0≤x' 0≤y 0≤y' =
    completionExt
      (nnMul x y 0≤x 0≤y)
      (nnMul x y' 0≤x' 0≤y')
      (lower-map y y' y≡y')
      (lower-map y' y (sym y≡y'))
      (upper-map y y' y≡y')
      (upper-map y' y (sym y≡y'))
    where
    lower-map :
      (z z' : DedekindCompletion ℓᴾ) →
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
      (z z' : DedekindCompletion ℓᴾ) →
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
    (x x' y : DedekindCompletion ℓᴾ) →
    x ≡ x' →
    (0≤x : x ≥0) →
    (0≤x' : x' ≥0) →
    (0≤y 0≤y' : y ≥0) →
    nnMul x y 0≤x 0≤y ≡ nnMul x' y 0≤x' 0≤y'
  nnMul-congL x x' y x≡x' 0≤x 0≤x' 0≤y 0≤y' =
    completionExt
      (nnMul x y 0≤x 0≤y)
      (nnMul x' y 0≤x' 0≤y')
      (lower-map x x' x≡x')
      (lower-map x' x (sym x≡x'))
      (upper-map x x' x≡x')
      (upper-map x' x (sym x≡x'))
    where
    lower-map :
      (z z' : DedekindCompletion ℓᴾ) →
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
      (z z' : DedekindCompletion ℓᴾ) →
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
    (x x' y y' : DedekindCompletion ℓᴾ) →
    x ≡ x' →
    y ≡ y' →
    (0≤x : x ≥0) →
    (0≤x' : x' ≥0) →
    (0≤y : y ≥0) →
    (0≤y' : y' ≥0) →
    nnMul x y 0≤x 0≤y ≡ nnMul x' y' 0≤x' 0≤y'
  nnMul-cong₂ x x' y y' x≡x' y≡y' 0≤x 0≤x' 0≤y 0≤y' =
    nnMul-congL x x' y x≡x' 0≤x 0≤x' 0≤y 0≤y ∙
    nnMul-congR x' y y' y≡y' 0≤x' 0≤x' 0≤y 0≤y'


module NonNegativeProperties
  (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  baseField : LinearlyOrderedField ℓ ℓ'
  baseField = 𝒜 .fst

  open CompletionBase baseField
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
  open Helpers (LinearlyOrderedCommRing→CommRing (baseField .fst))

  open ArithmeticBase 𝒜
  open Addition {ℓᴾ}
  open AdditiveGroup 𝒜 {ℓᴾ}
  open NonNegativeMultiplication 𝒜 {ℓᴾ}

  private
    K : Type ℓ
    K = Carrier

    dense :
      {p q : K} →
      p < q →
      ∥ Σ[ r ∈ K ] (p < r) × (r < q) ∥₁
    dense {p = p} {q = q} p<q =
      ∣ middle p q , middle>l p<q , middle<r p<q ∣₁

    negative-or-nonnegative :
      (q : K) →
      (q < 0r) ⊎ (0r ≤ q)
    negative-or-nonnegative q with trichotomy 0r q
    ... | LinearBase.lt 0<q = Sum.inr (<-≤-weaken 0<q)
    ... | LinearBase.eq 0≡q = Sum.inr (≤-refl 0≡q)
    ... | LinearBase.gt q<0 = Sum.inl q<0

    mul-nonpositive-right :
      {a b : K} →
      0r < a →
      b ≤ 0r →
      a · b ≤ 0r
    mul-nonpositive-right {a = a} {b = b} 0<a b≤0 =
      subst (a · b ≤_) (0RightAnnihilates a)
        (·-lPosPres≤ (<-≤-weaken 0<a) b≤0)

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
            (sym (left-diff+ ac m))
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
