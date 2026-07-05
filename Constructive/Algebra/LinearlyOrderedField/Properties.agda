{-

Properties of linearly ordered fields

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Algebra.LinearlyOrderedField.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Nullary
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Field as CubicalField
  using (Field→CommRing)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Algebra.LinearlyOrderedCommRing
import Constructive.Algebra.OrderedField.Base as OrderedFieldBase
open import Constructive.Algebra.LinearlyOrderedField.Base

private
  variable
    ℓ ℓ' ℓ'' : Level


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (p p⁻¹ q⁻¹ : 𝓡 .fst) → p · (p⁻¹ · q⁻¹) ≡ (p · p⁻¹) · q⁻¹
    helper1 _ _ _ = solve! 𝓡

    helper2 : (q p⁻¹ q⁻¹ : 𝓡 .fst) → q · (p⁻¹ · q⁻¹) ≡ (q · q⁻¹) · p⁻¹
    helper2 _ _ _ = solve! 𝓡

    helper3 : (y z : 𝓡 .fst) → y + (z - y) ≡ z
    helper3 _ _ = solve! 𝓡

    helper4 : (x y z : 𝓡 .fst) → x · (y · z) ≡ (y · x) · z
    helper4 _ _ _ = solve! 𝓡

    helper5 :
      (lx ux ly uy : 𝓡 .fst) →
      ux · uy ≡ lx · ly + (((ux - lx) · uy) + (lx · (uy - ly)))
    helper5 _ _ _ _ = solve! 𝓡

    helper6 :
      (U V gap : 𝓡 .fst) →
      U + ((V + gap) + 1r) ≡ ((U + V) + gap) + 1r
    helper6 _ _ _ = solve! 𝓡

    helper7 :
      (U V gap : 𝓡 .fst) →
      V + ((U + gap) + 1r) ≡ ((U + V) + gap) + 1r
    helper7 _ _ _ = solve! 𝓡

    helper8 :
      (U V gap : 𝓡 .fst) →
      (U + V) + (gap + 1r) ≡ ((U + V) + gap) + 1r
    helper8 _ _ _ = solve! 𝓡

    helper9 :
      (ε M M⁻¹ : 𝓡 .fst) →
      M⁻¹ · M ≡ 1r →
      (ε · M⁻¹) · M ≡ ε
    helper9 ε M M⁻¹ M⁻¹M≡1 =
      sym (·Assoc ε M⁻¹ M) ∙
      cong (ε ·_) M⁻¹M≡1 ∙
      ·IdR ε

    helper10 :
      (δ U V : 𝓡 .fst) →
      (δ · V) + (δ · U) ≡ δ · (U + V)
    helper10 _ _ _ = solve! 𝓡

    helper11 :
      (a b c : 𝓡 .fst) →
      a · (b + c) ≡ (a · b) + (a · c)
    helper11 _ _ _ = solve! 𝓡

    helper12 : (p q : 𝓡 .fst) → (p - q) + q ≡ p
    helper12 _ _ = solve! 𝓡

    helper13 :
      (lx ly η : 𝓡 .fst) →
      (lx + η) + (ly + η) ≡ (lx + ly) + (η + η)
    helper13 _ _ _ = solve! 𝓡

    helper14 :
      (p l r : 𝓡 .fst) →
      p + (l + (r - p)) ≡ r + l
    helper14 _ _ _ = solve! 𝓡


module LinearlyOrderedFieldStr (𝒦 : LinearlyOrderedField ℓ ℓ') where

  private
    𝒦ᶠ = LinearlyOrderedField→Field 𝒦

  open CubicalField.FieldStr (𝒦ᶠ .snd) public
  open RingTheory  (CommRing→Ring (Field→CommRing 𝒦ᶠ)) public
  open Units       (Field→CommRing 𝒦ᶠ) public
  open LinearlyOrderedCommRingStr (𝒦 .fst) public
  module OF = OrderedFieldBase.OrderedFieldStr (LinearlyOrderedField→OrderedField 𝒦)
  open OF public
    using ( inv ; ·-rInv ; ·-lInv ; inv-≢0 ; invIdem ; invUniq
          ; ·-≢0 ; ·-Inv
          ; 1/_ ; 1/n·n≡1 ; _/_ ; ·-/-rInv ; ·-/-lInv
          ; middle ; middle-sym ; 2·middle ; x/2+x/2≡x
          ; middle-l ; middle-r
          ; #→≢0 ; inv# ; ·-lInv# ; 0#1)

  private
    K = 𝒦 .fst .fst .fst

    variable
      p q x y z : K

  open Helpers (LinearlyOrderedCommRing→CommRing (𝒦 .fst))

  {-

    Inverse of positive element

  -}

  inv₊ : q > 0r → K
  inv₊ q>0 = OF.inv₊ q>0

  ·-rInv₊ : (q>0 : q > 0r) → q · inv₊ q>0 ≡ 1r
  ·-rInv₊ q>0 = OF.·-rInv₊ q>0

  ·-lInv₊ : (q>0 : q > 0r) → inv₊ q>0 · q ≡ 1r
  ·-lInv₊ q>0 = OF.·-lInv₊ q>0


  {-

    Division by non-zero natural numbers

  -}

  1/n>0 : (n : ℕ₊₁) →  1/ n > 0r
  1/n>0 (1+ n) = ·-lPosCancel>0 (ℕ→R-PosSuc>0 n) (subst (_> 0r) (sym (1/n·n≡1 (1+ n))) 1>0)


  {-

    Middle of an interval

  -}

  middle>l : p < q → middle p q > p
  middle>l {p = p} {q = q} p<q =
    Diff>0→> {x = middle p q} {y = p} (·-rPosCancel>0 {x = 2r} {y = middle p q - p} 2>0
      (subst (_> 0r) (sym (middle-l p q)) (>→Diff>0 {x = q} {y = p} p<q)))

  middle<r : p < q → q > middle p q
  middle<r {p = p} {q = q} p<q =
    Diff<0→< {x = middle p q} {y = q} (·-rPosCancel<0 {x = 2r} {y = middle p q - q} 2>0
      (subst (_< 0r) (sym (middle-r p q)) (<→Diff<0 {x = p} {y = q} p<q)))


  {-

    Order of multiplicative inverse

  -}

  p>0→p⁻¹>0 : (p>0 : p > 0r) → inv₊ p>0 > 0r
  p>0→p⁻¹>0 {p = p} p>0 = ·-rPosCancel>0 {x = p} {y = inv₊ p>0} p>0 p·p⁻¹>0
    where
    p·p⁻¹>0 : p · inv₊ p>0 > 0r
    p·p⁻¹>0 = subst (_> 0r) (sym (·-rInv₊ p>0)) 1>0

  p>q>0→p·q⁻¹>1 : (q>0 : q > 0r) → p > q → p · inv₊ q>0 > 1r
  p>q>0→p·q⁻¹>1 {q = q} {p = p} q>0 p>q =
    subst (p · inv (>-arefl {x = q} q>0) >_) (·-rInv (>-arefl {x = q} q>0))
      (·-rPosPres< {x = inv (>-arefl {x = q} q>0)} {y = q} {z = p} (p>0→p⁻¹>0 {p = q} q>0) p>q)

  inv-Reverse< : (p>0 : p > 0r)(q>0 : q > 0r) → p > q → inv₊ p>0 < inv₊ q>0
  inv-Reverse< {p = p} {q = q} p>0 q>0 p>q = q⁻¹>p⁻¹
    where
    p⁻¹ = inv₊ p>0
    q⁻¹ = inv₊ q>0
    p⁻¹·q⁻¹>0 : p⁻¹ · q⁻¹ > 0r
    p⁻¹·q⁻¹>0 = ·-Pres>0 {x = p⁻¹} {y = q⁻¹} (p>0→p⁻¹>0 {p = p} p>0) (p>0→p⁻¹>0 {p = q} q>0)
    p·p⁻¹·q⁻¹>q·q⁻¹·p⁻¹ : (p · p⁻¹) · q⁻¹ > (q · q⁻¹) · p⁻¹
    p·p⁻¹·q⁻¹>q·q⁻¹·p⁻¹ = transport (λ i → helper1 p p⁻¹ q⁻¹ i > helper2 q p⁻¹ q⁻¹ i)
      (·-rPosPres< {x = p⁻¹ · q⁻¹} {y = q} {z = p} p⁻¹·q⁻¹>0 p>q)
    1·q⁻¹>1·p⁻¹ : 1r · q⁻¹ > 1r · p⁻¹
    1·q⁻¹>1·p⁻¹ = transport (λ i → ·-rInv₊ p>0 i · q⁻¹ > ·-rInv₊ q>0 i · p⁻¹) p·p⁻¹·q⁻¹>q·q⁻¹·p⁻¹
    q⁻¹>p⁻¹ : q⁻¹ > p⁻¹
    q⁻¹>p⁻¹ = transport (λ i → ·IdL q⁻¹ i > ·IdL p⁻¹ i) 1·q⁻¹>1·p⁻¹

  inv₊Idem : (q>0 : q > 0r) → inv₊ (p>0→p⁻¹>0 q>0) ≡ q
  inv₊Idem {q = q} q>0 = sym (·IdL _)
    ∙ (λ i → ·-rInv₊ q>0 (~ i) · inv₊ (p>0→p⁻¹>0 q>0))
    ∙ sym (·Assoc _ _ _) ∙ (λ i →  q · ·-rInv₊ (p>0→p⁻¹>0 q>0) i) ∙ ·IdR _

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
  ... | lt 0<q = inr (<-≤-weaken 0<q)
  ... | eq 0≡q = inr (≤-refl 0≡q)
  ... | gt q<0 = inl q<0

  nonnegative-right-of-< :
    {p q : K} →
    0r ≤ p →
    p < q →
    0r < q
  nonnegative-right-of-< = ≤<-trans

  positive-sum-split :
    (r s : K) →
    0r < r + s →
    (0r < r) ⊎ (0r < s)
  positive-sum-split r s 0<r+s with trichotomy 0r r
  ... | lt 0<r = inl 0<r
  ... | eq 0≡r = inr 0<s
    where
    r+s≡s : r + s ≡ s
    r+s≡s =
      cong (_+ s) (sym 0≡r) ∙
      +IdL s

    0<s : 0r < s
    0<s =
      subst (0r <_) r+s≡s 0<r+s
  ... | gt r<0 with trichotomy 0r s
  ... | lt 0<s = inr 0<s
  ... | eq 0≡s =
    Empty.rec (<-asym 0<r+s r+s<0)
    where
    r+s≡r : r + s ≡ r
    r+s≡r =
      cong (r +_) (sym 0≡s) ∙
      +IdR r

    r+s<0 : r + s < 0r
    r+s<0 =
      subst (_< 0r) (sym r+s≡r) r<0
  ... | gt s<0 =
    Empty.rec (<-asym 0<r+s r+s<0)
    where
    r+s<0+0 : r + s < 0r + 0r
    r+s<0+0 =
      +-Pres< r<0 s<0

    r+s<0 : r + s < 0r
    r+s<0 =
      subst (r + s <_) (+IdR 0r) r+s<0+0

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
    helper9 ε M (inv₊ 0<M) (·-lInv₊ 0<M)

  p+[q-p]≡q : (p q : K) → p + (q - p) ≡ q
  p+[q-p]≡q = helper3

  [p-q]+q≡p : (p q : K) → (p - q) + q ≡ p
  [p-q]+q≡p = helper12

  mul-distrib-left :
    (a b c : K) →
    a · (b + c) ≡ (a · b) + (a · c)
  mul-distrib-left = helper11

  sum-left-close-path :
    (p l r : K) →
    p + (l + (r - p)) ≡ r + l
  sum-left-close-path = helper14

  sum-close-upper< :
    (lx ly ux uy η p q : K) →
    ux < lx + η →
    uy < ly + η →
    lx + ly ≤ p →
    η + η ≡ q - p →
    p < q →
    ux + uy < q
  sum-close-upper< lx ly ux uy η p q ux<lx+η uy<ly+η lx+ly≤p η+η≡q-p p<q =
    <≤-trans ux+uy<lx+ly+η+η lx+ly+η+η≤q
    where
    ux+uy<lx+η+ly+η : ux + uy < (lx + η) + (ly + η)
    ux+uy<lx+η+ly+η = +-Pres< ux<lx+η uy<ly+η

    ux+uy<lx+ly+η+η : ux + uy < (lx + ly) + (η + η)
    ux+uy<lx+ly+η+η =
      subst (ux + uy <_)
        (helper13 lx ly η)
        ux+uy<lx+η+ly+η

    lx+ly+η+η≤p+η+η : (lx + ly) + (η + η) ≤ p + (η + η)
    lx+ly+η+η≤p+η+η = +-rPres≤ lx+ly≤p

    p+η+η≡q : p + (η + η) ≡ q
    p+η+η≡q =
      cong (p +_) η+η≡q-p ∙
      p+[q-p]≡q p q

    lx+ly+η+η≤q : (lx + ly) + (η + η) ≤ q
    lx+ly+η+η≤q =
      ≤-trans lx+ly+η+η≤p+η+η (≤-refl p+η+η≡q)

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
    subst (U <_) (helper6 U V gap)
      (+-rPos→> (+-Pres>0 (+-Pres>0 0<V 0<gap) 1>0))

  mulErrorDenom>V :
    {gap U V : K} →
    0r < U →
    0r < gap →
    V < mulErrorDenom U V gap
  mulErrorDenom>V {gap = gap} {U = U} {V = V} 0<U 0<gap =
    subst (V <_) (helper7 U V gap)
      (+-rPos→> (+-Pres>0 (+-Pres>0 0<U 0<gap) 1>0))

  mulErrorDenom>U+V :
    {gap U V : K} →
    0r < gap →
    U + V < mulErrorDenom U V gap
  mulErrorDenom>U+V {gap = gap} {U = U} {V = V} 0<gap =
    subst (U + V <_) (helper8 U V gap)
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
      (sym (helper5 lx ux ly uy))
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
        (helper10 δ U V)
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

  mul-nonpositive-right :
    {a b : K} →
    0r < a →
    b ≤ 0r →
    a · b ≤ 0r
  mul-nonpositive-right {a = a} {b = b} 0<a b≤0 =
    subst (a · b ≤_) (0RightAnnihilates a)
      (·-lPosPres≤ (<-≤-weaken 0<a) b≤0)


  private
    ·inv-helper : (y>0 : y > 0r) → (x · y) · inv₊ y>0 ≡ x
    ·inv-helper {x = x} y>0 = sym (·Assoc _ _ _) ∙ (λ i → x · ·-rInv₊ y>0 i) ∙ ·IdR _

  ·-MoveLToR< : (y>0 : y > 0r) → x · y < z → x < z · inv₊ y>0
  ·-MoveLToR< {y = y} {x = x} {z = z} y>0 xy<z =
    subst (_< z · inv₊ y>0) (·inv-helper y>0) (·-rPosPres< (p>0→p⁻¹>0 y>0) xy<z)

  ·-MoveRToL< : (y>0 : y > 0r) → z < x · y → z · inv₊ y>0 < x
  ·-MoveRToL< {y = y} {z = z} {x = x} y>0 xy>z =
    subst (_> z · inv₊ y>0) (·inv-helper y>0) (·-rPosPres< (p>0→p⁻¹>0 y>0) xy>z)


  {-

    Decomposition and ordering

  -}

  <-+-Decompose : (x y z : K) → x + y < z → Σ[ s ∈ K ] Σ[ t ∈ K ] (x < s) × (y < t) × (z ≡ s + t)
  <-+-Decompose x y z x+y<z = mid , z - mid , mid>x , z-mid>y , sym (helper3 mid z)
    where
    mid = middle x (z - y)
    x<z-y : x < z - y
    x<z-y = +-MoveLToR< x+y<z
    y+mid<z : y + mid < z
    y+mid<z = subst (y + mid <_) (helper3 y z) (+-lPres< (middle<r x<z-y))
    mid>x = middle>l x<z-y
    z-mid>y : y < z - mid
    z-mid>y = +-MoveLToR< y+mid<z


  private
    ·inv-helper' : (x>0 : x > 0r) → x · (y · inv₊ x>0) ≡ y
    ·inv-helper' {x = x} y>0 = helper4 _ _ _ ∙ ·inv-helper y>0

  <-·-Decompose : (x y z : K) → x > 0r → y > 0r → x · y < z
    → Σ[ s ∈ K ] Σ[ t ∈ K ] (x < s) × (y < t) × (z ≡ s · t)
  <-·-Decompose x y z x>0 y>0 xy<z =
    mid , z · inv₊ mid>0 , mid>x , z·mid⁻¹>y , sym (·inv-helper' mid>0)
    where
    mid = middle x (z · inv₊ y>0)
    x<zy⁻¹ : x < z · inv₊ y>0
    x<zy⁻¹ = ·-MoveLToR< y>0 xy<z
    mid>0 : mid > 0r
    mid>0 = <-trans x>0 (middle>l x<zy⁻¹)
    y·mid<z : y · mid < z
    y·mid<z = subst (y · mid <_) (·inv-helper' y>0) (·-lPosPres< y>0 (middle<r x<zy⁻¹))
    mid>x = middle>l x<zy⁻¹
    z·mid⁻¹>y : y < z · inv₊ mid>0
    z·mid⁻¹>y = ·-MoveLToR< mid>0 y·mid<z


  {-

    Pick out a smaller-than-both positive element

  -}

  min2 : x > 0r → y > 0r → Σ[ z ∈ K ] (z > 0r) × (z < x) × (z < y)
  min2 {x = x} {y = y} x>0 y>0 = case-split (trichotomy x y)
    where
    case-split : Trichotomy (𝒦 .fst .fst) x y → Σ[ z ∈ K ] (z > 0r) × (z < x) × (z < y)
    case-split (lt x<y) = middle 0r x , middle>l x>0 , middle<r x>0 , <-trans (middle<r x>0) x<y
    case-split (gt x>y) = middle 0r y , middle>l y>0 , <-trans (middle<r y>0) x>y , middle<r y>0
    case-split (eq x≡y) =
      middle 0r x , middle>l x>0 , middle<r x>0 , subst (middle 0r x <_) x≡y (middle<r x>0)


  abstract
    mul-by-<1 :
      {a b : K} →
      0r < a →
      b < 1r →
      a · b < a
    mul-by-<1 {a = a} {b = b} 0<a b<1 =
      subst (a · b <_) (·IdR a) (·-lPosPres< 0<a b<1)

    mul-by->1 :
      {a b : K} →
      0r < a →
      1r < b →
      a < a · b
    mul-by->1 {a = a} {b = b} 0<a 1<b =
      subst (_< a · b) (·IdR a) (·-lPosPres< 0<a 1<b)

    unit-lower-factor :
      (q a : K) →
      0r ≤ q →
      q < a →
      0r < a →
      Σ[ b ∈ K ]
        (0r < b) ×
        (b < 1r) ×
        (q < a · b)
    unit-lower-factor q a 0≤q q<a 0<a =
      b , 0<b , b<1 , q<ab
      where
      qa : K
      qa = q · inv₊ 0<a

      qa<1 : qa < 1r
      qa<1 =
        subst (qa <_) (·-rInv₊ 0<a)
          (·-rPosPres< (p>0→p⁻¹>0 0<a) q<a)

      b : K
      b = middle qa 1r

      qa<b : qa < b
      qa<b = middle>l qa<1

      b<1 : b < 1r
      b<1 = middle<r qa<1

      0≤qa : 0r ≤ qa
      0≤qa =
        ·-Pres≥0
          0≤q
          (<-≤-weaken (p>0→p⁻¹>0 0<a))

      0<b : 0r < b
      0<b =
        ≤<-trans 0≤qa qa<b

      aqa<ab : a · qa < a · b
      aqa<ab =
        ·-lPosPres< 0<a qa<b

      q<ab : q < a · b
      q<ab =
        subst (λ v → v < a · b)
          (·inv-helper' {x = a} {y = q} 0<a)
          aqa<ab

    unit-upper-factor :
      (r q : K) →
      0r < r →
      r < q →
      Σ[ b ∈ K ]
        (1r < b) ×
        (0r < b) ×
        (r · b < q)
    unit-upper-factor r q 0<r r<q =
      b , 1<b , 0<b , rb<q
      where
      t : K
      t = q · inv₊ 0<r

      1<t : 1r < t
      1<t =
        subst (_< t) (·-rInv₊ 0<r)
          (·-rPosPres< (p>0→p⁻¹>0 0<r) r<q)

      b : K
      b = middle 1r t

      1<b : 1r < b
      1<b = middle>l 1<t

      b<t : b < t
      b<t = middle<r 1<t

      0<b : 0r < b
      0<b =
        <-trans 1>0 1<b

      rb<rt : r · b < r · t
      rb<rt =
        ·-lPosPres< 0<r b<t

      rb<q : r · b < q
      rb<q =
        subst (λ v → r · b < v)
          (·inv-helper' {x = r} {y = q} 0<r)
          rb<rt

{-

  The Archimedean Property of Linearly Ordered Fields

-}

open import Constructive.Preliminary.Nat
open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean

module _ (𝒦 : LinearlyOrderedField ℓ ℓ')(archimedean : isArchimedean (𝒦 .fst .fst)) where

  open LinearlyOrderedFieldStr 𝒦

  private
    K = 𝒦 .fst .fst .fst

  -- An inverse version of the Archimedean property,
  -- which says you can make a non-zero element arbitrarily small by dividing a natural number.

  isArchimedeanInv : Type (ℓ-max ℓ ℓ')
  isArchimedeanInv = (x ε : K) → x > 0r → ε > 0r → Σ[ n ∈ ℕ₊₁ ] ε / n < x

  isArchimedean→isArchimedeanInv : isArchimedeanInv
  isArchimedean→isArchimedeanInv x ε x>0 ε>0 = let (n , nx>ε) = archimedean ε x x>0 in helper n nx>ε
    where
    helper : (n : ℕ) → n ⋆ x > ε → Σ[ n ∈ ℕ₊₁ ] ε / n < x
    helper zero nx>ε = Empty.rec (<-asym ε>0 (subst (_> ε) (0⋆q≡0 _) nx>ε))
    helper (suc n) nx>ε = 1+ n ,
      subst (ε / (1+ n) <_) (sym (·Assoc _ _ _)
      ∙ ·-/-lInv x (1+ n)) (·-rPosPres< (1/n>0 (1+ n)) nx>ε)


  -- A useful lemma to lift mere existence to explicit existence.

  module _
    {P : (x : K) → Type ℓ''}
    (isPropP : (x : K) → isProp (P x))
    (decP : (x : K) → Dec (P x))
    (<-close : (x y : K) → x > 0r → x < y → P y → P x)
    (∃ε : ∥ Σ[ ε ∈ K ] (ε > 0r) × P ε ∥₁) where

    private
      P' : ℕ → Type ℓ''
      P' n = P (1r / (1+ n))

      1r/n>0 : (n : ℕ₊₁) → 1r / n > 0r
      1r/n>0 n = ·-Pres>0 1>0 (1/n>0 n)

      ∃P'n : ∥ Σ[ n ∈ ℕ ] P' n ∥₁
      ∃P'n = do
        (ε , ε>0 , pε) ← ∃ε
        let (1+ n , 1/n<ε) =
              isArchimedean→isArchimedeanInv ε 1r ε>0 1>0
        return (n , <-close _ _ (1r/n>0 _) 1/n<ε pε)

    findExplicit : Σ[ ε ∈ K ] (ε > 0r) × P ε
    findExplicit = let (n , p) = find (λ _ → decP _) ∃P'n in 1r / (1+ n) , (1r/n>0 _) , p
