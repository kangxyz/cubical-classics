{-

Basic constructive order lemmas for Cubical rationals

-}
{-# OPTIONS --safe #-}
module Constructive.Data.Rationals.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤOrder
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.NatPlusOne using (ℕ₊₁)
open import Cubical.Data.NatPlusOne.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁)
open import Cubical.Relation.Nullary using (Dec)
open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection
open import Constructive.Algebra.LinearlyOrderedCommRing
open import Constructive.Algebra.LinearlyOrderedCommRing.Instances.Rationals
  using (ℚLinearlyOrderedCommRing)
import Constructive.Algebra.LinearlyOrderedCommRing.Instances.Rationals.Archimedean as ℚArch
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Algebra.LinearlyOrderedField.Instances.Rationals
  using (ℚLinearlyOrderedField)


private
  module ℚLOR = LinearlyOrderedCommRingStr ℚLinearlyOrderedCommRing
  module ℚOF = LinearlyOrderedFieldStr ℚLinearlyOrderedField
  ℚCommRing = LinearlyOrderedCommRing→CommRing ℚLinearlyOrderedCommRing

  module RingSolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    mul-error-split :
      (lx ux ly uy : 𝓡 .fst) →
      ux · uy ≡ lx · ly + (((ux - lx) · uy) + (lx · (uy - ly)))
    mul-error-split _ _ _ _ = solve! 𝓡

0ℚ : ℚ
0ℚ = 0


1ℚ : ℚ
1ℚ = 1


mul-error-split :
  (lx ux ly uy : ℚ) →
  ux ℚ.· uy ≡
  lx ℚ.· ly ℚ.+ (((ux ℚ.- lx) ℚ.· uy) ℚ.+ (lx ℚ.· (uy ℚ.- ly)))
mul-error-split =
  RingSolverHelpers.mul-error-split ℚCommRing


1/2 : ℚ
1/2 = [ pos 1 / 2 ]


0<1 : 0 ℚOrder.< 1
0<1 = ℤOrder.zero-<sucPos


0<1/2 : 0 ℚOrder.< 1/2
0<1/2 = ℤOrder.zero-<sucPos


1/2+1/2≡1 : 1/2 ℚ.+ 1/2 ≡ 1
1/2+1/2≡1 = ℚ.eq/ _ _ refl


double-half : (q : ℚ) → (q ℚ.+ q) ℚ.· 1/2 ≡ q
double-half q =
  ℚ.·DistR+ q q 1/2 ∙
  sym (ℚ.·DistL+ q 1/2 1/2) ∙
  (λ i → q ℚ.· 1/2+1/2≡1 i) ∙
  ℚ.·IdR q


middle : ℚ → ℚ → ℚ
middle p q = (p ℚ.+ q) ℚ.· 1/2


middle>l : {p q : ℚ} → p ℚOrder.< q → p ℚOrder.< middle p q
middle>l {p = p} {q = q} p<q =
  subst (λ r → r ℚOrder.< middle p q) (double-half p)
    (ℚOrder.<-·o (p ℚ.+ p) (p ℚ.+ q) 1/2 0<1/2
      (ℚOrder.<-o+ p q p p<q))


middle<r : {p q : ℚ} → p ℚOrder.< q → middle p q ℚOrder.< q
middle<r {p = p} {q = q} p<q =
  subst (λ r → middle p q ℚOrder.< r) (double-half q)
    (ℚOrder.<-·o (p ℚ.+ q) (q ℚ.+ q) 1/2 0<1/2
      (ℚOrder.<-+o p q q p<q))


dense :
  {p q : ℚ} → p ℚOrder.< q →
  ∥ Σ[ r ∈ ℚ ] (p ℚOrder.< r) × (r ℚOrder.< q) ∥₁
dense {p = p} {q = q} p<q =
  ∣ middle p q
  , middle>l {p = p} {q = q} p<q
  , middle<r {p = p} {q = q} p<q
  ∣₁


-1ℚ : ℚ
-1ℚ = ℚ.- 1ℚ


-1<0 : -1ℚ ℚOrder.< 0
-1<0 = ℤOrder.negsuc<-zero {zero}


q<q+1 : (q : ℚ) → q ℚOrder.< q ℚ.+ 1
q<q+1 q =
  subst (λ r → r ℚOrder.< q ℚ.+ 1) (ℚ.+IdR q)
    (ℚOrder.<-o+ 0 1 q 0<1)


q-1<q : (q : ℚ) → q ℚ.- 1 ℚOrder.< q
q-1<q q =
  subst (λ r → q ℚ.- 1 ℚOrder.< r) (ℚ.+IdR q)
    (ℚOrder.<-o+ -1ℚ 0 q -1<0)


q<q+positive :
  (q ε : ℚ) →
  0 ℚOrder.< ε →
  q ℚOrder.< q ℚ.+ ε
q<q+positive q ε 0<ε =
  subst (λ r → r ℚOrder.< q ℚ.+ ε) (ℚ.+IdR q)
    (ℚOrder.<-o+ 0 ε q 0<ε)


q≤q+nonnegative :
  (q ε : ℚ) →
  0 ℚOrder.≤ ε →
  q ℚOrder.≤ q ℚ.+ ε
q≤q+nonnegative q ε 0≤ε =
  subst (λ r → r ℚOrder.≤ q ℚ.+ ε) (ℚ.+IdR q)
    (ℚOrder.≤Monotone+
      q q
      0ℚ ε
      (ℚOrder.isRefl≤ q)
      0≤ε)


positive-sum :
  {p q : ℚ} →
  0ℚ ℚOrder.< p →
  0ℚ ℚOrder.< q →
  0ℚ ℚOrder.< p ℚ.+ q
positive-sum {p = p} {q = q} 0<p 0<q =
  ℚOrder.isTrans< 0ℚ p (p ℚ.+ q)
    0<p
    (q<q+positive p q 0<q)


nonnegative-positive-sum :
  {p q : ℚ} →
  0ℚ ℚOrder.≤ p →
  0ℚ ℚOrder.< q →
  0ℚ ℚOrder.< p ℚ.+ q
nonnegative-positive-sum {p = p} {q = q} 0≤p 0<q =
  ℚOrder.isTrans≤<
    0ℚ
    p
    (p ℚ.+ q)
    0≤p
    (q<q+positive p q 0<q)


≤-refl : (q : ℚ) → q ℚOrder.≤ q
≤-refl q = ℚLOR.≤-refl {x = q} {y = q} refl


<→≤ : {p q : ℚ} → p ℚOrder.< q → p ℚOrder.≤ q
<→≤ {p = p} {q = q} = ℚLOR.<-≤-weaken {x = p} {y = q}


dec< : (p q : ℚ) → Dec (p ℚOrder.< q)
dec< =
  ℚLOR.dec<


≤-trans :
  {p q r : ℚ} →
  p ℚOrder.≤ q →
  q ℚOrder.≤ r →
  p ℚOrder.≤ r
≤-trans {p = p} {q = q} {r = r} =
  ℚLOR.≤-trans {x = p} {y = q} {z = r}


<≤-trans :
  {p q r : ℚ} →
  p ℚOrder.< q →
  q ℚOrder.≤ r →
  p ℚOrder.< r
<≤-trans {p = p} {q = q} {r = r} =
  ℚLOR.<≤-trans {x = p} {y = q} {z = r}


≤<-trans :
  {p q r : ℚ} →
  p ℚOrder.≤ q →
  q ℚOrder.< r →
  p ℚOrder.< r
≤<-trans {p = p} {q = q} {r = r} =
  ℚLOR.≤<-trans {x = p} {y = q} {z = r}


≤-total : (p q : ℚ) → (p ℚOrder.≤ q) ⊎ (q ℚOrder.≤ p)
≤-total = ℚLOR.≤-total


+-rPres≤ :
  {p q r : ℚ} →
  p ℚOrder.≤ q →
  p ℚ.+ r ℚOrder.≤ q ℚ.+ r
+-rPres≤ {p = p} {q = q} {r = r} p≤q =
  ℚOrder.≤Monotone+
    p q
    r r
    p≤q
    (≤-refl r)


add-nonpositive≤right :
  {p r : ℚ} →
  p ℚOrder.≤ 0ℚ →
  p ℚ.+ r ℚOrder.≤ r
add-nonpositive≤right {p = p} {r = r} p≤0 =
  subst (λ t → p ℚ.+ r ℚOrder.≤ t)
    (ℚ.+IdL r)
    (+-rPres≤ {p = p} {q = 0ℚ} {r = r} p≤0)


neg-nonpositive :
  {q : ℚ} →
  0ℚ ℚOrder.≤ q →
  ℚ.- q ℚOrder.≤ 0ℚ
neg-nonpositive {q = q} 0≤q =
  subst2
    ℚOrder._≤_
    (ℚ.+IdL (ℚ.- q))
    (ℚ.+InvR q)
    (ℚOrder.≤-+o 0ℚ q (ℚ.- q) 0≤q)


sub-nonnegative-right≤ :
  {p q : ℚ} →
  0ℚ ℚOrder.≤ q →
  p ℚ.- q ℚOrder.≤ p
sub-nonnegative-right≤ {p = p} {q = q} 0≤q =
  subst
    (λ t → t ℚOrder.≤ p)
    (ℚ.+Comm (ℚ.- q) p)
    (add-nonpositive≤right {p = ℚ.- q} {r = p} (neg-nonpositive {q = q} 0≤q))


negative-or-nonnegative : (q : ℚ) → (q ℚOrder.< 0ℚ) ⊎ (0ℚ ℚOrder.≤ q)
negative-or-nonnegative q with 0ℚ ℚOrder.≟ q
... | ℚOrder.lt 0<q = inr (<→≤ {p = 0ℚ} {q = q} 0<q)
... | ℚOrder.eq 0≡q = inr (ℚOrder.≡Weaken≤ 0ℚ q 0≡q)
... | ℚOrder.gt q<0 = inl q<0


nonnegative-right-of-< :
  {p q : ℚ} →
  0ℚ ℚOrder.≤ p →
  p ℚOrder.< q →
  0ℚ ℚOrder.< q
nonnegative-right-of-< {p = p} {q = q} =
  ≤<-trans {p = 0ℚ} {q = p} {r = q}


p+[q-p]≡q : (p q : ℚ) → p ℚ.+ (q ℚ.- p) ≡ q
p+[q-p]≡q p q =
  ℚ.+Assoc p q (ℚ.- p) ∙
  cong (λ r → r ℚ.+ (ℚ.- p)) (ℚ.+Comm p q) ∙
  sym (ℚ.+Assoc q p (ℚ.- p)) ∙
  cong (q ℚ.+_) (ℚ.+InvR p) ∙
  ℚ.+IdR q


diff≤right :
  {p q : ℚ} →
  0ℚ ℚOrder.≤ p →
  q ℚ.- p ℚOrder.≤ q
diff≤right {p = p} {q = q} 0≤p =
  subst (λ r → gap ℚOrder.≤ r)
    (p+[q-p]≡q p q)
    gap≤p+gap
  where
  gap : ℚ
  gap = q ℚ.- p

  gap≤p+gap : gap ℚOrder.≤ p ℚ.+ gap
  gap≤p+gap =
    subst (λ r → r ℚOrder.≤ p ℚ.+ gap)
      (ℚ.+IdL gap)
      (ℚOrder.≤Monotone+
        0ℚ p
        gap gap
        0≤p
        (≤-refl gap))


[p+q]-q≡p : (p q : ℚ) → (p ℚ.+ q) ℚ.- q ≡ p
[p+q]-q≡p p q =
  sym (ℚ.+Assoc p q (ℚ.- q)) ∙
  cong (p ℚ.+_) (ℚ.+InvR q) ∙
  ℚ.+IdR p


[p-q]+q≡p : (p q : ℚ) → (p ℚ.- q) ℚ.+ q ≡ p
[p-q]+q≡p p q =
  sym (ℚ.+Assoc p (ℚ.- q) q) ∙
  cong (p ℚ.+_) (ℚ.+InvL q) ∙
  ℚ.+IdR p


diff<→shift< :
  (p q r : ℚ) →
  q ℚ.- p ℚOrder.< r →
  q ℚOrder.< p ℚ.+ r
diff<→shift< p q r q-p<r =
  subst (λ t → t ℚOrder.< p ℚ.+ r)
    (p+[q-p]≡q p q)
    (ℚOrder.<-o+ (q ℚ.- p) r p q-p<r)


<+→diff< :
  (a b c : ℚ) →
  a ℚOrder.< b ℚ.+ c →
  a ℚ.- c ℚOrder.< b
<+→diff< a b c a<b+c =
  subst (λ r → a ℚ.- c ℚOrder.< r)
    ([p+q]-q≡p b c)
    (ℚOrder.<-+o a (b ℚ.+ c) (ℚ.- c) a<b+c)


diff<→right+< :
  (a b c : ℚ) →
  a ℚ.- c ℚOrder.< b →
  a ℚOrder.< b ℚ.+ c
diff<→right+< a b c a-c<b =
  subst (λ r → a ℚOrder.< r)
    (ℚ.+Comm c b)
    (diff<→shift< c a b a-c<b)


right+<→diff< :
  (a b c : ℚ) →
  a ℚ.+ b ℚOrder.< c →
  a ℚOrder.< c ℚ.- b
right+<→diff< a b c a+b<c =
  subst (λ r → r ℚOrder.< c ℚ.- b)
    ([p+q]-q≡p a b)
    (ℚOrder.<-+o (a ℚ.+ b) c (ℚ.- b) a+b<c)


diff-right<→+< :
  (a b c : ℚ) →
  a ℚOrder.< c ℚ.- b →
  a ℚ.+ b ℚOrder.< c
diff-right<→+< a b c a<c-b =
  subst (λ r → a ℚ.+ b ℚOrder.< r)
    ([p-q]+q≡p c b)
    (ℚOrder.<-+o a (c ℚ.- b) b a<c-b)


diff-positive :
  {p q : ℚ} →
  p ℚOrder.< q →
  0 ℚOrder.< q ℚ.- p
diff-positive {p = p} {q = q} p<q =
  subst (λ r → r ℚOrder.< q ℚ.- p)
    (ℚ.+InvR p)
    (ℚOrder.<-+o p q (ℚ.- p) p<q)


+-interchange :
  (a b c d : ℚ) →
  (a ℚ.+ c) ℚ.+ (b ℚ.+ d) ≡ (a ℚ.+ b) ℚ.+ (c ℚ.+ d)
+-interchange a b c d =
  ℚ.+Assoc (a ℚ.+ c) b d ∙
  cong (λ r → r ℚ.+ d) (sym (ℚ.+Assoc a c b)) ∙
  cong (λ r → (a ℚ.+ r) ℚ.+ d) (ℚ.+Comm c b) ∙
  cong (λ r → r ℚ.+ d) (ℚ.+Assoc a b c) ∙
  sym (ℚ.+Assoc (a ℚ.+ b) c d)


sum-close-upper< :
  (lx ly ux uy η p q : ℚ) →
  ux ℚOrder.< lx ℚ.+ η →
  uy ℚOrder.< ly ℚ.+ η →
  lx ℚ.+ ly ℚOrder.≤ p →
  η ℚ.+ η ≡ q ℚ.- p →
  ux ℚ.+ uy ℚOrder.< q
sum-close-upper< lx ly ux uy η p q ux<lx+η uy<ly+η lx+ly≤p η+η≡q-p =
  subst (λ r → ux ℚ.+ uy ℚOrder.< r)
    (p+[q-p]≡q p q)
    ux+uy<p+q-p
  where
  ux+uy<lx+η+ly+η :
    ux ℚ.+ uy ℚOrder.< (lx ℚ.+ η) ℚ.+ (ly ℚ.+ η)
  ux+uy<lx+η+ly+η =
    ℚOrder.<Monotone+
      ux (lx ℚ.+ η)
      uy (ly ℚ.+ η)
      ux<lx+η
      uy<ly+η

  ux+uy<lx+ly+η+η :
    ux ℚ.+ uy ℚOrder.< (lx ℚ.+ ly) ℚ.+ (η ℚ.+ η)
  ux+uy<lx+ly+η+η =
    subst (λ r → ux ℚ.+ uy ℚOrder.< r)
      (+-interchange lx ly η η)
      ux+uy<lx+η+ly+η

  lx+ly+η+η≤p+η+η :
    (lx ℚ.+ ly) ℚ.+ (η ℚ.+ η)
    ℚOrder.≤
    p ℚ.+ (η ℚ.+ η)
  lx+ly+η+η≤p+η+η =
    ℚOrder.≤Monotone+
      (lx ℚ.+ ly)
      p
      (η ℚ.+ η)
      (η ℚ.+ η)
      lx+ly≤p
      (ℚOrder.isRefl≤ (η ℚ.+ η))

  ux+uy<p+η+η :
    ux ℚ.+ uy ℚOrder.< p ℚ.+ (η ℚ.+ η)
  ux+uy<p+η+η =
    ℚOrder.isTrans<≤
      (ux ℚ.+ uy)
      ((lx ℚ.+ ly) ℚ.+ (η ℚ.+ η))
      (p ℚ.+ (η ℚ.+ η))
      ux+uy<lx+ly+η+η
      lx+ly+η+η≤p+η+η

  ux+uy<p+q-p :
    ux ℚ.+ uy ℚOrder.< p ℚ.+ (q ℚ.- p)
  ux+uy<p+q-p =
    subst (λ r → ux ℚ.+ uy ℚOrder.< p ℚ.+ r)
      η+η≡q-p
      ux+uy<p+η+η


negReverse< : {p q : ℚ} → p ℚOrder.< q → (ℚ.- q) ℚOrder.< (ℚ.- p)
negReverse< {p = p} {q = q} p<q =
  subst2 ℚOrder._<_
    (p ℚ.+ ((ℚ.- p) ℚ.+ (ℚ.- q)) ≡⟨ ℚ.+Assoc p (ℚ.- p) (ℚ.- q) ⟩
     (p ℚ.+ (ℚ.- p)) ℚ.+ (ℚ.- q) ≡⟨ cong (λ r → r ℚ.+ (ℚ.- q)) (ℚ.+InvR p) ⟩
     0 ℚ.+ (ℚ.- q) ≡⟨ ℚ.+IdL (ℚ.- q) ⟩
     ℚ.- q ∎)
    (q ℚ.+ ((ℚ.- p) ℚ.+ (ℚ.- q)) ≡⟨ cong (q ℚ.+_) (ℚ.+Comm (ℚ.- p) (ℚ.- q)) ⟩
     q ℚ.+ ((ℚ.- q) ℚ.+ (ℚ.- p)) ≡⟨ ℚ.+Assoc q (ℚ.- q) (ℚ.- p) ⟩
     (q ℚ.+ (ℚ.- q)) ℚ.+ (ℚ.- p) ≡⟨ cong (λ r → r ℚ.+ (ℚ.- p)) (ℚ.+InvR q) ⟩
     0 ℚ.+ (ℚ.- p) ≡⟨ ℚ.+IdL (ℚ.- p) ⟩
     ℚ.- p ∎)
    (ℚOrder.<-+o p q ((ℚ.- p) ℚ.+ (ℚ.- q)) p<q)


negReverse<-involutive :
  {p q : ℚ} → (ℚ.- q) ℚOrder.< (ℚ.- p) → p ℚOrder.< q
negReverse<-involutive {p = p} {q = q} -q<-p =
  subst2 ℚOrder._<_ (ℚ.-Invol p) (ℚ.-Invol q)
    (negReverse< {p = ℚ.- q} {q = ℚ.- p} -q<-p)


neg-zero : ℚ.- 0ℚ ≡ 0ℚ
neg-zero =
  sym (ℚ.+IdL (ℚ.- 0ℚ)) ∙
  ℚ.+InvR 0ℚ


neg-positive : {q : ℚ} → q ℚOrder.< 0ℚ → 0ℚ ℚOrder.< ℚ.- q
neg-positive {q = q} q<0 =
  subst (λ r → r ℚOrder.< ℚ.- q)
    neg-zero
    (negReverse< {p = q} {q = 0ℚ} q<0)


swap-sub< :
  (p q u : ℚ) →
  u ℚOrder.< p ℚ.- q →
  q ℚOrder.< p ℚ.- u
swap-sub< p q u u<p-q =
  right+<→diff< q u p
    (subst (λ r → r ℚOrder.< p)
      (ℚ.+Comm u q)
      (diff-right<→+< u q p u<p-q))


sum-left-close< :
  (p l u r : ℚ) →
  u ℚOrder.< l ℚ.+ (r ℚ.- p) →
  p ℚ.+ u ℚOrder.< r ℚ.+ l
sum-left-close< p l u r u<l+r-p =
  subst (λ v → p ℚ.+ u ℚOrder.< v)
    p+l+r-p≡r+l
    (ℚOrder.<-o+ u (l ℚ.+ (r ℚ.- p)) p u<l+r-p)
  where
  p+l+r-p≡r+l : p ℚ.+ (l ℚ.+ (r ℚ.- p)) ≡ r ℚ.+ l
  p+l+r-p≡r+l =
    ℚ.+Assoc p l (r ℚ.- p) ∙
    cong (λ v → v ℚ.+ (r ℚ.- p)) (ℚ.+Comm p l) ∙
    sym (ℚ.+Assoc l p (r ℚ.- p)) ∙
    cong (l ℚ.+_) (p+[q-p]≡q p r) ∙
    ℚ.+Comm l r
