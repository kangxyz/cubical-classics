{-

Constructive order lemmas for Cubical's quotient rationals

Shared support for ordered algebra and constructive real constructions.

-}
{-# OPTIONS --safe #-}
module Constructive.Data.Rationals where

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


mul-positive :
  {a b : ℚ} →
  0ℚ ℚOrder.< a →
  0ℚ ℚOrder.< b →
  0ℚ ℚOrder.< a ℚ.· b
mul-positive {a = a} {b = b} 0<a 0<b =
  subst (λ v → v ℚOrder.< a ℚ.· b)
    (ℚ.·AnnihilL b)
    (ℚOrder.<-·o 0ℚ a b 0<b 0<a)

mul-nonnegative :
  {a b : ℚ} →
  0ℚ ℚOrder.≤ a →
  0ℚ ℚOrder.≤ b →
  0ℚ ℚOrder.≤ a ℚ.· b
mul-nonnegative {a = a} {b = b} 0≤a 0≤b =
  subst (λ v → v ℚOrder.≤ a ℚ.· b)
    (ℚ.·AnnihilL b)
    (ℚOrder.≤-·o 0ℚ a b 0≤b 0≤a)


mul-nonpositive-right :
  {a b : ℚ} →
  0ℚ ℚOrder.< a →
  b ℚOrder.≤ 0ℚ →
  a ℚ.· b ℚOrder.≤ 0ℚ
mul-nonpositive-right {a = a} {b = b} 0<a b≤0 =
  subst2 ℚOrder._≤_
    (ℚ.·Comm b a)
    (ℚ.·AnnihilL a)
    (ℚOrder.≤-·o b 0ℚ a (<→≤ {p = 0ℚ} {q = a} 0<a) b≤0)


mul-nonpositive-left :
  {a b : ℚ} →
  a ℚOrder.≤ 0ℚ →
  0ℚ ℚOrder.< b →
  a ℚ.· b ℚOrder.≤ 0ℚ
mul-nonpositive-left {a = a} {b = b} a≤0 0<b =
  subst (λ v → v ℚOrder.≤ 0ℚ)
    (ℚ.·Comm b a)
    (mul-nonpositive-right {a = b} {b = a} 0<b a≤0)


mul-distrib-left :
  (a b c : ℚ) →
  a ℚ.· (b ℚ.+ c) ≡ (a ℚ.· b) ℚ.+ (a ℚ.· c)
mul-distrib-left = ℚ.·DistL+


mul-mono-positive-< :
  {a b c d : ℚ} →
  a ℚOrder.< c →
  b ℚOrder.< d →
  0ℚ ℚOrder.< b →
  0ℚ ℚOrder.< c →
  a ℚ.· b ℚOrder.< c ℚ.· d
mul-mono-positive-< {a = a} {b = b} {c = c} {d = d}
  a<c b<d 0<b 0<c =
  ℚOrder.isTrans< (a ℚ.· b) (c ℚ.· b) (c ℚ.· d)
    a*b<c*b
    c*b<c*d
  where
  a*b<c*b : a ℚ.· b ℚOrder.< c ℚ.· b
  a*b<c*b = ℚOrder.<-·o a c b 0<b a<c

  c*b<c*d : c ℚ.· b ℚOrder.< c ℚ.· d
  c*b<c*d =
    subst2 ℚOrder._<_
      (ℚ.·Comm b c)
      (ℚ.·Comm d c)
      (ℚOrder.<-·o b d c 0<c b<d)


mul-mono-positive-<≤ :
  {a b c d : ℚ} →
  0ℚ ℚOrder.< a →
  0ℚ ℚOrder.< c →
  a ℚOrder.< b →
  c ℚOrder.≤ d →
  a ℚ.· c ℚOrder.< b ℚ.· d
mul-mono-positive-<≤ {a = a} {b = b} {c = c} {d = d} 0<a 0<c a<b c≤d =
  ℚOrder.isTrans<≤ (a ℚ.· c) (b ℚ.· c) (b ℚ.· d)
    a*c<b*c
    b*c≤b*d
  where
  0<b : 0ℚ ℚOrder.< b
  0<b = ℚOrder.isTrans< 0ℚ a b 0<a a<b

  0≤b : 0ℚ ℚOrder.≤ b
  0≤b = <→≤ {p = 0ℚ} {q = b} 0<b

  a*c<b*c : a ℚ.· c ℚOrder.< b ℚ.· c
  a*c<b*c = ℚOrder.<-·o a b c 0<c a<b

  b*c≤b*d : b ℚ.· c ℚOrder.≤ b ℚ.· d
  b*c≤b*d =
    subst2 ℚOrder._≤_
      (ℚ.·Comm c b)
      (ℚ.·Comm d b)
      (ℚOrder.≤-·o c d b 0≤b c≤d)


mul-close-left-nonpositive-upper< :
  {q gap δ V lx ux uy : ℚ} →
  lx ℚOrder.≤ 0ℚ →
  ux ℚOrder.< lx ℚ.+ δ →
  0ℚ ℚOrder.< ux →
  0ℚ ℚOrder.< uy →
  uy ℚOrder.≤ V →
  δ ℚ.· V ℚOrder.< gap →
  gap ℚOrder.≤ q →
  ux ℚ.· uy ℚOrder.< q
mul-close-left-nonpositive-upper<
  {q = q} {gap = gap} {δ = δ} {V = V} {lx = lx} {ux = ux} {uy = uy}
  lx≤0 ux<lx+δ 0<ux 0<uy uy≤V δV<gap gap≤q =
  <≤-trans {p = ux ℚ.· uy} {q = gap} {r = q}
    (ℚOrder.isTrans< (ux ℚ.· uy) (δ ℚ.· V) gap uxuy<δV δV<gap)
    gap≤q
  where
  lx+δ≤δ : lx ℚ.+ δ ℚOrder.≤ δ
  lx+δ≤δ =
    add-nonpositive≤right {p = lx} {r = δ} lx≤0

  ux<δ : ux ℚOrder.< δ
  ux<δ =
    <≤-trans {p = ux} {q = lx ℚ.+ δ} {r = δ}
      ux<lx+δ
      lx+δ≤δ

  uxuy<δV : ux ℚ.· uy ℚOrder.< δ ℚ.· V
  uxuy<δV =
    mul-mono-positive-<≤
      {a = ux} {b = δ} {c = uy} {d = V}
      0<ux 0<uy ux<δ uy≤V


mul-close-right-nonpositive-upper< :
  {q gap δ U ly ux uy : ℚ} →
  ly ℚOrder.≤ 0ℚ →
  uy ℚOrder.< ly ℚ.+ δ →
  0ℚ ℚOrder.< ux →
  0ℚ ℚOrder.< uy →
  ux ℚOrder.≤ U →
  δ ℚ.· U ℚOrder.< gap →
  gap ℚOrder.≤ q →
  ux ℚ.· uy ℚOrder.< q
mul-close-right-nonpositive-upper<
  {q = q} {gap = gap} {δ = δ} {U = U} {ly = ly} {ux = ux} {uy = uy}
  ly≤0 uy<ly+δ 0<ux 0<uy ux≤U δU<gap gap≤q =
  <≤-trans {p = ux ℚ.· uy} {q = gap} {r = q}
    (ℚOrder.isTrans< (ux ℚ.· uy) (δ ℚ.· U) gap uxuy<δU δU<gap)
    gap≤q
  where
  ly+δ≤δ : ly ℚ.+ δ ℚOrder.≤ δ
  ly+δ≤δ =
    add-nonpositive≤right {p = ly} {r = δ} ly≤0

  uy<δ : uy ℚOrder.< δ
  uy<δ =
    <≤-trans {p = uy} {q = ly ℚ.+ δ} {r = δ}
      uy<ly+δ
      ly+δ≤δ

  uyux<δU : uy ℚ.· ux ℚOrder.< δ ℚ.· U
  uyux<δU =
    mul-mono-positive-<≤
      {a = uy} {b = δ} {c = ux} {d = U}
      0<uy 0<ux uy<δ ux≤U

  uxuy<δU : ux ℚ.· uy ℚOrder.< δ ℚ.· U
  uxuy<δU =
    subst (λ r → r ℚOrder.< δ ℚ.· U)
      (ℚ.·Comm uy ux)
      uyux<δU


mul-close-positive-upper< :
  {p q gap δ U V lx ux ly uy : ℚ} →
  lx ℚOrder.< ux →
  ly ℚOrder.< uy →
  0ℚ ℚOrder.< lx →
  0ℚ ℚOrder.< ly →
  ux ℚOrder.< lx ℚ.+ δ →
  uy ℚOrder.< ly ℚ.+ δ →
  ux ℚOrder.≤ U →
  uy ℚOrder.≤ V →
  lx ℚ.· ly ℚOrder.≤ p →
  δ ℚ.· (U ℚ.+ V) ℚOrder.< gap →
  p ℚ.+ gap ≡ q →
  ux ℚ.· uy ℚOrder.< q
mul-close-positive-upper<
  {p = p} {q = q} {gap = gap} {δ = δ} {U = U} {V = V}
  {lx = lx} {ux = ux} {ly = ly} {uy = uy}
  lx<ux ly<uy 0<lx 0<ly ux<lx+δ uy<ly+δ ux≤U uy≤V lxly≤p δUV<gap p+gap≡q =
  subst (λ r → r ℚOrder.< q)
    (sym (mul-error-split lx ux ly uy))
    rhs<q
  where
  err₁ : ℚ
  err₁ = (ux ℚ.- lx) ℚ.· uy

  err₂ : ℚ
  err₂ = lx ℚ.· (uy ℚ.- ly)

  0<uy : 0ℚ ℚOrder.< uy
  0<uy = ℚOrder.isTrans< 0ℚ ly uy 0<ly ly<uy

  ux<δ+lx : ux ℚOrder.< δ ℚ.+ lx
  ux<δ+lx =
    subst (λ r → ux ℚOrder.< r)
      (ℚ.+Comm lx δ)
      ux<lx+δ

  ux-lx<δ : ux ℚ.- lx ℚOrder.< δ
  ux-lx<δ = <+→diff< ux δ lx ux<δ+lx

  0<ux-lx : 0ℚ ℚOrder.< ux ℚ.- lx
  0<ux-lx = diff-positive {p = lx} {q = ux} lx<ux

  err₁<δV : err₁ ℚOrder.< δ ℚ.· V
  err₁<δV =
    mul-mono-positive-<≤
      {a = ux ℚ.- lx} {b = δ} {c = uy} {d = V}
      0<ux-lx 0<uy ux-lx<δ uy≤V

  uy<δ+ly : uy ℚOrder.< δ ℚ.+ ly
  uy<δ+ly =
    subst (λ r → uy ℚOrder.< r)
      (ℚ.+Comm ly δ)
      uy<ly+δ

  uy-ly<δ : uy ℚ.- ly ℚOrder.< δ
  uy-ly<δ = <+→diff< uy δ ly uy<δ+ly

  0<uy-ly : 0ℚ ℚOrder.< uy ℚ.- ly
  0<uy-ly = diff-positive {p = ly} {q = uy} ly<uy

  lx≤ux : lx ℚOrder.≤ ux
  lx≤ux = <→≤ {p = lx} {q = ux} lx<ux

  lx≤U : lx ℚOrder.≤ U
  lx≤U = ≤-trans {p = lx} {q = ux} {r = U} lx≤ux ux≤U

  uy-ly*lx<δU : (uy ℚ.- ly) ℚ.· lx ℚOrder.< δ ℚ.· U
  uy-ly*lx<δU =
    mul-mono-positive-<≤
      {a = uy ℚ.- ly} {b = δ} {c = lx} {d = U}
      0<uy-ly 0<lx uy-ly<δ lx≤U

  err₂<δU : err₂ ℚOrder.< δ ℚ.· U
  err₂<δU =
    subst (λ r → r ℚOrder.< δ ℚ.· U)
      (ℚ.·Comm (uy ℚ.- ly) lx)
      uy-ly*lx<δU

  err₁+err₂<δV+δU :
    err₁ ℚ.+ err₂ ℚOrder.< (δ ℚ.· V) ℚ.+ (δ ℚ.· U)
  err₁+err₂<δV+δU =
    ℚOrder.<Monotone+
      err₁ (δ ℚ.· V)
      err₂ (δ ℚ.· U)
      err₁<δV
      err₂<δU

  δV+δU≡δUV : (δ ℚ.· V) ℚ.+ (δ ℚ.· U) ≡ δ ℚ.· (U ℚ.+ V)
  δV+δU≡δUV =
    sym (ℚ.·DistL+ δ V U) ∙
    cong (δ ℚ.·_) (ℚ.+Comm V U)

  err₁+err₂<δUV : err₁ ℚ.+ err₂ ℚOrder.< δ ℚ.· (U ℚ.+ V)
  err₁+err₂<δUV =
    subst (λ r → err₁ ℚ.+ err₂ ℚOrder.< r)
      δV+δU≡δUV
      err₁+err₂<δV+δU

  err₁+err₂<gap : err₁ ℚ.+ err₂ ℚOrder.< gap
  err₁+err₂<gap =
    ℚOrder.isTrans< (err₁ ℚ.+ err₂) (δ ℚ.· (U ℚ.+ V)) gap
      err₁+err₂<δUV
      δUV<gap

  base+err≤p+err :
    (lx ℚ.· ly) ℚ.+ (err₁ ℚ.+ err₂)
      ℚOrder.≤
    p ℚ.+ (err₁ ℚ.+ err₂)
  base+err≤p+err =
    +-rPres≤ {p = lx ℚ.· ly} {q = p} {r = err₁ ℚ.+ err₂} lxly≤p

  p+err<p+gap : p ℚ.+ (err₁ ℚ.+ err₂) ℚOrder.< p ℚ.+ gap
  p+err<p+gap =
    ℚOrder.<-o+ (err₁ ℚ.+ err₂) gap p err₁+err₂<gap

  rhs<p+gap :
    (lx ℚ.· ly) ℚ.+ (err₁ ℚ.+ err₂) ℚOrder.< p ℚ.+ gap
  rhs<p+gap =
    ℚOrder.isTrans≤< ((lx ℚ.· ly) ℚ.+ (err₁ ℚ.+ err₂))
      (p ℚ.+ (err₁ ℚ.+ err₂))
      (p ℚ.+ gap)
      base+err≤p+err
      p+err<p+gap

  rhs<q :
    (lx ℚ.· ly) ℚ.+ (err₁ ℚ.+ err₂) ℚOrder.< q
  rhs<q =
    subst (λ r → (lx ℚ.· ly) ℚ.+ (err₁ ℚ.+ err₂) ℚOrder.< r)
      p+gap≡q
      rhs<p+gap


mul-left-positive-< :
  {a b c : ℚ} →
  0ℚ ℚOrder.< a →
  b ℚOrder.< c →
  a ℚ.· b ℚOrder.< a ℚ.· c
mul-left-positive-< {a = a} {b = b} {c = c} 0<a b<c =
  subst2 ℚOrder._<_
    (ℚ.·Comm b a)
    (ℚ.·Comm c a)
    (ℚOrder.<-·o b c a 0<a b<c)


mul-right-positive-< :
  {a b c : ℚ} →
  0ℚ ℚOrder.< a →
  b ℚOrder.< c →
  b ℚ.· a ℚOrder.< c ℚ.· a
mul-right-positive-< {a = a} {b = b} {c = c} 0<a b<c =
  ℚOrder.<-·o b c a 0<a b<c


mul-left-nonnegative-≤ :
  {a b c : ℚ} →
  0ℚ ℚOrder.≤ a →
  b ℚOrder.≤ c →
  a ℚ.· b ℚOrder.≤ a ℚ.· c
mul-left-nonnegative-≤ {a = a} {b = b} {c = c} 0≤a b≤c =
  subst2 ℚOrder._≤_
    (ℚ.·Comm b a)
    (ℚ.·Comm c a)
    (ℚOrder.≤-·o b c a 0≤a b≤c)


posInv : (q : ℚ) → 0ℚ ℚOrder.< q → ℚ
posInv q 0<q = ℚOF.inv₊ {q = q} 0<q


posInv-positive :
  {q : ℚ} →
  (0<q : 0ℚ ℚOrder.< q) →
  0ℚ ℚOrder.< posInv q 0<q
posInv-positive {q = q} 0<q =
  ℚOF.p>0→p⁻¹>0 {p = q} 0<q


posInv-right :
  (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  q ℚ.· posInv q 0<q ≡ 1ℚ
posInv-right q 0<q =
  ℚOF.·-rInv₊ {q = q} 0<q


posInv-left :
  (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  posInv q 0<q ℚ.· q ≡ 1ℚ
posInv-left q 0<q =
  ℚOF.·-lInv₊ {q = q} 0<q


mul-right-cancel-positive-≤ :
  {p q c : ℚ} →
  0ℚ ℚOrder.< c →
  p ℚ.· c ℚOrder.≤ q ℚ.· c →
  p ℚOrder.≤ q
mul-right-cancel-positive-≤ {p = p} {q = q} {c = c} 0<c pc≤qc =
  subst2 ℚOrder._≤_
    p-path
    q-path
    scaled≤
  where
  c⁻¹ : ℚ
  c⁻¹ =
    posInv c 0<c

  0≤c⁻¹ : 0ℚ ℚOrder.≤ c⁻¹
  0≤c⁻¹ =
    <→≤
      {p = 0ℚ}
      {q = c⁻¹}
      (posInv-positive {q = c} 0<c)

  scaled≤ : (p ℚ.· c) ℚ.· c⁻¹ ℚOrder.≤ (q ℚ.· c) ℚ.· c⁻¹
  scaled≤ =
    ℚOrder.≤-·o
      (p ℚ.· c)
      (q ℚ.· c)
      c⁻¹
      0≤c⁻¹
      pc≤qc

  p-path : (p ℚ.· c) ℚ.· c⁻¹ ≡ p
  p-path =
    sym (ℚ.·Assoc p c c⁻¹) ∙
    cong (p ℚ.·_) (posInv-right c 0<c) ∙
    ℚ.·IdR p

  q-path : (q ℚ.· c) ℚ.· c⁻¹ ≡ q
  q-path =
    sym (ℚ.·Assoc q c c⁻¹) ∙
    cong (q ℚ.·_) (posInv-right c 0<c) ∙
    ℚ.·IdR q


posInv-reverse< :
  {p q : ℚ} →
  (0<p : 0ℚ ℚOrder.< p) →
  (0<q : 0ℚ ℚOrder.< q) →
  p ℚOrder.< q →
  posInv q 0<q ℚOrder.< posInv p 0<p
posInv-reverse< {p = p} {q = q} 0<p 0<q p<q =
  ℚOF.inv-Reverse< {p = q} {q = p} 0<q 0<p p<q


posInv-involutive :
  (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  posInv (posInv q 0<q) (posInv-positive {q = q} 0<q) ≡ q
posInv-involutive q 0<q =
  ℚOF.inv₊Idem {q = q} 0<q

mul-posInv-cancelL :
  (a q : ℚ) →
  (0<a : 0ℚ ℚOrder.< a) →
  a ℚ.· (q ℚ.· posInv a 0<a) ≡ q
mul-posInv-cancelL a q 0<a =
  ℚ.·Assoc a q (posInv a 0<a) ∙
  cong (λ r → r ℚ.· posInv a 0<a) (ℚ.·Comm a q) ∙
  sym (ℚ.·Assoc q a (posInv a 0<a)) ∙
  cong (q ℚ.·_) (posInv-right a 0<a) ∙
  ℚ.·IdR q

div-positive-denom-<1 :
  {q a : ℚ} →
  q ℚOrder.< a →
  (0<a : 0ℚ ℚOrder.< a) →
  q ℚ.· posInv a 0<a ℚOrder.< 1ℚ
div-positive-denom-<1 {q = q} {a = a} q<a 0<a =
  subst (λ r → q ℚ.· posInv a 0<a ℚOrder.< r)
    (posInv-right a 0<a)
    (ℚOrder.<-·o q a (posInv a 0<a)
      (posInv-positive {q = a} 0<a)
      q<a)

1<div-positive-denom :
  {r q : ℚ} →
  r ℚOrder.< q →
  (0<r : 0ℚ ℚOrder.< r) →
  1ℚ ℚOrder.< q ℚ.· posInv r 0<r
1<div-positive-denom {r = r} {q = q} r<q 0<r =
  subst (λ lhs → lhs ℚOrder.< q ℚ.· posInv r 0<r)
    (posInv-right r 0<r)
    (ℚOrder.<-·o r q (posInv r 0<r)
      (posInv-positive {q = r} 0<r)
      r<q)

abstract
  mul-by-<1 :
    {a b : ℚ} →
    0ℚ ℚOrder.< a →
    b ℚOrder.< 1ℚ →
    a ℚ.· b ℚOrder.< a
  mul-by-<1 {a = a} {b = b} 0<a b<1 =
    subst2 ℚOrder._<_
      (ℚ.·Comm b a)
      (ℚ.·IdL a)
      (ℚOrder.<-·o b 1ℚ a 0<a b<1)

  mul-by->1 :
    {a b : ℚ} →
    0ℚ ℚOrder.< a →
    1ℚ ℚOrder.< b →
    a ℚOrder.< a ℚ.· b
  mul-by->1 {a = a} {b = b} 0<a 1<b =
    subst2 ℚOrder._<_
      (ℚ.·IdL a)
      (ℚ.·Comm b a)
      (ℚOrder.<-·o 1ℚ b a 0<a 1<b)

  unit-lower-factor :
    (q a : ℚ) →
    0ℚ ℚOrder.≤ q →
    q ℚOrder.< a →
    0ℚ ℚOrder.< a →
    Σ[ b ∈ ℚ ]
      (0ℚ ℚOrder.< b) ×
      (b ℚOrder.< 1ℚ) ×
      (q ℚOrder.< a ℚ.· b)
  unit-lower-factor q a 0≤q q<a 0<a =
    b , 0<b , b<1 , q<ab
    where
    qa : ℚ
    qa = q ℚ.· posInv a 0<a

    qa<1 : qa ℚOrder.< 1ℚ
    qa<1 = div-positive-denom-<1 {q = q} {a = a} q<a 0<a

    b : ℚ
    b = middle qa 1ℚ

    qa<b : qa ℚOrder.< b
    qa<b = middle>l {p = qa} {q = 1ℚ} qa<1

    b<1 : b ℚOrder.< 1ℚ
    b<1 = middle<r {p = qa} {q = 1ℚ} qa<1

    0≤qa : 0ℚ ℚOrder.≤ qa
    0≤qa =
      mul-nonnegative
        {a = q}
        {b = posInv a 0<a}
        0≤q
        (<→≤ {p = 0ℚ} {q = posInv a 0<a}
          (posInv-positive {q = a} 0<a))

    0<b : 0ℚ ℚOrder.< b
    0<b =
      ≤<-trans {p = 0ℚ} {q = qa} {r = b} 0≤qa qa<b

    aqa<ab : a ℚ.· qa ℚOrder.< a ℚ.· b
    aqa<ab =
      mul-left-positive-< {a = a} {b = qa} {c = b} 0<a qa<b

    q<ab : q ℚOrder.< a ℚ.· b
    q<ab =
      subst (λ v → v ℚOrder.< a ℚ.· b)
        (mul-posInv-cancelL a q 0<a)
        aqa<ab

  unit-upper-factor :
    (r q : ℚ) →
    0ℚ ℚOrder.< r →
    r ℚOrder.< q →
    Σ[ b ∈ ℚ ]
      (1ℚ ℚOrder.< b) ×
      (0ℚ ℚOrder.< b) ×
      (r ℚ.· b ℚOrder.< q)
  unit-upper-factor r q 0<r r<q =
    b , 1<b , 0<b , rb<q
    where
    t : ℚ
    t = q ℚ.· posInv r 0<r

    1<t : 1ℚ ℚOrder.< t
    1<t = 1<div-positive-denom {r = r} {q = q} r<q 0<r

    b : ℚ
    b = middle 1ℚ t

    1<b : 1ℚ ℚOrder.< b
    1<b = middle>l {p = 1ℚ} {q = t} 1<t

    b<t : b ℚOrder.< t
    b<t = middle<r {p = 1ℚ} {q = t} 1<t

    0<b : 0ℚ ℚOrder.< b
    0<b =
      ℚOrder.isTrans< 0ℚ 1ℚ b 0<1 1<b

    rb<rt : r ℚ.· b ℚOrder.< r ℚ.· t
    rb<rt =
      mul-left-positive-< {a = r} {b = b} {c = t} 0<r b<t

    rb<q : r ℚ.· b ℚOrder.< q
    rb<q =
      subst (λ v → r ℚ.· b ℚOrder.< v)
        (mul-posInv-cancelL r q 0<r)
        rb<rt


scaleByPositive : (ε M : ℚ) → 0ℚ ℚOrder.< M → ℚ
scaleByPositive ε M 0<M = ε ℚ.· posInv M 0<M


scaleByPositive-positive :
  {ε M : ℚ} →
  0ℚ ℚOrder.< ε →
  (0<M : 0ℚ ℚOrder.< M) →
  0ℚ ℚOrder.< scaleByPositive ε M 0<M
scaleByPositive-positive {ε = ε} {M = M} 0<ε 0<M =
  mul-positive {a = ε} {b = posInv M 0<M}
    0<ε
    (posInv-positive {q = M} 0<M)


scaleByPositive-cancelR :
  (ε M : ℚ) →
  (0<M : 0ℚ ℚOrder.< M) →
  scaleByPositive ε M 0<M ℚ.· M ≡ ε
scaleByPositive-cancelR ε M 0<M =
  sym (ℚ.·Assoc ε (posInv M 0<M) M) ∙
  cong (ε ℚ.·_) (posInv-left M 0<M) ∙
  ℚ.·IdR ε


scaleByPositive-cancelL :
  (ε M : ℚ) →
  (0<M : 0ℚ ℚOrder.< M) →
  M ℚ.· scaleByPositive ε M 0<M ≡ ε
scaleByPositive-cancelL ε M 0<M =
  ℚ.·Comm M (scaleByPositive ε M 0<M) ∙
  scaleByPositive-cancelR ε M 0<M


mulErrorDenom : ℚ → ℚ → ℚ → ℚ
mulErrorDenom U V gap = ((U ℚ.+ V) ℚ.+ gap) ℚ.+ 1ℚ


mulErrorDenom-positive :
  {U V gap : ℚ} →
  0ℚ ℚOrder.< U →
  0ℚ ℚOrder.< V →
  0ℚ ℚOrder.< gap →
  0ℚ ℚOrder.< mulErrorDenom U V gap
mulErrorDenom-positive {U = U} {V = V} {gap = gap} 0<U 0<V 0<gap =
  positive-sum
    {p = (U ℚ.+ V) ℚ.+ gap}
    {q = 1ℚ}
    (positive-sum
      {p = U ℚ.+ V}
      {q = gap}
      (positive-sum {p = U} {q = V} 0<U 0<V)
      0<gap)
    0<1


mulErrorScale :
  (gap U V : ℚ) →
  0ℚ ℚOrder.< U →
  0ℚ ℚOrder.< V →
  0ℚ ℚOrder.< gap →
  ℚ
mulErrorScale gap U V 0<U 0<V 0<gap =
  scaleByPositive gap
    (mulErrorDenom U V gap)
    (mulErrorDenom-positive {U = U} {V = V} {gap = gap} 0<U 0<V 0<gap)


mulErrorScale-positive :
  {gap U V : ℚ}
  (0<U : 0ℚ ℚOrder.< U)
  (0<V : 0ℚ ℚOrder.< V)
  (0<gap : 0ℚ ℚOrder.< gap) →
  0ℚ ℚOrder.< mulErrorScale gap U V 0<U 0<V 0<gap
mulErrorScale-positive {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap =
  scaleByPositive-positive
    {ε = gap}
    {M = mulErrorDenom U V gap}
    0<gap
    (mulErrorDenom-positive {U = U} {V = V} {gap = gap} 0<U 0<V 0<gap)


private
  denom>U-path : (U V gap : ℚ) →
    U ℚ.+ ((V ℚ.+ gap) ℚ.+ 1ℚ) ≡ mulErrorDenom U V gap
  denom>U-path U V gap =
    ℚ.+Assoc U (V ℚ.+ gap) 1ℚ ∙
    cong (λ r → r ℚ.+ 1ℚ) (ℚ.+Assoc U V gap)

  denom>V-path : (U V gap : ℚ) →
    V ℚ.+ ((U ℚ.+ gap) ℚ.+ 1ℚ) ≡ mulErrorDenom U V gap
  denom>V-path U V gap =
    ℚ.+Assoc V (U ℚ.+ gap) 1ℚ ∙
    cong (λ r → r ℚ.+ 1ℚ)
      (ℚ.+Assoc V U gap ∙
       cong (λ r → r ℚ.+ gap) (ℚ.+Comm V U))

  denom>U+V-path : (U V gap : ℚ) →
    (U ℚ.+ V) ℚ.+ (gap ℚ.+ 1ℚ) ≡ mulErrorDenom U V gap
  denom>U+V-path U V gap =
    ℚ.+Assoc (U ℚ.+ V) gap 1ℚ


mulErrorDenom>U :
  {gap U V : ℚ} →
  0ℚ ℚOrder.< V →
  0ℚ ℚOrder.< gap →
  U ℚOrder.< mulErrorDenom U V gap
mulErrorDenom>U {gap = gap} {U = U} {V = V} 0<V 0<gap =
  subst (λ r → U ℚOrder.< r)
    (denom>U-path U V gap)
    (q<q+positive U ((V ℚ.+ gap) ℚ.+ 1ℚ)
      (positive-sum
        {p = V ℚ.+ gap}
        {q = 1ℚ}
        (positive-sum {p = V} {q = gap} 0<V 0<gap)
        0<1))


mulErrorDenom>V :
  {gap U V : ℚ} →
  0ℚ ℚOrder.< U →
  0ℚ ℚOrder.< gap →
  V ℚOrder.< mulErrorDenom U V gap
mulErrorDenom>V {gap = gap} {U = U} {V = V} 0<U 0<gap =
  subst (λ r → V ℚOrder.< r)
    (denom>V-path U V gap)
    (q<q+positive V ((U ℚ.+ gap) ℚ.+ 1ℚ)
      (positive-sum
        {p = U ℚ.+ gap}
        {q = 1ℚ}
        (positive-sum {p = U} {q = gap} 0<U 0<gap)
        0<1))


mulErrorDenom>U+V :
  {gap U V : ℚ} →
  0ℚ ℚOrder.< gap →
  U ℚ.+ V ℚOrder.< mulErrorDenom U V gap
mulErrorDenom>U+V {gap = gap} {U = U} {V = V} 0<gap =
  subst (λ r → U ℚ.+ V ℚOrder.< r)
    (denom>U+V-path U V gap)
    (q<q+positive (U ℚ.+ V) (gap ℚ.+ 1ℚ)
      (positive-sum {p = gap} {q = 1ℚ} 0<gap 0<1))


mulErrorScale-times-U<gap :
  {gap U V : ℚ} →
  (0<U : 0ℚ ℚOrder.< U) →
  (0<V : 0ℚ ℚOrder.< V) →
  (0<gap : 0ℚ ℚOrder.< gap) →
  mulErrorScale gap U V 0<U 0<V 0<gap ℚ.· U ℚOrder.< gap
mulErrorScale-times-U<gap {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap =
  subst (λ r → δ ℚ.· U ℚOrder.< r)
    (scaleByPositive-cancelR gap D 0<D)
    δU<δD
  where
  D : ℚ
  D = mulErrorDenom U V gap

  0<D : 0ℚ ℚOrder.< D
  0<D = mulErrorDenom-positive {U = U} {V = V} {gap = gap} 0<U 0<V 0<gap

  δ : ℚ
  δ = mulErrorScale gap U V 0<U 0<V 0<gap

  0<δ : 0ℚ ℚOrder.< δ
  0<δ = mulErrorScale-positive {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap

  U<D : U ℚOrder.< D
  U<D = mulErrorDenom>U {gap = gap} {U = U} {V = V} 0<V 0<gap

  δU<δD : δ ℚ.· U ℚOrder.< δ ℚ.· D
  δU<δD = mul-left-positive-< {a = δ} {b = U} {c = D} 0<δ U<D


mulErrorScale-times-V<gap :
  {gap U V : ℚ} →
  (0<U : 0ℚ ℚOrder.< U) →
  (0<V : 0ℚ ℚOrder.< V) →
  (0<gap : 0ℚ ℚOrder.< gap) →
  mulErrorScale gap U V 0<U 0<V 0<gap ℚ.· V ℚOrder.< gap
mulErrorScale-times-V<gap {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap =
  subst (λ r → δ ℚ.· V ℚOrder.< r)
    (scaleByPositive-cancelR gap D 0<D)
    δV<δD
  where
  D : ℚ
  D = mulErrorDenom U V gap

  0<D : 0ℚ ℚOrder.< D
  0<D = mulErrorDenom-positive {U = U} {V = V} {gap = gap} 0<U 0<V 0<gap

  δ : ℚ
  δ = mulErrorScale gap U V 0<U 0<V 0<gap

  0<δ : 0ℚ ℚOrder.< δ
  0<δ = mulErrorScale-positive {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap

  V<D : V ℚOrder.< D
  V<D = mulErrorDenom>V {gap = gap} {U = U} {V = V} 0<U 0<gap

  δV<δD : δ ℚ.· V ℚOrder.< δ ℚ.· D
  δV<δD = mul-left-positive-< {a = δ} {b = V} {c = D} 0<δ V<D


mulErrorScale-times-sum<gap :
  {gap U V : ℚ} →
  (0<U : 0ℚ ℚOrder.< U) →
  (0<V : 0ℚ ℚOrder.< V) →
  (0<gap : 0ℚ ℚOrder.< gap) →
  mulErrorScale gap U V 0<U 0<V 0<gap ℚ.· (U ℚ.+ V) ℚOrder.< gap
mulErrorScale-times-sum<gap {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap =
  subst (λ r → δ ℚ.· (U ℚ.+ V) ℚOrder.< r)
    (scaleByPositive-cancelR gap D 0<D)
    δUV<δD
  where
  D : ℚ
  D = mulErrorDenom U V gap

  0<D : 0ℚ ℚOrder.< D
  0<D = mulErrorDenom-positive {U = U} {V = V} {gap = gap} 0<U 0<V 0<gap

  δ : ℚ
  δ = mulErrorScale gap U V 0<U 0<V 0<gap

  0<δ : 0ℚ ℚOrder.< δ
  0<δ = mulErrorScale-positive {gap = gap} {U = U} {V = V} 0<U 0<V 0<gap

  U+V<D : U ℚ.+ V ℚOrder.< D
  U+V<D = mulErrorDenom>U+V {gap = gap} {U = U} {V = V} 0<gap

  δUV<δD : δ ℚ.· (U ℚ.+ V) ℚOrder.< δ ℚ.· D
  δUV<δD =
    mul-left-positive-< {a = δ} {b = U ℚ.+ V} {c = D} 0<δ U+V<D


min≤r : (p q : ℚ) → ℚ.min p q ℚOrder.≤ q
min≤r p q =
  subst (λ r → r ℚOrder.≤ q)
    (ℚ.minComm q p)
    (ℚOrder.min≤ q p)


≤max-r : (p q : ℚ) → q ℚOrder.≤ ℚ.max p q
≤max-r p q =
  subst (λ r → q ℚOrder.≤ r)
    (ℚ.maxComm q p)
    (ℚOrder.≤max q p)


<min :
  {q r s : ℚ} →
  q ℚOrder.< r →
  q ℚOrder.< s →
  q ℚOrder.< ℚ.min r s
<min {q = q} {r = r} {s = s} q<r q<s with r ℚOrder.≟ s
... | ℚOrder.lt r<s =
  subst (λ t → q ℚOrder.< t)
    (sym (ℚOrder.≤→min r s (ℚOrder.<Weaken≤ r s r<s)))
    q<r
... | ℚOrder.eq r≡s =
  subst (λ t → q ℚOrder.< t)
    (sym (ℚOrder.≤→min r s (ℚOrder.≡Weaken≤ r s r≡s)))
    q<r
... | ℚOrder.gt s<r =
  subst (λ t → q ℚOrder.< t)
    (sym
      (ℚ.min r s ≡⟨ ℚ.minComm r s ⟩
       ℚ.min s r ≡⟨ ℚOrder.≤→min s r (ℚOrder.<Weaken≤ s r s<r) ⟩
       s ∎))
    q<s


max< :
  {r s q : ℚ} →
  r ℚOrder.< q →
  s ℚOrder.< q →
  ℚ.max r s ℚOrder.< q
max< {r = r} {s = s} {q = q} r<q s<q with r ℚOrder.≟ s
... | ℚOrder.lt r<s =
  subst (λ t → t ℚOrder.< q)
    (sym (ℚOrder.≤→max r s (ℚOrder.<Weaken≤ r s r<s)))
    s<q
... | ℚOrder.eq r≡s =
  subst (λ t → t ℚOrder.< q)
    (sym (ℚOrder.≤→max r s (ℚOrder.≡Weaken≤ r s r≡s)))
    s<q
... | ℚOrder.gt s<r =
  subst (λ t → t ℚOrder.< q)
    (sym
      (ℚ.max r s ≡⟨ ℚ.maxComm r s ⟩
       ℚ.max s r ≡⟨ ℚOrder.≤→max s r (ℚOrder.<Weaken≤ s r s<r) ⟩
       r ∎))
    r<q


natMul : ℕ → ℚ → ℚ
natMul = ℚLOR._⋆_


archimedean :
  (q ε : ℚ) →
  0 ℚOrder.< ε →
  Σ[ n ∈ ℕ ] q ℚOrder.< natMul n ε
archimedean = ℚArch.isArchimedeanℚ


unitFraction : ℕ → ℚ
unitFraction n =
  ℚOF._/_ 1ℚ (1+ n)


unitFraction-positive :
  (n : ℕ) →
  0 ℚOrder.< unitFraction n
unitFraction-positive n =
  ℚOF.·-Pres>0
    {x = 1ℚ}
    {y = ℚOF.1/ (1+ n)}
    0<1
    (ℚOF.1/n>0 (1+ n))


divideBySuc : ℚ → ℕ → ℚ
divideBySuc q n =
  ℚOF._/_ q (1+ n)


divideBySuc-positive :
  {q : ℚ} →
  0ℚ ℚOrder.< q →
  (n : ℕ) →
  0ℚ ℚOrder.< divideBySuc q n
divideBySuc-positive {q = q} 0<q n =
  mul-positive
    {a = q}
    {b = ℚOF.1/ (1+ n)}
    0<q
    (ℚOF.1/n>0 (1+ n))


divideBySuc-as-unitFraction :
  (q : ℚ) →
  (n : ℕ) →
  divideBySuc q n ≡ q ℚ.· unitFraction n
divideBySuc-as-unitFraction q n =
  cong (q ℚ.·_) (sym (ℚ.·IdL (ℚOF.1/ (1+ n))))


natMul-divideBySuc :
  (q : ℚ) →
  (n : ℕ) →
  natMul (suc n) (divideBySuc q n) ≡ q
natMul-divideBySuc q n =
  ℚOF.·-/-lInv q (1+ n)


abstract
  archimedean-unit-fraction :
    (ε : ℚ) →
    0 ℚOrder.< ε →
    Σ[ n ∈ ℕ ] unitFraction n ℚOrder.< ε
  archimedean-unit-fraction ε 0<ε with
      isArchimedean→isArchimedeanInv
        ℚLinearlyOrderedField
        ℚArch.isArchimedeanℚ
        ε
        1ℚ
        0<ε
        0<1
  ... | 1+ n , unit<ε =
    n , unit<ε


natMul-zero : (ε : ℚ) → natMul zero ε ≡ 0
natMul-zero = ℚLOR.0⋆q≡0


natMul-suc : (n : ℕ) (ε : ℚ) → natMul (suc n) ε ≡ natMul n ε ℚ.+ ε
natMul-suc = ℚLOR.sucn⋆q≡n⋆q+q


natMul-one : (ε : ℚ) → natMul (suc zero) ε ≡ ε
natMul-one ε =
  natMul-suc zero ε ∙
  cong (λ r → r ℚ.+ ε) (natMul-zero ε) ∙
  ℚ.+IdL ε


natMul-step< :
  (n : ℕ) {ε : ℚ} →
  0 ℚOrder.< ε →
  natMul n ε ℚOrder.< natMul (suc n) ε
natMul-step< n {ε = ε} 0<ε =
  subst (λ r → natMul n ε ℚOrder.< r)
    (sym (natMul-suc n ε))
    (q<q+positive (natMul n ε) ε 0<ε)


natMul-step≤ :
  (n : ℕ) {ε : ℚ} →
  0 ℚOrder.< ε →
  natMul n ε ℚOrder.≤ natMul (suc n) ε
natMul-step≤ n {ε = ε} 0<ε =
  ℚOrder.<Weaken≤
    (natMul n ε)
    (natMul (suc n) ε)
    (natMul-step< n 0<ε)


shift-bound-suc :
  (p ε : ℚ) (n : ℕ) →
  p ℚ.+ natMul (suc (suc n)) ε ≡
  (p ℚ.+ ε) ℚ.+ natMul (suc n) ε
shift-bound-suc p ε n =
  cong (p ℚ.+_) (natMul-suc (suc n) ε) ∙
  cong (p ℚ.+_) (ℚ.+Comm (natMul (suc n) ε) ε) ∙
  ℚ.+Assoc p ε (natMul (suc n) ε)


natMul-suc-positive :
  (n : ℕ) {ε : ℚ} →
  0 ℚOrder.< ε →
  0 ℚOrder.< natMul (suc n) ε
natMul-suc-positive n 0<ε = ℚLOR.sucn⋆q>0 n _ 0<ε


natMul-nonnegative :
  (n : ℕ) {ε : ℚ} →
  0 ℚOrder.< ε →
  0 ℚOrder.≤ natMul n ε
natMul-nonnegative n 0<ε = ℚLOR.n⋆q≥0 n _ 0<ε


natMul-mono-≤ :
  (n m : ℕ) {ε : ℚ} →
  0 ℚOrder.< ε →
  NatOrder._≤_ n m →
  natMul n ε ℚOrder.≤ natMul m ε
natMul-mono-≤ zero m {ε = ε} 0<ε _ =
  subst
    (λ q → q ℚOrder.≤ natMul m ε)
    (sym (natMul-zero ε))
    (natMul-nonnegative m 0<ε)
natMul-mono-≤ (suc n) zero 0<ε sn≤0 =
  Empty.rec (NatOrder.¬-<-zero sn≤0)
natMul-mono-≤ (suc n) (suc m) {ε = ε} 0<ε sn≤sm =
  subst2
    ℚOrder._≤_
    (sym (natMul-suc n ε))
    (sym (natMul-suc m ε))
    (ℚOrder.≤Monotone+
      (natMul n ε)
      (natMul m ε)
      ε ε
      (natMul-mono-≤ n m 0<ε (NatOrder.pred-≤-pred sn≤sm))
      (≤-refl ε))


natMul-factor-mono-≤ :
  (n : ℕ) →
  {ε δ : ℚ} →
  ε ℚOrder.≤ δ →
  natMul n ε ℚOrder.≤ natMul n δ
natMul-factor-mono-≤ zero {ε = ε} {δ = δ} ε≤δ =
  subst2
    ℚOrder._≤_
    (sym (natMul-zero ε))
    (sym (natMul-zero δ))
    (≤-refl 0ℚ)
natMul-factor-mono-≤ (suc n) {ε = ε} {δ = δ} ε≤δ =
  subst2
    ℚOrder._≤_
    (sym (natMul-suc n ε))
    (sym (natMul-suc n δ))
    (ℚOrder.≤Monotone+
      (natMul n ε)
      (natMul n δ)
      ε δ
      (natMul-factor-mono-≤ n ε≤δ)
      ε≤δ)


natMul-mul-left :
  (n : ℕ) →
  (a b : ℚ) →
  natMul n (a ℚ.· b) ≡ a ℚ.· natMul n b
natMul-mul-left zero a b =
  natMul-zero (a ℚ.· b) ∙
  sym (ℚ.·AnnihilR a) ∙
  cong (a ℚ.·_) (sym (natMul-zero b))
natMul-mul-left (suc n) a b =
  natMul-suc n (a ℚ.· b) ∙
  cong (λ q → q ℚ.+ (a ℚ.· b)) (natMul-mul-left n a b) ∙
  sym (ℚ.·DistL+ a (natMul n b) b) ∙
  cong (a ℚ.·_) (sym (natMul-suc n b))


positive-half :
  {ε : ℚ} →
  0 ℚOrder.< ε →
  0 ℚOrder.< ε ℚ.· 1/2
positive-half {ε = ε} 0<ε =
  subst (λ q → q ℚOrder.< ε ℚ.· 1/2)
    (ℚ.·AnnihilL 1/2)
    (ℚOrder.<-·o 0 ε 1/2 0<1/2 0<ε)


half+half : (ε : ℚ) → (ε ℚ.· 1/2) ℚ.+ (ε ℚ.· 1/2) ≡ ε
half+half ε =
  sym (ℚ.·DistL+ ε 1/2 1/2) ∙
  (λ i → ε ℚ.· 1/2+1/2≡1 i) ∙
  ℚ.·IdR ε


half<whole :
  {ε : ℚ} →
  0 ℚOrder.< ε →
  ε ℚ.· 1/2 ℚOrder.< ε
half<whole {ε = ε} 0<ε =
  subst (λ r → ε ℚ.· 1/2 ℚOrder.< r)
    (half+half ε)
    (q<q+positive (ε ℚ.· 1/2) (ε ℚ.· 1/2) (positive-half {ε = ε} 0<ε))


grid : ℚ → ℚ → ℕ → ℚ
grid a δ n = a ℚ.+ natMul n δ


grid-zero : (a δ : ℚ) → grid a δ zero ≡ a
grid-zero a δ =
  cong (a ℚ.+_) (natMul-zero δ) ∙
  ℚ.+IdR a


grid-suc :
  (a δ : ℚ) (n : ℕ) →
  grid a δ (suc n) ≡ grid a δ n ℚ.+ δ
grid-suc a δ n =
  cong (a ℚ.+_) (natMul-suc n δ) ∙
  ℚ.+Assoc a (natMul n δ) δ


grid-step< :
  {a δ : ℚ} (n : ℕ) →
  0 ℚOrder.< δ →
  grid a δ n ℚOrder.< grid a δ (suc n)
grid-step< {a = a} {δ = δ} n 0<δ =
  subst (λ r → grid a δ n ℚOrder.< r)
    (sym (grid-suc a δ n))
    (q<q+positive (grid a δ n) δ 0<δ)


grid-two-step :
  (a δ : ℚ) (n : ℕ) →
  grid a δ (suc (suc n)) ≡ grid a δ n ℚ.+ (δ ℚ.+ δ)
grid-two-step a δ n =
  grid-suc a δ (suc n) ∙
  cong (λ r → r ℚ.+ δ) (grid-suc a δ n) ∙
  sym (ℚ.+Assoc (grid a δ n) δ δ)


grid-two-half :
  (a ε : ℚ) (n : ℕ) →
  grid a (ε ℚ.· 1/2) (suc (suc n)) ≡ grid a (ε ℚ.· 1/2) n ℚ.+ ε
grid-two-half a ε n =
  grid-two-step a (ε ℚ.· 1/2) n ∙
  cong (grid a (ε ℚ.· 1/2) n ℚ.+_) (half+half ε)
