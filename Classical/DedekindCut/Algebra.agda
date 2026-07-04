{-

Algebraic Operations on Dedekind Cuts

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.DedekindCut.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

open import Classical.Axioms
open import Classical.Foundations.Powerset

open import Constructive.Algebra.StrictlyOrderedCommRing
open import Constructive.Algebra.StrictlyOrderedCommRing.Archimedes
open import Constructive.Algebra.StrictlyOrderedField
open import Classical.DedekindCut.Base
open import Classical.DedekindCut.Archimedes

private
  variable
    ℓ ℓ' : Level

private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (q r : 𝓡 .fst) → q ≡ r + (q - r)
    helper1 _ _ = solve! 𝓡

    helper2 : (q r : 𝓡 .fst) → q ≡ (q + r) - r
    helper2 _ _ = solve! 𝓡

    helper3 : (p q r : 𝓡 .fst) → q · (p · r) ≡ p · (q · r)
    helper3 _ _ _ = solve! 𝓡

    helper4 : (q r : 𝓡 .fst) → r + (r · (q - 1r)) ≡ r · q
    helper4 _ _ = solve! 𝓡


module Algebra ⦃ 🤖 : Oracle ⦄
  (𝒦 : OrderedField ℓ ℓ')(archimedesK : isArchimedean (𝒦 . fst))
  where

  private
    K = 𝒦 .fst .fst .fst


  open OrderedFieldStr 𝒦
  open Basics      𝒦
  open Archimedes  𝒦 archimedesK
  open DedekindCut

  open Helpers (StrictlyOrderedCommRing→CommRing (𝒦 .fst))


  {-

    Addition

  -}

  +𝕂Comm : (a b : 𝕂) → a +𝕂 b ≡ b +𝕂 a
  +𝕂Comm a b = ≤𝕂-asym (lift (upper⊆ b a)) (lift (upper⊆ a b))
    where
    upper⊆ : (a b : 𝕂){q : K} → q ∈ (a +𝕂 b) .upper → q ∈ (b +𝕂 a) .upper
    upper⊆ a b {q = q} q∈upper = Inhab→∈ (+upper b a) do
      (s , t , s∈upper , t∈upper , q≡s+t) ← ∈→Inhab (+upper a b) q∈upper
      return (t , s , t∈upper , s∈upper , q≡s+t ∙ +Comm s t)

  +𝕂Assoc : (a b c : 𝕂) → a +𝕂 (b +𝕂 c) ≡ (a +𝕂 b) +𝕂 c
  +𝕂Assoc a b c = ≤𝕂-asym (lift upper⊇) (lift upper⊆)
    where
    upper⊆ : {q : K} → q ∈ (a +𝕂 (b +𝕂 c)) .upper → q ∈ ((a +𝕂 b) +𝕂 c) .upper
    upper⊆ {q = q} q∈upper = Inhab→∈ (+upper (a +𝕂 b) c) do
      (s , t , s∈upper , t∈upper , q≡s+t) ← ∈→Inhab (+upper a (b +𝕂 c)) q∈upper
      (r , w , r∈upper , w∈upper , t≡r+w) ← ∈→Inhab (+upper b c) t∈upper
      return (s + r , w ,
        Inhab→∈ (+upper a b) ∣ s , r , s∈upper , r∈upper , refl ∣₁ ,
        w∈upper , q≡s+t ∙ (λ i → s + t≡r+w i) ∙ +Assoc s r w)

    upper⊇ : {q : K} → q ∈ ((a +𝕂 b) +𝕂 c) .upper → q ∈ (a +𝕂 (b +𝕂 c)) .upper
    upper⊇ {q = q} q∈upper = Inhab→∈ (+upper a (b +𝕂 c)) do
      (s , t , s∈upper , t∈upper , q≡s+t) ← ∈→Inhab (+upper (a +𝕂 b) c) q∈upper
      (r , w , r∈upper , w∈upper , s≡r+w) ← ∈→Inhab (+upper a b) s∈upper
      return (r , w + t ,
        r∈upper , Inhab→∈ (+upper b c) ∣ w , t , w∈upper , t∈upper , refl ∣₁ ,
        q≡s+t ∙ (λ i → s≡r+w i + t) ∙ sym (+Assoc r w t))


  +𝕂IdR : (a : 𝕂) → a +𝕂 𝟘 ≡ a
  +𝕂IdR a = ≤𝕂-asym (lift upper⊇) (lift upper⊆)
    where
    upper⊆ : {q : K} → q ∈ (a +𝕂 𝟘) .upper → q ∈ a .upper
    upper⊆ {q = q} q∈upper =
      proof _ , isProp∈ (a .upper) by do
      (s , t , s∈upper , t∈upper , q≡s+t) ← ∈→Inhab (+upper a 𝟘) q∈upper
      return (subst (_∈ a .upper) (sym q≡s+t)
        (a .upper-close (s + t) s s∈upper (+-rPos→> (∈→Inhab (0r <P_) t∈upper))))

    upper⊇ : {q : K} → q ∈ a .upper → q ∈ (a +𝕂 𝟘) .upper
    upper⊇ {q = q} q∈upper =
      proof _ , isProp∈ ((a +𝕂 𝟘) .upper) by do
      (r , r<q , r∈upper) ← a .upper-round q q∈upper
      return (
        Inhab→∈ (+upper a 𝟘) ∣ r , q - r , r∈upper ,
        Inhab→∈ (0r <P_) (>→Diff>0 r<q) , helper1 q r ∣₁)


  +𝕂InvR : (a : 𝕂) → a +𝕂 (-𝕂 a) ≡ 𝟘
  +𝕂InvR a = ≤𝕂-asym (lift upper⊇) (lift upper⊆)
    where
    upper⊆ : {q : K} → q ∈ (a +𝕂 (-𝕂 a)) .upper → q ∈ 𝟘 .upper
    upper⊆ {q = q} q∈upper =
      proof _ , isProp∈ (𝟘 .upper) by do
      (s , t , s∈upper , t∈upper , q≡s+t) ← ∈→Inhab (+upper a (-𝕂 a)) q∈upper
      (p , p<r∈upper , t>-p) ← ∈→Inhab (-upper a) t∈upper
      let p<s : p < s
          p<s = p<r∈upper s s∈upper
          -p>-s : - p > - s
          -p>-s = -Reverse< p<s
          s+t>s-s : s + t > s - s
          s+t>s-s = <-trans (+-lPres< {z = s} -p>-s) (+-lPres< {z = s} t>-p)
          s+t>0 : s + t > 0r
          s+t>0 = subst (s + t >_) (+InvR s) s+t>s-s
          q>0 : q > 0r
          q>0 = subst (_> 0r) (sym q≡s+t) s+t>0
      return (Inhab→∈ (0r <P_) q>0)

    upper⊇ : {q : K} → q ∈ 𝟘 .upper → q ∈ (a +𝕂 (-𝕂 a)) .upper
    upper⊇ {q = q} q∈upper =
      proof _ , isProp∈ ((a +𝕂 (-𝕂 a)) .upper) by do
      let q>0 = ∈→Inhab (0r <P_) q∈upper
      (r , s , s<q∈upper , r<s , r+q∈upper) ← archimedes a q q>0
      return (
        Inhab→∈ (+upper a (-𝕂 a)) ∣ q + r , - r ,
        subst (_∈ a .upper) (+Comm r q) r+q∈upper ,
        Inhab→∈ (-upper a) ∣ s , s<q∈upper , -Reverse< r<s ∣₁ ,
        helper2 q r ∣₁)


  +𝕂IdL : (a : 𝕂) → 𝟘 +𝕂 a ≡ a
  +𝕂IdL a = +𝕂Comm 𝟘 a ∙ +𝕂IdR a

  +𝕂InvL : (a : 𝕂) → (-𝕂 a) +𝕂 a ≡ 𝟘
  +𝕂InvL a = +𝕂Comm (-𝕂 a) a ∙ +𝕂InvR a

  -𝕂Involutive : (a : 𝕂) → -𝕂 (-𝕂 a) ≡ a
  -𝕂Involutive a =
      sym (+𝕂IdR (-𝕂 (-𝕂 a)))
    ∙ (λ i → (-𝕂 (-𝕂 a)) +𝕂 (+𝕂InvL a (~ i)))
    ∙ +𝕂Assoc (-𝕂 (-𝕂 a)) (-𝕂 a) a
    ∙ (λ i → (+𝕂InvL (-𝕂 a) i) +𝕂 a)
    ∙ +𝕂IdL a

  {-

    Multiplication of Non-Negative Reals

  -}

  ·𝕂₊Comm : (a b : 𝕂₊) → a ·𝕂₊ b ≡ b ·𝕂₊ a
  ·𝕂₊Comm a b = path-𝕂₊ _ _ (≤𝕂-asym (lift (upper⊆ b a)) (lift (upper⊆ a b)))
    where
    upper⊆ : (a b : 𝕂₊){q : K} → q ∈ (a ·𝕂₊ b) .fst .upper → q ∈ (b ·𝕂₊ a) .fst .upper
    upper⊆ (a , a≥0) (b , b≥0) {q = q} q∈upper = Inhab→∈ (·upper b a) do
      (s , t , s∈upper , t∈upper , q≡s·t) ← ∈→Inhab (·upper a b) q∈upper
      return (t , s , t∈upper , s∈upper , q≡s·t ∙ ·Comm s t)


  ·𝕂₊Assoc : (a b c : 𝕂₊) → a ·𝕂₊ (b ·𝕂₊ c) ≡ (a ·𝕂₊ b) ·𝕂₊ c
  ·𝕂₊Assoc a b c = path-𝕂₊ _ _ (≤𝕂-asym (lift upper⊇) (lift upper⊆))
    where
    upper⊆ : {q : K} → q ∈ (a ·𝕂₊ (b ·𝕂₊ c)) .fst .upper → q ∈ ((a ·𝕂₊ b) ·𝕂₊ c) .fst .upper
    upper⊆ {q = q} q∈upper = Inhab→∈ (·upper₊ (a ·𝕂₊ b) c) do
      (s , t , s∈upper , t∈upper , q≡s·t) ← ∈→Inhab (·upper₊ a (b ·𝕂₊ c)) q∈upper
      (r , w , r∈upper , w∈upper , t≡r·w) ← ∈→Inhab (·upper₊ b c) t∈upper
      return (
        s · r , w ,
        Inhab→∈ (·upper₊ a b) ∣ s , r , s∈upper , r∈upper , refl ∣₁ ,
        w∈upper , q≡s·t ∙ (λ i → s · t≡r·w i) ∙ ·Assoc s r w)

    upper⊇ : {q : K} → q ∈ ((a ·𝕂₊ b) ·𝕂₊ c) .fst .upper → q ∈ (a ·𝕂₊ (b ·𝕂₊ c)) .fst .upper
    upper⊇ {q = q} q∈upper = Inhab→∈ (·upper₊ a (b ·𝕂₊ c)) do
      (s , t , s∈upper , t∈upper , q≡s·t) ← ∈→Inhab (·upper₊ (a ·𝕂₊ b) c) q∈upper
      (r , w , r∈upper , w∈upper , s≡r·w) ← ∈→Inhab (·upper₊ a b) s∈upper
      return (
        r , w · t ,
        r∈upper , Inhab→∈ (·upper₊ b c) ∣ w , t , w∈upper , t∈upper , refl ∣₁ ,
        q≡s·t ∙ (λ i → s≡r·w i · t) ∙ sym (·Assoc r w t))

  private
    alg-helper : (p q : K)(p≢0 : ¬ p ≡ 0r) → q ≡ p · (q · inv p≢0)
    alg-helper p q p≢0 = sym (·IdR q) ∙ (λ i → q · ·-rInv p≢0 (~ i)) ∙ helper3 p q (inv p≢0)


  ·𝕂₊ZeroR : (a : 𝕂₊) → a ·𝕂₊ 𝟘₊ ≡ 𝟘₊
  ·𝕂₊ZeroR a = path-𝕂₊ _ _ (≤𝕂-asym (lift upper⊇) (lift upper⊆))
    where
    upper⊆ : {q : K} → q ∈ (a ·𝕂₊ 𝟘₊) .fst .upper → q ∈ 𝟘 .upper
    upper⊆ = lower ((a ·𝕂₊ 𝟘₊) .snd)

    upper⊇ : {q : K} → q ∈ 𝟘 .upper → q ∈ (a ·𝕂₊ 𝟘₊) .fst .upper
    upper⊇ {q = q} q∈upper =
      proof _ , isProp∈ ((a ·𝕂₊ 𝟘₊) .fst .upper) by do
      (p , p∈upper) ← a .fst .upper-inhab
      let q>0 = ∈→Inhab (0r <P_) q∈upper
          p>0 = q∈𝕂₊→q>0 a p p∈upper
          p≢0 = >-arefl p>0
          p⁻¹ = inv p≢0
      return (
        Inhab→∈ (·upper₊ a 𝟘₊) ∣ p , q · p⁻¹ , p∈upper ,
        Inhab→∈ (0r <P_) (·-Pres>0 q>0 (p>0→p⁻¹>0 p>0)) , alg-helper p q p≢0 ∣₁)


  ·𝕂₊IdR : (a : 𝕂₊) → a ·𝕂₊ 𝟙₊ ≡ a
  ·𝕂₊IdR a = path-𝕂₊ _ _ (≤𝕂-asym (lift upper⊇) (lift upper⊆))
    where
    upper⊆ : {q : K} → q ∈ (a ·𝕂₊ 𝟙₊) .fst .upper → q ∈ a .fst .upper
    upper⊆ {q = q} q∈upper =
      proof _ , isProp∈ (a .fst .upper) by do
      (s , t , s∈upper , t∈upper , q≡s·t) ← ∈→Inhab (·upper₊ a 𝟙₊) q∈upper
      let s>0 = q∈𝕂₊→q>0 a s s∈upper
      return (subst (_∈ a .fst .upper) (sym q≡s·t)
        (a .fst .upper-close (s · t) s s∈upper (·-Pos·>1→> s>0 (∈→Inhab (1r <P_) t∈upper))))

    upper⊇ : {q : K} → q ∈ a .fst .upper → q ∈ (a ·𝕂₊ 𝟙₊) .fst .upper
    upper⊇ {q = q} q∈upper =
      proof _ , isProp∈ ((a ·𝕂₊ 𝟙₊) .fst .upper) by do
      (r , r<q , r∈upper) ← a .fst .upper-round q q∈upper
      let r>0 = q∈𝕂₊→q>0 a r r∈upper
          r≢0 = >-arefl r>0
          r⁻¹ = inv r≢0
      return (
        Inhab→∈ (·upper₊ a 𝟙₊) ∣ r , q · r⁻¹ , r∈upper ,
        Inhab→∈ (1r <P_) (p>q>0→p·q⁻¹>1  r>0 r<q) , alg-helper r q r≢0 ∣₁)


  ·𝕂₊ZeroL : (a : 𝕂₊) → 𝟘₊ ·𝕂₊ a ≡ 𝟘₊
  ·𝕂₊ZeroL a = ·𝕂₊Comm 𝟘₊ a ∙ ·𝕂₊ZeroR a

  ·𝕂₊IdL : (a : 𝕂₊) → 𝟙₊ ·𝕂₊ a ≡ a
  ·𝕂₊IdL a = ·𝕂₊Comm 𝟙₊ a ∙ ·𝕂₊IdR a


  private
    upper-round2 : (a : 𝕂)(p q : K) → p ∈ a .upper → q ∈ a .upper → ∥ Σ[ r ∈ K ] (r < p) × (r < q) × (r ∈ a .upper) ∥₁
    upper-round2 a p q p∈upper q∈upper = do
      (r , r<p , r∈upper) ← a .upper-round p p∈upper
      (s , s<q , s∈upper) ← a .upper-round q q∈upper
      return (case-split r s r<p r∈upper s<q s∈upper (trichotomy r s))
      where
      case-split : (r s : K)
        → r < p → r ∈ a .upper → s < q → s ∈ a .upper
        → Trichotomy (𝒦 .fst .fst) r s
        → Σ[ t ∈ K ] (t < p) × (t < q) × (t ∈ a .upper)
      case-split r s r<p r∈upper s<q s∈upper (lt r<s) =
        r , r<p , <-trans r<s s<q , r∈upper
      case-split r s r<p r∈upper s<q s∈upper (eq r≡s) =
        s , subst (_< p) r≡s r<p , s<q , s∈upper
      case-split r s r<p r∈upper s<q s∈upper (gt r>s) =
        s , <-trans r>s r<p , s<q , s∈upper


  ·𝕂₊DistR : (a b c : 𝕂₊) → (a ·𝕂₊ b) +𝕂₊ (a ·𝕂₊ c) ≡ a ·𝕂₊ (b +𝕂₊ c)
  ·𝕂₊DistR a b c = path-𝕂₊ _ _ (≤𝕂-asym (lift upper⊇) (lift upper⊆))
    where
    upper⊆ : {q : K} → q ∈ ((a ·𝕂₊ b) +𝕂₊ (a ·𝕂₊ c)) .fst .upper → q ∈ (a ·𝕂₊ (b +𝕂₊ c)) .fst .upper
    upper⊆ {q = q} q∈upper =
      proof _ , isProp∈ ((a ·𝕂₊ (b +𝕂₊ c)) .fst .upper) by do
      (s , t , s∈upper , t∈upper , q≡s+t) ← ∈→Inhab (+upper₊ (a ·𝕂₊ b) (a ·𝕂₊ c)) q∈upper
      (r , w , r∈upper , w∈upper , s≡r·w) ← ∈→Inhab (·upper₊ a b) s∈upper
      (u , v , u∈upper , v∈upper , t≡u·v) ← ∈→Inhab (·upper₊ a c) t∈upper
      (x , x<r , x<u , x∈upper) ← upper-round2 (a .fst) r u r∈upper u∈upper
      let x>0 = q∈𝕂₊→q>0 a x x∈upper
          w>0 = q∈𝕂₊→q>0 b w w∈upper
          v>0 = q∈𝕂₊→q>0 c v v∈upper
          x·w+x·v<r·w+u·v : x · w + x · v < r · w + u · v
          x·w+x·v<r·w+u·v = +-Pres< (·-rPosPres< w>0 x<r) (·-rPosPres< v>0 x<u)
          x·[w+v]<r·w+u·v : x · (w + v) < r · w + u · v
          x·[w+v]<r·w+u·v = subst (_< (r · w + u · v)) (sym (·DistR+ x w v)) x·w+x·v<r·w+u·v
          x·[w+v]∈upper : x · (w + v) ∈ (a ·𝕂₊ (b +𝕂₊ c)) .fst .upper
          x·[w+v]∈upper = Inhab→∈ (·upper₊ a (b +𝕂₊ c))
            ∣ x , w + v , x∈upper ,
              Inhab→∈ (+upper₊ b c) ∣ w , v , w∈upper , v∈upper , refl ∣₁ , refl ∣₁
          r·w+u·v≡q : r · w + u · v ≡ q
          r·w+u·v≡q = (λ i → s≡r·w (~ i) + t≡u·v (~ i)) ∙ sym q≡s+t
          x·[w+v]<q : x · (w + v) < q
          x·[w+v]<q = subst (x · (w + v) <_) r·w+u·v≡q x·[w+v]<r·w+u·v
      return ((a ·𝕂₊ (b +𝕂₊ c)) .fst .upper-close _ _ x·[w+v]∈upper x·[w+v]<q)

    upper⊇ : {q : K} → q ∈ (a ·𝕂₊ (b +𝕂₊ c)) .fst .upper → q ∈ ((a ·𝕂₊ b) +𝕂₊ (a ·𝕂₊ c)) .fst .upper
    upper⊇ {q = q} q∈upper = Inhab→∈ (+upper₊ (a ·𝕂₊ b) (a ·𝕂₊ c)) do
      (s , t , s∈upper , t∈upper , q≡s·t) ← ∈→Inhab (·upper₊ a (b +𝕂₊ c)) q∈upper
      (r , w , r∈upper , w∈upper , t≡r+w) ← ∈→Inhab (+upper₊ b c) t∈upper
      return (s · r , s · w ,
        Inhab→∈ (·upper₊ a b) ∣ s , r , s∈upper , r∈upper , refl ∣₁ ,
        Inhab→∈ (·upper₊ a c) ∣ s , w , s∈upper , w∈upper , refl ∣₁ ,
        q≡s·t ∙ cong (s ·_) t≡r+w ∙ ·DistR+ s r w)


  -- Multiplicative Inverse

  module _
    (a₊@(a , a≥0) : 𝕂₊)(q₀ : K)(q₀>0 : q₀ > 0r)
    (q₀<r∈upper : ((r : K) → r ∈ a .upper → q₀ < r)) where

    private
      a⁻¹ : 𝕂₊
      a⁻¹ = inv𝕂₊ a q₀ q₀>0 q₀<r∈upper

      a·a⁻¹ = (a₊ ·𝕂₊ a⁻¹) .fst

      ineq-helper : (r q q' : K) → q - 1r > 0r → r > q' → r + (q' · (q - 1r)) < r · q
      ineq-helper r q q' q-1>0 r>q' = subst (r + (q' · (q - 1r)) <_) (helper4 q r) r+·<r+·
        where r+·<r+· : r + (q' · (q - 1r)) < r + (r · (q - 1r))
              r+·<r+· = +-lPres< (·-rPosPres< q-1>0 r>q')

    ·𝕂₊InvR' : a·a⁻¹ ≡ 𝟙
    ·𝕂₊InvR' = ≤𝕂-asym (lift upper⊇) (lift upper⊆)
      where
      upper⊆ : {q : K} → q ∈ a·a⁻¹ .upper → q ∈ 𝟙 .upper
      upper⊆ {q = q} q∈upper =
        proof _ , isProp∈ (𝟙 .upper) by do
        (s , t , s∈upper , t∈upper , q≡s·t) ← ∈→Inhab (·upper₊ a₊ a⁻¹) q∈upper
        (p , p>0 , p<r∈upper , t>p⁻¹) ← ∈→Inhab (inv-upper a) t∈upper
        let p<s : p < s
            p<s = p<r∈upper s s∈upper
            s>0 : s > 0r
            s>0 = <-trans q₀>0 (q₀<r∈upper s s∈upper)
            p⁻¹ = inv (>-arefl p>0)
            s⁻¹ = inv (>-arefl s>0)
            p⁻¹>s⁻¹ : p⁻¹ > s⁻¹
            p⁻¹>s⁻¹ = inv-Reverse< s>0 p>0 p<s
            s·t>s·s⁻¹ : s · t > s · s⁻¹
            s·t>s·s⁻¹ = <-trans (·-lPosPres< {x = s} s>0 p⁻¹>s⁻¹) (·-lPosPres< {x = s} s>0 t>p⁻¹)
            s·t>1 : s · t > 1r
            s·t>1 = subst (s · t >_) (·-rInv (>-arefl s>0)) s·t>s·s⁻¹
            q>1 : q > 1r
            q>1 = subst (_> 1r) (sym q≡s·t) s·t>1
        return (Inhab→∈ (1r <P_) q>1)

      upper⊇ : {q : K} → q ∈ 𝟙 .upper → q ∈ a·a⁻¹ .upper
      upper⊇ {q = q} q∈upper =
        proof _ , isProp∈ (a·a⁻¹ .upper) by do
        let q>1 = ∈→Inhab (1r <P_) q∈upper
            q-1>0 : q - 1r > 0r
            q-1>0 = subst (q - 1r >_) (+InvR 1r) (+-rPres< {z = - 1r} q>1)
            q' = middle 0r q₀
            q'>0 : q' > 0r
            q'>0 = middle>l q₀>0
            q'<q₀ : q' < q₀
            q'<q₀ = middle<r q₀>0
            ε = q' · (q - 1r)
            ε>0 : ε > 0r
            ε>0 = ·-Pres>0 q'>0 q-1>0
        (r , s , s<q∈upper , q'<r , r<s , r+ε∈upper) ← archimedes' a ε ε>0 q' (q₀ , q₀<r∈upper , q'<q₀)
        let r+ε<r·q : r + ε < r · q
            r+ε<r·q = ineq-helper r q q' q-1>0 q'<r
            r·q∈upper : r · q ∈ a .upper
            r·q∈upper = a .upper-close _ _ r+ε∈upper r+ε<r·q
            r>0 : r > 0r
            r>0 = <-trans q'>0 q'<r
            r⁻¹ = inv (>-arefl r>0)
            s>0 : s > 0r
            s>0 = <-trans r>0 r<s
            r⁻¹∈upper : r⁻¹ ∈ a⁻¹ .fst .upper
            r⁻¹∈upper = Inhab→∈ (inv-upper a)
              ∣ s , s>0 , s<q∈upper , inv-Reverse< s>0 r>0 r<s ∣₁
        return (Inhab→∈ (·upper₊ a₊ a⁻¹)
          ∣ r · q , r⁻¹ , r·q∈upper , r⁻¹∈upper ,
          alg-helper r q (>-arefl r>0) ∙ ·Assoc r q r⁻¹ ∣₁)
