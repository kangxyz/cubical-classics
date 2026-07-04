{-

Sequence of Real Numbers

This file contains:
- Basics of real-number sequence;
- The monotone convergence theorem;
- The Bolzano-Weierstrass theorem;
- The Cauchy completeness of ℝ.

-}
{-# OPTIONS --safe #-}
module Classical.Analysis.Real.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
  using    (ℕ ; suc ; zero)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
  using    (<-weaken ; ≤0→≡0)
  renaming (_>_ to _>ℕ_ ; _<_ to _<ℕ_
          ; _≥_ to _≥ℕ_ ; _≤_ to _≤ℕ_
          ; isProp≤  to isProp≤ℕ
          ; ≤-refl   to ≤ℕ-refl
          ; <-trans  to <ℕ-trans
          ; <≤-trans to <≤ℕ-trans
          ; ≤<-trans to ≤<ℕ-trans)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Nullary

open import Classical.Axioms
open import Classical.Foundations.Powerset
open import Classical.Preliminary.Nat
open import Classical.Preliminary.Logic
open import Constructive.Algebra.StrictlyOrderedCommRing.AbsoluteValue
open import Constructive.Algebra.OrderedField
open import Classical.Algebra.OrderedField.Extremum
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Topology.Metric
open import Classical.Topology.Metric.Sequence
open import Classical.Analysis.Real.Base
open import Classical.Analysis.Real.Topology


module _ ⦃ 🤖 : Oracle ⦄ where

  open Oracle 🤖

  open OrderedFieldStr (ℝMacNeilleCompleteOrderedField .fst)
  open AbsoluteValue   (ℝMacNeilleCompleteOrderedField .fst .fst)
  open Metric   ℝMetric

  open MacNeilleCompleteOrderedField (ℝMacNeilleCompleteOrderedField .fst)
  open Extremum        (ℝMacNeilleCompleteOrderedField .fst)
  open Supremum

  open Limit
  open ClusterPoint

  private
    getSup = ℝMacNeilleCompleteOrderedField .snd


  {-

    Monotone Convergence Theorem

  -}

  -- Monotone increasing and upper-bounded sequence

  isIncreasing : (ℕ → ℝ) → Type
  isIncreasing seq = (m n : ℕ) → m ≥ℕ n → seq m ≥ seq n

  isUpperBoundedSequence : (ℕ → ℝ) → Type
  isUpperBoundedSequence seq = ∥ Σ[ b ∈ ℝ ] ((n : ℕ) → seq n ≤ b) ∥₁


  -- A weaker formulation of increasing, and its equivalence.

  isIncreasing' : (ℕ → ℝ) → Type
  isIncreasing' seq = (n : ℕ) → seq (suc n) ≥ seq n

  isIncreasing'→isIncreasing : {seq : ℕ → ℝ} → isIncreasing' seq → isIncreasing seq
  isIncreasing'→isIncreasing {seq = seq} incr m n m≥n = ≥-helper m (m≥n .fst) (m≥n .snd)
    where
    ≥-helper : (m k : ℕ) → k +ℕ n ≡ m → seq m ≥ seq n
    ≥-helper m 0 n≡m  = subst (λ x → seq x ≥ seq n) n≡m  (≤-refl refl)
    ≥-helper m 1 sn≡m = subst (λ x → seq x ≥ seq n) sn≡m (incr n)
    ≥-helper m (suc (suc k)) ssk+n≡m = subst (λ x → seq x ≥ seq n) ssk+n≡m
        (≤-trans (≥-helper _ (suc k) refl) (incr _))


  -- A monotone increasing and upper-bounded sequence has a limit.

  isMonoBounded→Limit : {seq : ℕ → ℝ} → isIncreasing seq → isUpperBoundedSequence seq → Limit seq
  isMonoBounded→Limit {seq = seq} incr boundSeq =
    record { lim = limit ; conv = λ ε ε>0 → ∣ n₀ ε ε>0 , converge ε ε>0 ∣₁ }
    where

    seq-prop : ℝ → hProp _
    seq-prop x = ∥ Σ[ n ∈ ℕ ] seq n ≡ x ∥₁ , squash₁

    seq-sub : ℙ ℝ
    seq-sub = specify seq-prop

    boundSub : isUpperBounded seq-sub
    boundSub = do
      (b , seqn≤b) ← boundSeq
      return (b , λ r r∈sub →
        proof _ , isProp≤ by do
        (n , seqn≡r) ← ∈→Inhab seq-prop r∈sub
        return (subst (_≤ b) seqn≡r (seqn≤b n)))

    seq-sup : Supremum seq-sub
    seq-sup = getSup ∣ _ , Inhab→∈ seq-prop ∣ 0 , refl ∣₁ ∣₁ boundSub

    limit : ℝ
    limit = seq-sup .sup

    lim-seqn≥0 : (n : ℕ) → limit - seq n ≥ 0
    lim-seqn≥0 n = ≥→Diff≥0 (seq-sup .bound _ (Inhab→∈ seq-prop ∣ _ , refl ∣₁))

    module _ (ε : ℝ)(ε>0 : ε > 0) where

      ∃p : ∥ Σ[ n ∈ ℕ ] (limit - seq n < ε) ∥₁
      ∃p = do
        (x , lim-ε<x , x∈sub) ← <sup→∃∈ _ seq-sup (-rPos→< ε>0)
        (n , seqn≡x) ← ∈→Inhab seq-prop x∈sub
        let lim-ε<seqn : limit - ε < seq n
            lim-ε<seqn = subst (limit - ε <_) (sym seqn≡x) lim-ε<x
            lim-seqn<ε : limit - seq n < ε
            lim-seqn<ε = +-MoveRToL<' (-MoveLToR< lim-ε<seqn)
        return (n , lim-seqn<ε)

      Σp : Σ[ n ∈ ℕ ] limit - seq n < ε
      Σp = findByOracle (λ _ → isProp<) ∃p

      n₀ = Σp .fst

      converge : (n : ℕ) → n >ℕ n₀ → abs (limit - seq n) < ε
      converge n n>n₀ =
        subst (_< ε) (sym (x≥0→abs≡x (lim-seqn≥0 n))) lim-seqn<ε
        where
        lim-seqn<ε : limit - seq n < ε
        lim-seqn<ε = ≤<-trans (+-lPres≤ (-Reverse≤ (incr _ _ (<-weaken n>n₀)))) (Σp .snd)


  {-

    The Bolzano-Weierstrass Theorem

  -}

  -- Bounded sequence

  isBoundedSequence : (ℕ → ℝ) → Type
  isBoundedSequence seq = ∥ Σ[ a ∈ ℝ ] Σ[ b ∈ ℝ ] ((n : ℕ) → (a ≤ seq n) × (seq n ≤ b)) ∥₁


  -- A bounded sequence of real numbers admits a cluster point.

  isBounded→ClusterPoint : {seq : ℕ → ℝ} → isBoundedSequence seq → ClusterPoint seq
  isBounded→ClusterPoint {seq = seq} bSeq = record { point = x₀ ; accum = ∃cluster }
    where

    accum-prop : ℝ → hProp _
    accum-prop x = ((n : ℕ) → ∥ Σ[ n' ∈ ℕ ] (n ≤ℕ n') × (x ≤ seq n') ∥₁) ,
      isPropΠ (λ _ → squash₁)

    accum-sub = specify accum-prop

    module _
      ((a , b , bound) : Σ[ a ∈ ℝ ] Σ[ b ∈ ℝ ] ((n : ℕ) → (a ≤ seq n) × (seq n ≤ b)))
      where

      a∈accum : a ∈ accum-sub
      a∈accum = Inhab→∈ accum-prop (λ n → ∣ n , ≤ℕ-refl , bound n .fst ∣₁)

      x∈accum→x≤b : (x : ℝ) → x ∈ accum-sub → x ≤ b
      x∈accum→x≤b x x∈accum = ¬<→≥ ¬x>b
        where
        ¬x>b : ¬ x > b
        ¬x>b x>b =
          proof _ , isProp⊥ by do
          (n , _ , x≤seqn) ← ∈→Inhab accum-prop x∈accum 0
          return (<≤-asym x>b (≤-trans x≤seqn (bound n .snd)))

      inhabSub : isInhabited  accum-sub
      inhabSub = ∣ a , a∈accum ∣₁

      boundSub : isUpperBounded  accum-sub
      boundSub = ∣ b , x∈accum→x≤b ∣₁

    accum-sup : Supremum accum-sub
    accum-sup = getSup (Prop.rec squash₁ inhabSub bSeq) (Prop.rec squash₁ boundSub bSeq)

    x₀ = accum-sup .sup

    ∃fin>x₀ : (ε : ℝ) → ε > 0 → ∥ Σ[ n₀ ∈ ℕ ] ((n : ℕ) → n₀ ≤ℕ n → seq n < x₀ + ε) ∥₁
    ∃fin>x₀  ε ε>0 = do
      (n₀ , ¬p) ←
        ¬∀→∃¬ (λ _ → squash₁) (∉→Empty accum-prop
          (¬∈→∉ {A = accum-sub} (>sup→¬∈ _ accum-sup (+-rPos→> ε>0))))
      return (n₀ , λ n n₀≤n → ¬≤→> (¬∃→∀¬2 ¬p n n₀≤n))

    ∃cluster : isClusteringAt seq x₀
    ∃cluster n₀ ε ε>0 = do
      (m₀ , fin>x₀) ← ∃fin>x₀ ε ε>0
      (x , x₀-ε<x , x∈sub) ← <sup→∃∈ _ accum-sup (-rPos→< ε>0)
      let m = sucmax n₀ m₀
      (n , n≥m , x≤seqn) ← ∈→Inhab accum-prop x∈sub m
      let x₀-ε<seqn : x₀ - ε < seq n
          x₀-ε<seqn = <≤-trans x₀-ε<x x≤seqn
          seqn<x₀+ε : seq n < x₀ + ε
          seqn<x₀+ε = fin>x₀ n (<-weaken (<≤ℕ-trans (sucmax>right {m = n₀} {n = m₀}) n≥m))
      return (n , <≤ℕ-trans (sucmax>left {m = n₀} {n = m₀}) n≥m ,
        absInOpenInterval ε>0 x₀-ε<seqn seqn<x₀+ε)


  {-

    Cauchy Sequences in ℝ

  -}

  -- A Cauchy sequence is bounded.

  isCauchy→isBoundedSequence : {seq : ℕ → ℝ} → isCauchy seq → isBoundedSequence seq
  isCauchy→isBoundedSequence {seq = seq} cauchy = bSeq
    where

    finBound : (n : ℕ) → Σ[ a ∈ ℝ ] Σ[ b ∈ ℝ ] ((m : ℕ) → (m ≤ℕ n) → (a ≤ seq m) × (seq m ≤ b))
    finBound zero = seq 0 , seq 0 , λ m m≤n →
      subst (λ k → (seq 0 ≤ seq k) × (seq k ≤ seq 0)) (sym (≤0→≡0 m≤n)) (≤-refl refl , ≤-refl refl)
    finBound (suc n) = a , b , λ m m≤n → case-split m (≤-ind m≤n)
      where
      a' = finBound n .fst
      b' = finBound n .snd .fst
      bfin = finBound n .snd .snd

      a = min a' (seq (suc n))
      b = max b' (seq (suc n))

      case-split : (m : ℕ) → (m ≤ℕ n) ⊎ (m ≡ suc n) → (a ≤ seq m) × (seq m ≤ b)
      case-split m (inl m≤n) = ≤-trans min≤left (bfin _ m≤n .fst) , ≤-trans (bfin _ m≤n .snd) max≥left
      case-split m (inr m≡sn) = subst (λ k → (a ≤ seq k) × (seq k ≤ b)) (sym m≡sn) (min≤right , max≥right)

    module _
      (ε : ℝ)(ε>0 : ε > 0)(n₀ : ℕ)
      (abs< : (n : ℕ) → n >ℕ n₀ → abs (seq n₀ - seq n) < ε) where

      a = finBound n₀ .fst
      b = finBound n₀ .snd .fst
      bfin = finBound n₀ .snd .snd

      case-split : (n : ℕ) → (n >ℕ n₀) ⊎ (n ≤ℕ n₀) → (a - ε ≤ seq n) × (seq n ≤ b + ε)
      case-split n (inr n≤n₀) =
        ≤-trans (<-≤-weaken (-rPos→< ε>0)) (bfin _ n≤n₀ .fst) ,
        ≤-trans (bfin _ n≤n₀ .snd) (<-≤-weaken (+-rPos→> ε>0))
      case-split n (inl n>n₀) =
        <-≤-weaken (absSuppress≥ (bfin _ ≤ℕ-refl .fst) (abs< _ n>n₀)) ,
        <-≤-weaken (absSuppress≤ (bfin _ ≤ℕ-refl .snd) (abs< _ n>n₀))

      ΣbSeq : Σ[ a ∈ ℝ ] Σ[ b ∈ ℝ ] ((n : ℕ) → (a ≤ seq n) × (seq n ≤ b))
      ΣbSeq = a - ε , b + ε , λ n → case-split n (<≤-split n₀ n)

    bSeq : isBoundedSequence seq
    bSeq = do
      (n₀ , abs<') ← cauchy 1 1>0
      return (ΣbSeq 1 1>0 (suc n₀) (λ n n>sn₀ →
        abs<' (suc n₀) n ≤ℕ-refl (<ℕ-trans ≤ℕ-refl n>sn₀)))


  -- The real numbers are Cauchy complete.

  isCauchy→Limit : isCauchyComplete
  isCauchy→Limit {seq = seq} cauchy = record { lim = cluster .point ; conv = converge }
    where

    cluster = isBounded→ClusterPoint (isCauchy→isBoundedSequence cauchy)

    module _ (ε : ℝ)(ε>0 : ε > 0) where

      ε/2 = middle 0 ε
      ε/2>0 = middle>l ε>0

      converge : ∥ Σ[ n₀ ∈ ℕ ] ((n : ℕ) → n >ℕ n₀ → abs (cluster .point - seq n) < ε) ∥₁
      converge = do
        (n₀ , ∀abs<) ← cauchy ε/2 ε/2>0
        (n₁ , n₁>n₀ , abs<) ← cluster .accum n₀ ε/2 ε/2>0
        return (
          n₁ , λ n n>n₁ →
            dist-triangle<ε ε>0 abs< (∀abs< n₁ n n₁>n₀ (<ℕ-trans n₁>n₀ n>n₁)))
