{-

Fixed-degree binomial-geometric weights.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.BinomialGeometric where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.GeometricDecay
  using
    ( positiveGeometricGap-positive
    ; positiveRationalPower-nonnegative
    )
open import Constructive.Analysis.GeometricDecay.Rational
  using (rationalPower)
open import Constructive.Data.PositiveRationals
  using (ℚ⁺ ; radius ; 1⁺ ; _*⁺_ ; _⊖_[_] ; posInv⁺)
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    step-bound :
      (q C g : 𝓡 .fst) →
      q · (C · g) + C ≡ (q · g + 1r) · C
    step-bound _ _ _ = solve! 𝓡

    weight-step :
      (q b c p : 𝓡 .fst) →
      q · (b · p) + c · (q · p) ≡ (b + c) · (q · p)
    weight-step _ _ _ _ = solve! 𝓡

open import Constructive.Analysis.Reals.PowerSeries.Recenter.Binomial
  using (binomialℕ ; natMul-one-+)


binomialGeometricWeight :
  ℚ⁺ →
  ℕ →
  ℕ →
  ℚ
binomialGeometricWeight q zero k =
  rationalPower (radius q) k
binomialGeometricWeight q (suc n) zero =
  Rational.1ℚ
binomialGeometricWeight q (suc n) (suc k) =
  radius q ℚ.· binomialGeometricWeight q (suc n) k ℚ.+
  binomialGeometricWeight q n (suc k)


binomialGeometricBoundScale :
  (q : ℚ⁺) →
  radius q ℚOrder.< Rational.1ℚ →
  ℕ →
  ℚ⁺
binomialGeometricBoundScale q q<1 zero =
  1⁺
binomialGeometricBoundScale q q<1 (suc n) =
  binomialGeometricBoundScale q q<1 n *⁺
  posInv⁺ (1⁺ ⊖ q [ q<1 ])


binomialℕ-above-diagonal :
  (n k : ℕ) →
  binomialℕ n (suc (n Nat.+ k)) ≡ zero
binomialℕ-above-diagonal zero k =
  refl
binomialℕ-above-diagonal (suc n) k =
  cong₂
    Nat._+_
    (subst
      (λ m → binomialℕ n (suc m) ≡ zero)
      (Nat.+-suc n k)
      (binomialℕ-above-diagonal n (suc k)))
    (binomialℕ-above-diagonal n k)


binomialℕ-diagonal :
  (n : ℕ) →
  binomialℕ n n ≡ suc zero
binomialℕ-diagonal zero =
  refl
binomialℕ-diagonal (suc n) =
  cong₂
    Nat._+_
    (subst
      (λ m → binomialℕ n m ≡ zero)
      (cong suc (Nat.+-zero n))
      (binomialℕ-above-diagonal n zero))
    (binomialℕ-diagonal n)


binomialGeometricWeight-path :
  (q : ℚ⁺) →
  (n k : ℕ) →
  binomialGeometricWeight q n k ≡
  Rational.natMul (binomialℕ (n Nat.+ k) n) Rational.1ℚ ℚ.·
  rationalPower (radius q) k
binomialGeometricWeight-path q zero k =
  sym (ℚ.·IdL qpow) ∙
  cong
    (λ r → r ℚ.· qpow)
    (sym (Rational.natMul-one Rational.1ℚ))
  where
  qpow : ℚ
  qpow =
    rationalPower (radius q) k
binomialGeometricWeight-path q (suc n) zero =
  sym (ℚ.·IdR Rational.1ℚ) ∙
  cong
    (λ r → r ℚ.· Rational.1ℚ)
    (sym (Rational.natMul-one Rational.1ℚ)) ∙
  cong
    (λ b → Rational.natMul b Rational.1ℚ ℚ.· Rational.1ℚ)
    (sym diagonal)
  where
  diagonal :
    binomialℕ (suc n Nat.+ zero) (suc n) ≡ suc zero
  diagonal =
    cong (λ m → binomialℕ m (suc n)) (Nat.+-zero (suc n)) ∙
    binomialℕ-diagonal (suc n)
binomialGeometricWeight-path q (suc n) (suc k) =
  cong₂
    (λ l r → radius q ℚ.· l ℚ.+ r)
    (binomialGeometricWeight-path q (suc n) k)
    (binomialGeometricWeight-path q n (suc k)) ∙
  SolverHelpers.weight-step ℚCommRing (radius q) left right qpow ∙
  cong
    (λ r → r ℚ.· (radius q ℚ.· qpow))
    (sym (natMul-one-+ leftℕ rightℕ)) ∙
  cong
    (λ b →
      Rational.natMul b Rational.1ℚ ℚ.·
      (radius q ℚ.· qpow))
    (sym target-binomial-path)
  where
  qpow : ℚ
  qpow =
    rationalPower (radius q) k

  leftℕ : ℕ
  leftℕ =
    binomialℕ (suc n Nat.+ k) (suc n)

  rightℕ : ℕ
  rightℕ =
    binomialℕ (n Nat.+ suc k) n

  left : ℚ
  left =
    Rational.natMul leftℕ Rational.1ℚ

  right : ℚ
  right =
    Rational.natMul rightℕ Rational.1ℚ

  left-index-path :
    binomialℕ (suc n Nat.+ k) (suc n) ≡
    binomialℕ (n Nat.+ suc k) (suc n)
  left-index-path =
    cong (λ m → binomialℕ m (suc n)) (sym (Nat.+-suc n k))

  target-binomial-path :
    binomialℕ (suc n Nat.+ suc k) (suc n) ≡
    leftℕ Nat.+ rightℕ
  target-binomial-path =
    refl ∙
    cong₂
      Nat._+_
      (sym left-index-path)
      refl


binomialGeometricWeight-nonnegative :
  (q : ℚ⁺) →
  (n k : ℕ) →
  Rational.0ℚ ℚOrder.≤ binomialGeometricWeight q n k
binomialGeometricWeight-nonnegative q zero k =
  positiveRationalPower-nonnegative q k
binomialGeometricWeight-nonnegative q (suc n) zero =
  Rational.<→≤ {p = Rational.0ℚ} {q = Rational.1ℚ} Rational.0<1
binomialGeometricWeight-nonnegative q (suc n) (suc k) =
  subst
    (λ r → r ℚOrder.≤ term ℚ.+ rest)
    (sym (ℚ.+IdR Rational.0ℚ))
    (ℚOrder.≤Monotone+
      Rational.0ℚ
      term
      Rational.0ℚ
      rest
      term-nonnegative
      rest-nonnegative)
  where
  term : ℚ
  term =
    radius q ℚ.· binomialGeometricWeight q (suc n) k

  rest : ℚ
  rest =
    binomialGeometricWeight q n (suc k)

  term-nonnegative : Rational.0ℚ ℚOrder.≤ term
  term-nonnegative =
    Rational.mul-nonnegative
      {a = radius q}
      {b = binomialGeometricWeight q (suc n) k}
      (Rational.<→≤ {p = Rational.0ℚ} {q = radius q} (q .snd))
      (binomialGeometricWeight-nonnegative q (suc n) k)

  rest-nonnegative : Rational.0ℚ ℚOrder.≤ rest
  rest-nonnegative =
    binomialGeometricWeight-nonnegative q n (suc k)


binomialGeometricGap :
  (q : ℚ⁺) →
  radius q ℚOrder.< Rational.1ℚ →
  ℚ⁺
binomialGeometricGap q q<1 =
  1⁺ ⊖ q [ q<1 ]


binomialGeometricGap-sum :
  (q : ℚ⁺) →
  (q<1 : radius q ℚOrder.< Rational.1ℚ) →
  radius q ℚ.+ radius (binomialGeometricGap q q<1) ≡ Rational.1ℚ
binomialGeometricGap-sum q q<1 =
  Rational.p+[q-p]≡q (radius q) Rational.1ℚ


binomialGeometricGap-inv-cancel :
  (q : ℚ⁺) →
  (q<1 : radius q ℚOrder.< Rational.1ℚ) →
  radius q ℚ.· radius (posInv⁺ (binomialGeometricGap q q<1)) ℚ.+
    Rational.1ℚ
  ≡
  radius (posInv⁺ (binomialGeometricGap q q<1))
binomialGeometricGap-inv-cancel q q<1 =
  cong
    (radius q ℚ.· inv-gap ℚ.+_)
    (sym (Rational.posInv-right gap gap-positive)) ∙
  sym (ℚ.·DistR+ (radius q) gap inv-gap) ∙
  cong (λ r → r ℚ.· inv-gap) (binomialGeometricGap-sum q q<1) ∙
  ℚ.·IdL inv-gap
  where
  gap : ℚ
  gap =
    radius (binomialGeometricGap q q<1)

  inv-gap : ℚ
  inv-gap =
    radius (posInv⁺ (binomialGeometricGap q q<1))

  gap-positive : Rational.0ℚ ℚOrder.< gap
  gap-positive =
    positiveGeometricGap-positive q q<1




binomialGeometricGap≤1 :
  (q : ℚ⁺) →
  (q<1 : radius q ℚOrder.< Rational.1ℚ) →
  radius (binomialGeometricGap q q<1) ℚOrder.≤ Rational.1ℚ
binomialGeometricGap≤1 q q<1 =
  Rational.sub-nonnegative-right≤
    (Rational.<→≤ {p = Rational.0ℚ} {q = radius q} (q .snd))


binomialGeometricBoundScale≥1 :
  (q : ℚ⁺) →
  (q<1 : radius q ℚOrder.< Rational.1ℚ) →
  (n : ℕ) →
  Rational.1ℚ ℚOrder.≤ radius (binomialGeometricBoundScale q q<1 n)
binomialGeometricBoundScale≥1 q q<1 zero =
  Rational.≤-refl Rational.1ℚ
binomialGeometricBoundScale≥1 q q<1 (suc n) =
  Rational.mul-right-cancel-positive-≤
    {p = Rational.1ℚ}
    {q = radius (binomialGeometricBoundScale q q<1 (suc n))}
    {c = gap}
    gap-positive
    scaled≤
  where
  gap : ℚ
  gap =
    radius (binomialGeometricGap q q<1)

  gap-positive : Rational.0ℚ ℚOrder.< gap
  gap-positive =
    positiveGeometricGap-positive q q<1

  scale : ℚ
  scale =
    radius (binomialGeometricBoundScale q q<1 n)

  inv-gap : ℚ
  inv-gap =
    radius (posInv⁺ (binomialGeometricGap q q<1))

  gap≤scale : gap ℚOrder.≤ scale
  gap≤scale =
    Rational.≤-trans
      {p = gap}
      {q = Rational.1ℚ}
      {r = scale}
      (binomialGeometricGap≤1 q q<1)
      (binomialGeometricBoundScale≥1 q q<1 n)

  scaled≤ :
    Rational.1ℚ ℚ.· gap
      ℚOrder.≤
    (scale ℚ.· inv-gap) ℚ.· gap
  scaled≤ =
    subst2
      ℚOrder._≤_
      (sym (ℚ.·IdL gap))
      (sym
        (sym (ℚ.·Assoc scale inv-gap gap) ∙
         cong (scale ℚ.·_)
          (Rational.posInv-left gap gap-positive) ∙
         ℚ.·IdR scale))
      gap≤scale


binomialGeometricWeight≤scale :
  (q : ℚ⁺) →
  (q<1 : radius q ℚOrder.< Rational.1ℚ) →
  (n k : ℕ) →
  binomialGeometricWeight q n k
    ℚOrder.≤
  radius (binomialGeometricBoundScale q q<1 n)
binomialGeometricWeight≤scale q q<1 zero k =
  positiveGeometricPower≤1 q q<1 k
  where
  positiveGeometricPower≤1 :
    (ρ : ℚ⁺) →
    radius ρ ℚOrder.< Rational.1ℚ →
    (m : ℕ) →
    rationalPower (radius ρ) m ℚOrder.≤ Rational.1ℚ
  positiveGeometricPower≤1 ρ ρ<1 zero =
    Rational.≤-refl Rational.1ℚ
  positiveGeometricPower≤1 ρ ρ<1 (suc m) =
    Rational.≤-trans
      {p = radius ρ ℚ.· rationalPower (radius ρ) m}
      {q = Rational.1ℚ ℚ.· rationalPower (radius ρ) m}
      {r = Rational.1ℚ}
      (ℚOrder.≤-·o
        (radius ρ)
        Rational.1ℚ
        (rationalPower (radius ρ) m)
        (positiveRationalPower-nonnegative ρ m)
        (Rational.<→≤ {p = radius ρ} {q = Rational.1ℚ} ρ<1))
      (subst
        (λ r → r ℚOrder.≤ Rational.1ℚ)
        (sym (ℚ.·IdL (rationalPower (radius ρ) m)))
        (positiveGeometricPower≤1 ρ ρ<1 m))
binomialGeometricWeight≤scale q q<1 (suc n) zero =
  binomialGeometricBoundScale≥1 q q<1 (suc n)
binomialGeometricWeight≤scale q q<1 (suc n) (suc k) =
  Rational.≤-trans
    {p = left}
    {q = radius q ℚ.· bound ℚ.+ bound-n}
    {r = bound}
    step≤
    bound-step≤
  where
  left : ℚ
  left =
    binomialGeometricWeight q (suc n) (suc k)

  prev : ℚ
  prev =
    binomialGeometricWeight q (suc n) k

  curr : ℚ
  curr =
    binomialGeometricWeight q n (suc k)

  bound-n : ℚ
  bound-n =
    radius (binomialGeometricBoundScale q q<1 n)

  gap : ℚ
  gap =
    radius (binomialGeometricGap q q<1)

  inv-gap : ℚ
  inv-gap =
    radius (posInv⁺ (binomialGeometricGap q q<1))

  bound : ℚ
  bound =
    radius (binomialGeometricBoundScale q q<1 (suc n))

  bound-path : bound ≡ bound-n ℚ.· inv-gap
  bound-path =
    refl

  q-nonnegative : Rational.0ℚ ℚOrder.≤ radius q
  q-nonnegative =
    Rational.<→≤ {p = Rational.0ℚ} {q = radius q} (q .snd)

  step≤ :
    left ℚOrder.≤ radius q ℚ.· bound ℚ.+ bound-n
  step≤ =
    ℚOrder.≤Monotone+
      (radius q ℚ.· prev)
      (radius q ℚ.· bound)
      curr
      bound-n
      (Rational.mul-left-nonnegative-≤
        {a = radius q}
        {b = prev}
        {c = bound}
        q-nonnegative
        (binomialGeometricWeight≤scale q q<1 (suc n) k))
      (binomialGeometricWeight≤scale q q<1 n (suc k))

  gap-positive : Rational.0ℚ ℚOrder.< gap
  gap-positive =
    positiveGeometricGap-positive q q<1

  bound-n-nonnegative : Rational.0ℚ ℚOrder.≤ bound-n
  bound-n-nonnegative =
    Rational.<→≤
      {p = Rational.0ℚ}
      {q = bound-n}
      (binomialGeometricBoundScale q q<1 n .snd)

  bound-step≤ :
    radius q ℚ.· bound ℚ.+ bound-n ℚOrder.≤ bound
  bound-step≤ =
    Rational.mul-right-cancel-positive-≤
      {p = radius q ℚ.· bound ℚ.+ bound-n}
      {q = bound}
      {c = gap}
      gap-positive
      (subst2
        ℚOrder._≤_
        (sym left-path)
        (sym right-path)
        product≤product)
    where
    left-path :
      (radius q ℚ.· bound ℚ.+ bound-n) ℚ.· gap ≡
      (radius q ℚ.· inv-gap ℚ.+ Rational.1ℚ) ℚ.· bound-n ℚ.· gap
    left-path =
      cong (λ r → (radius q ℚ.· r ℚ.+ bound-n) ℚ.· gap) bound-path ∙
      cong (λ r → r ℚ.· gap)
        (SolverHelpers.step-bound
          ℚCommRing
          (radius q)
          bound-n
          inv-gap)

    right-path :
      bound ℚ.· gap ≡
      inv-gap ℚ.· bound-n ℚ.· gap
    right-path =
      cong (λ r → r ℚ.· gap) bound-path ∙
      cong (λ r → r ℚ.· gap) (ℚ.·Comm bound-n inv-gap)

    inv-gap-cancel :
      (radius q ℚ.· inv-gap ℚ.+ Rational.1ℚ) ≡ inv-gap
    inv-gap-cancel =
      binomialGeometricGap-inv-cancel q q<1

    product≤product :
      (radius q ℚ.· inv-gap ℚ.+ Rational.1ℚ) ℚ.· bound-n ℚ.· gap
        ℚOrder.≤
      inv-gap ℚ.· bound-n ℚ.· gap
    product≤product =
      subst
        (λ r → r ℚ.· bound-n ℚ.· gap ℚOrder.≤
          inv-gap ℚ.· bound-n ℚ.· gap)
        (sym inv-gap-cancel)
        (Rational.≤-refl (inv-gap ℚ.· bound-n ℚ.· gap))
