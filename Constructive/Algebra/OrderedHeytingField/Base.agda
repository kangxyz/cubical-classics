{-

Ordered Heyting fields

This is an ordered commutative ring in which every element apart from zero,
with apartness induced by the strict order, has a multiplicative inverse.
It is separate from Cubical's `Field` interface, which asks for inverses from
mere inequality rather than apartness.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Algebra.OrderedHeytingField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Nullary
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Algebra.OrderedCommRing.Properties

private
  variable
    ℓ ℓ' : Level


module Apartness (𝓡 : OrderedCommRing ℓ ℓ') where
  open OrderedCommRingStr (𝓡 .snd)

  _#_ : 𝓡 .fst → 𝓡 .fst → Type ℓ'
  x # y = (x < y) ⊎ (y < x)

  infix 4 _#_


record IsHeytingFieldOnOrderedCommRing (𝓡 : OrderedCommRing ℓ ℓ') :
    Type (ℓ-max ℓ ℓ') where
  no-eta-equality

  open CommRingStr ((OrderedCommRing→CommRing 𝓡) .snd)
  open Apartness 𝓡

  field
    inv# :
      (x : 𝓡 .fst) →
      x # 0r →
      Σ[ y ∈ 𝓡 .fst ] x · y ≡ 1r


OrderedHeytingField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedHeytingField ℓ ℓ' =
  Σ[ 𝓡 ∈ OrderedCommRing ℓ ℓ' ] IsHeytingFieldOnOrderedCommRing 𝓡


OrderedHeytingField→OrderedCommRing :
  OrderedHeytingField ℓ ℓ' → OrderedCommRing ℓ ℓ'
OrderedHeytingField→OrderedCommRing = fst


OrderedHeytingField→CommRing :
  OrderedHeytingField ℓ ℓ' → CommRing ℓ
OrderedHeytingField→CommRing 𝒦 =
  OrderedCommRing→CommRing (OrderedHeytingField→OrderedCommRing 𝒦)


isPropIsHeytingFieldOnOrderedCommRing :
  (𝓡 : OrderedCommRing ℓ ℓ') →
  isProp (IsHeytingFieldOnOrderedCommRing 𝓡)
isPropIsHeytingFieldOnOrderedCommRing 𝓡 c d i
  .IsHeytingFieldOnOrderedCommRing.inv# x x#0 =
    inv#-path x x#0 i
  where
  open CommRingStr ((OrderedCommRing→CommRing 𝓡) .snd)
  open RingTheory (CommRing→Ring (OrderedCommRing→CommRing 𝓡))

  inv-unique :
    {x y z : 𝓡 .fst} →
    x · y ≡ 1r →
    x · z ≡ 1r →
    y ≡ z
  inv-unique {x = x} {y = y} {z = z} xy≡1 xz≡1 =
    sym (·IdL y)
    ∙ (λ i → xz≡1 (~ i) · y)
    ∙ sym (·Assoc x z y)
    ∙ (λ i → x · ·Comm z y i)
    ∙ ·Assoc x y z
    ∙ (λ i → xy≡1 i · z)
    ∙ ·IdL z

  inv#-path :
    (x : 𝓡 .fst) →
    (x#0 : Apartness._#_ 𝓡 x 0r) →
    c .IsHeytingFieldOnOrderedCommRing.inv# x x#0
      ≡
    d .IsHeytingFieldOnOrderedCommRing.inv# x x#0
  inv#-path x x#0 =
    Σ≡Prop
      (λ y → is-set (x · y) 1r)
      (inv-unique
        (c .IsHeytingFieldOnOrderedCommRing.inv# x x#0 .snd)
        (d .IsHeytingFieldOnOrderedCommRing.inv# x x#0 .snd))


liftPathIsHeytingFieldOnOrderedCommRing :
  {𝓡 𝓡' : OrderedCommRing ℓ ℓ'}(p : 𝓡 ≡ 𝓡')
  (h : IsHeytingFieldOnOrderedCommRing 𝓡)
  (h' : IsHeytingFieldOnOrderedCommRing 𝓡')
  → PathP (λ i → IsHeytingFieldOnOrderedCommRing (p i)) h h'
liftPathIsHeytingFieldOnOrderedCommRing p =
  isProp→PathP (λ i → isPropIsHeytingFieldOnOrderedCommRing (p i))


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (x : 𝓡 .fst) → x + x ≡ (1r + 1r) · x
    helper1 _ = solve! 𝓡

    helper2 : (p q : 𝓡 .fst) → ((p + q) + (1r + 1r) · (- p)) ≡ q - p
    helper2 _ _ = solve! 𝓡

    helper3 : (x y : 𝓡 .fst) → (- x) + (- y) ≡ - (x + y)
    helper3 _ _ = solve! 𝓡


module OrderedHeytingFieldStr (𝒦 : OrderedHeytingField ℓ ℓ') where

  private
    𝓡 = OrderedHeytingField→OrderedCommRing 𝒦
    𝓡ᵣ = OrderedHeytingField→CommRing 𝒦
    K = 𝓡 .fst

    variable
      p q x y : K

  open RingTheory (CommRing→Ring 𝓡ᵣ) public
  open CommRingStr (𝓡ᵣ .snd) public
  open OrderedCommRingTheory 𝓡 public
  open Apartness 𝓡 public
  open IsHeytingFieldOnOrderedCommRing (𝒦 .snd) public
  open Helpers 𝓡ᵣ

  private
    module Ord = OrderedCommRingStr (𝓡 .snd)


  {-

    Apartness from the strict order

  -}

  isProp# : (x y : K) → isProp (x # y)
  isProp# x y = Sum.isProp⊎ isProp< isProp< <-asym

  #-irrefl : (x : K) → ¬ x # x
  #-irrefl x (inl x<x) = <-arefl x<x refl
  #-irrefl x (inr x<x) = <-arefl x<x refl

  #-sym : (x y : K) → x # y → y # x
  #-sym x y (inl x<y) = inr x<y
  #-sym x y (inr y<x) = inl y<x

  #-cotrans :
    (x y z : K) →
    x # y → ∥ (x # z) ⊎ (z # y) ∥₁
  #-cotrans x y z (inl x<y) =
    Prop.rec squash₁
      (λ where
        (inl x<z) → ∣ inl (inl x<z) ∣₁
        (inr z<y) → ∣ inr (inl z<y) ∣₁)
      (Ord.is-weakly-linear x y z x<y)
  #-cotrans x y z (inr y<x) =
    Prop.rec squash₁
      (λ where
        (inl y<z) → ∣ inr (inr y<z) ∣₁
        (inr z<x) → ∣ inl (inr z<x) ∣₁)
      (Ord.is-weakly-linear y x z y<x)

  #→≢ : (x y : K) → x # y → ¬ x ≡ y
  #→≢ x y (inl x<y) x≡y = <-arefl x<y x≡y
  #→≢ x y (inr y<x) x≡y = <-arefl y<x (sym x≡y)

  #→≢0 : (x : K) → x # 0r → ¬ x ≡ 0r
  #→≢0 x x#0 = #→≢ x 0r x#0

  #-tight : (x y : K) → ¬ x # y → x ≡ y
  #-tight x y ¬x#y =
    ≤-asym
      (¬<→≥ {x = y} {y = x} (λ y<x → ¬x#y (inr y<x)))
      (¬<→≥ {x = x} {y = y} (λ x<y → ¬x#y (inl x<y)))

  0#1 : 0r # 1r
  0#1 = inl 1>0

  +-reflects#0 : (x y : K) → x + y # 0r → ∥ (x # 0r) ⊎ (y # 0r) ∥₁
  +-reflects#0 x y (inr 0<x+y) =
    Prop.rec squash₁
      (λ where
        (inl 0<x) → ∣ inl (inr 0<x) ∣₁
        (inr 0<y) → ∣ inr (inr 0<y) ∣₁)
      (Ord.posSum→pos∨pos x y 0<x+y)
  +-reflects#0 x y (inl x+y<0) =
    Prop.rec squash₁
      (λ where
        (inl -x>0) → ∣ inl (inl (-Pos→Neg -x>0)) ∣₁
        (inr -y>0) → ∣ inr (inl (-Pos→Neg -y>0)) ∣₁)
      (Ord.posSum→pos∨pos (- x) (- y)
        (subst (_>0) (sym (helper3 x y)) (-Reverse<0 x+y<0)))


  {-

    Inverse from order apartness

  -}

  ·-rInv# : (x#0 : x # 0r) → x · inv# x x#0 .fst ≡ 1r
  ·-rInv# x#0 = inv# _ x#0 .snd

  ·-lInv# : (x : K) → x # 0r → Σ[ y ∈ K ] y · x ≡ 1r
  ·-lInv# x x#0 =
    x⁻¹ , ·Comm x⁻¹ x ∙ x-right
    where
    x⁻¹ : K
    x⁻¹ = inv# x x#0 .fst

    x-right : x · x⁻¹ ≡ 1r
    x-right = inv# x x#0 .snd

  inv₊ : x > 0r → K
  inv₊ {x = x} x>0 = inv# x (inr x>0) .fst

  ·-rInv₊ : (x>0 : x > 0r) → x · inv₊ x>0 ≡ 1r
  ·-rInv₊ {x = x} x>0 = inv# x (inr x>0) .snd

  ·-lInv₊ : (x>0 : x > 0r) → inv₊ x>0 · x ≡ 1r
  ·-lInv₊ {x = x} x>0 = ·Comm _ x ∙ ·-rInv₊ x>0


  {-

    Division by non-zero natural numbers

  -}

  1/_ : ℕ₊₁ → K
  1/ (1+ n) =
    inv# (ℕ→R-Pos (suc n)) (inr (ℕ→R-PosSuc>0 n)) .fst

  n·1/n≡1 : (n : ℕ₊₁) → ℕ→R-Pos (ℕ₊₁→ℕ n) · 1/ n ≡ 1r
  n·1/n≡1 (1+ n) =
    inv# (ℕ→R-Pos (suc n)) (inr (ℕ→R-PosSuc>0 n)) .snd

  1/n·n≡1 : (n : ℕ₊₁) → 1/ n · ℕ→R-Pos (ℕ₊₁→ℕ n) ≡ 1r
  1/n·n≡1 n = ·Comm _ _ ∙ n·1/n≡1 n

  _/_ : K → ℕ₊₁ → K
  q / n = q · 1/ n

  ·-/-rInv : (q : K)(n : ℕ₊₁) → (q / n) · (ℕ→R-Pos (ℕ₊₁→ℕ n)) ≡ q
  ·-/-rInv q n = sym (·Assoc q _ _) ∙ (λ i → q · 1/n·n≡1 n i) ∙ ·IdR q

  ·-/-lInv : (q : K)(n : ℕ₊₁) → (ℕ→R-Pos (ℕ₊₁→ℕ n)) · (q / n) ≡ q
  ·-/-lInv q n = ·Comm _ (q / n) ∙ ·-/-rInv q n


  {-

    Algebraic midpoint

  -}

  middle : (p q : K) → K
  middle p q = (p + q) / 2

  middle-sym : (p q : K) → middle p q ≡ middle q p
  middle-sym p q i = (+Comm p q i) / 2

  2·middle : (p q : K) → 2r · middle p q ≡ p + q
  2·middle p q = ·-/-lInv (p + q) 2

  x/2+x/2≡x : (x : K) → middle 0r x + middle 0r x ≡ x
  x/2+x/2≡x x = helper1 _ ∙ 2·middle 0r x ∙ +IdL x

  middle-l : (p q : K) → 2r · (middle p q - p) ≡ q - p
  middle-l p q =
    ·DistR+ 2r (middle p q) _
    ∙ (λ i → 2·middle p q i + 2r · (- p))
    ∙ helper2 p q

  middle-r : (p q : K) → 2r · (middle p q - q) ≡ p - q
  middle-r p q =
    (λ i → 2r · (middle-sym p q i - q)) ∙ middle-l q p
