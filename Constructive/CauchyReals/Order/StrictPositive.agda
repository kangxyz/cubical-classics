{-# OPTIONS --safe #-}

module Constructive.CauchyReals.Order.StrictPositive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as Empty using (⊥; isProp⊥)
open import Cubical.Data.Int.Order using (zero-<sucPos)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)
open import Cubical.Data.Sum as Sum using (_⊎_; inl; inr; isProp⊎)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Nullary

open import Constructive.CauchyReals.Arithmetic.Addition
open import Constructive.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.CauchyReals.Arithmetic.Base
open import Constructive.CauchyReals.Arithmetic.Negation
open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Order.Bounds
open import Constructive.CauchyReals.Order.Base
open import Constructive.CauchyReals.Order.Properties
open import Constructive.CauchyReals.Order.Rational
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


infix 4 _<ᶜ_ _>ᶜ_ _#ᶜ_


PositiveSepᶜ : ℝᶜ → Type₀
PositiveSepᶜ x =
  ∥ Σ[ ε ∈ ℚ⁺ ] rational (radius ε) ≤ᶜ x ∥₁


isPropPositiveSepᶜ : (x : ℝᶜ) → isProp (PositiveSepᶜ x)
isPropPositiveSepᶜ x =
  squash₁


positiveSepᶜ→nonnegative :
  {x : ℝᶜ} →
  PositiveSepᶜ x →
  0ᶜ ≤ᶜ x
positiveSepᶜ→nonnegative {x = x} =
  Prop.rec (isProp≤ᶜ 0ᶜ x) step
  where
  step : Σ[ ε ∈ ℚ⁺ ] rational (radius ε) ≤ᶜ x → 0ᶜ ≤ᶜ x
  step (ε , ε≤x) =
    ≤ᶜ-trans
      {x = 0ᶜ}
      {y = rational (radius ε)}
      {z = x}
      (≤ℚ→rational≤ᶜ
        {q = 0ℚ}
        {r = radius ε}
        (ℚOrder.<Weaken≤ 0ℚ (radius ε) (ε .snd)))
      ε≤x


positiveSepᶜ-not-zero : ¬ PositiveSepᶜ 0ᶜ
positiveSepᶜ-not-zero =
  Prop.rec isProp⊥ λ (ε , ε≤0) → positive-rational-not≤0ᶜ ε ε≤0


_<ᶜ_ : ℝᶜ → ℝᶜ → Type₀
x <ᶜ y =
  PositiveSepᶜ (y +ᶜ (-ᶜ x))


_>ᶜ_ : ℝᶜ → ℝᶜ → Type₀
x >ᶜ y = y <ᶜ x


isProp<ᶜ : (x y : ℝᶜ) → isProp (x <ᶜ y)
isProp<ᶜ x y =
  isPropPositiveSepᶜ (y +ᶜ (-ᶜ x))


diffᶜ-translate-right :
  (x y z : ℝᶜ) →
  (y +ᶜ z) +ᶜ (-ᶜ (x +ᶜ z)) ≡ y +ᶜ (-ᶜ x)
diffᶜ-translate-right x y z =
  cong ((y +ᶜ z) +ᶜ_) (neg-add x z) ∙
  add-interchange y z (-ᶜ x) (-ᶜ z) ∙
  cong ((y +ᶜ (-ᶜ x)) +ᶜ_) (add-inverse-right z) ∙
  add-zero-right (y +ᶜ (-ᶜ x))


diffᶜ-sum :
  (x y z : ℝᶜ) →
  (y +ᶜ (-ᶜ x)) +ᶜ (z +ᶜ (-ᶜ y)) ≡ z +ᶜ (-ᶜ x)
diffᶜ-sum x y z =
  add-interchange y (-ᶜ x) z (-ᶜ y) ∙
  cong (_+ᶜ ((-ᶜ x) +ᶜ (-ᶜ y))) (add-comm y z) ∙
  sym (add-interchange z (-ᶜ x) y (-ᶜ y)) ∙
  cong ((z +ᶜ (-ᶜ x)) +ᶜ_) (add-inverse-right y) ∙
  add-zero-right (z +ᶜ (-ᶜ x))


<ᶜ-irrefl : (x : ℝᶜ) → ¬ (x <ᶜ x)
<ᶜ-irrefl x x<x =
  positiveSepᶜ-not-zero
    (subst PositiveSepᶜ (add-inverse-right x) x<x)


<ᶜ→≤ᶜ : {x y : ℝᶜ} → x <ᶜ y → x ≤ᶜ y
<ᶜ→≤ᶜ {x = x} {y = y} x<y =
  subst2 _≤ᶜ_
    (add-zero-left x)
    (minus-plus-cancel-right y x)
    (addᶜ-pres≤ᶜ-right
      {x = 0ᶜ}
      {y = y +ᶜ (-ᶜ x)}
      x
      (positiveSepᶜ→nonnegative {x = y +ᶜ (-ᶜ x)} x<y))


diffᶜ-nonnegative→≤ᶜ :
  {x y : ℝᶜ} →
  0ᶜ ≤ᶜ (y +ᶜ (-ᶜ x)) →
  x ≤ᶜ y
diffᶜ-nonnegative→≤ᶜ {x = x} {y = y} 0≤y-x =
  subst2 _≤ᶜ_
    (add-zero-left x)
    (minus-plus-cancel-right y x)
    (addᶜ-pres≤ᶜ-right
      {x = 0ᶜ}
      {y = y +ᶜ (-ᶜ x)}
      x
      0≤y-x)


<ℚ→<ᶜ :
  {q r : ℚ} →
  q ℚOrder.< r →
  rational q <ᶜ rational r
<ℚ→<ᶜ {q = q} {r = r} q<r =
  ∣ (r ℚ.- q , Rational.diff-positive {p = q} {q = r} q<r) ,
    ≤ᶜ-refl (rational (r ℚ.- q))
  ∣₁


close-rational-positive :
  (x : ℝᶜ) (q : ℚ) (δ ε : ℚ⁺) →
  δ <⁺ ε →
  radius ε ℚOrder.< q →
  x ∼[ δ ] rational q →
  PositiveSepᶜ x
close-rational-positive x q δ ε δ<ε ε<q x∼q =
  ∣ (q ℚ.- radius ε , Rational.diff-positive {p = radius ε} {q = q} ε<q) ,
    close-rational-lower-bound x q δ ε δ<ε x∼q
  ∣₁


≤ᶜ-add :
  {a b c d : ℝᶜ} →
  a ≤ᶜ b →
  c ≤ᶜ d →
  (a +ᶜ c) ≤ᶜ (b +ᶜ d)
≤ᶜ-add {a = a} {b = b} {c = c} {d = d} a≤b c≤d =
  ≤ᶜ-trans
    {x = a +ᶜ c}
    {y = b +ᶜ c}
    {z = b +ᶜ d}
    (addᶜ-pres≤ᶜ-right {x = a} {y = b} c a≤b)
    (addᶜ-pres≤ᶜ-left {x = c} {y = d} b c≤d)


positiveSepᶜ-add :
  {x y : ℝᶜ} →
  PositiveSepᶜ x →
  PositiveSepᶜ y →
  PositiveSepᶜ (x +ᶜ y)
positiveSepᶜ-add {x = x} {y = y} =
  Prop.rec2 squash₁ step
  where
  step :
    Σ[ ε ∈ ℚ⁺ ] rational (radius ε) ≤ᶜ x →
    Σ[ δ ∈ ℚ⁺ ] rational (radius δ) ≤ᶜ y →
    PositiveSepᶜ (x +ᶜ y)
  step (ε , ε≤x) (δ , δ≤y) =
    ∣ ε +⁺ δ ,
      subst
        (λ w → w ≤ᶜ (x +ᶜ y))
        (sym (add-rational (radius ε) (radius δ)))
        (≤ᶜ-add
          {a = rational (radius ε)}
          {b = x}
          {c = rational (radius δ)}
          {d = y}
          ε≤x
          δ≤y)
    ∣₁


positiveSepᶜ-add-nonnegative :
  {x y : ℝᶜ} →
  PositiveSepᶜ x →
  0ᶜ ≤ᶜ y →
  PositiveSepᶜ (x +ᶜ y)
positiveSepᶜ-add-nonnegative {x = x} {y = y} =
  Prop.rec (isProp→ squash₁) step
  where
  step :
    Σ[ ε ∈ ℚ⁺ ] rational (radius ε) ≤ᶜ x →
    0ᶜ ≤ᶜ y →
    PositiveSepᶜ (x +ᶜ y)
  step (ε , ε≤x) 0≤y =
    ∣ ε ,
      subst
        (λ w → w ≤ᶜ (x +ᶜ y))
        (add-zero-right (rational (radius ε)))
        (≤ᶜ-add
          {a = rational (radius ε)}
          {b = x}
          {c = 0ᶜ}
          {d = y}
          ε≤x
          0≤y)
    ∣₁


nonnegative-positiveSepᶜ-add :
  {x y : ℝᶜ} →
  0ᶜ ≤ᶜ x →
  PositiveSepᶜ y →
  PositiveSepᶜ (x +ᶜ y)
nonnegative-positiveSepᶜ-add {x = x} {y = y} 0≤x pos-y =
  subst PositiveSepᶜ
    (add-comm y x)
    (positiveSepᶜ-add-nonnegative {x = y} {y = x} pos-y 0≤x)


≤ᶜ→diffᶜ-nonnegative :
  {x y : ℝᶜ} →
  x ≤ᶜ y →
  0ᶜ ≤ᶜ (y +ᶜ (-ᶜ x))
≤ᶜ→diffᶜ-nonnegative {x = x} {y = y} x≤y =
  subst
    (λ w → w ≤ᶜ (y +ᶜ (-ᶜ x)))
    (add-inverse-right x)
    (addᶜ-pres≤ᶜ-right {x = x} {y = y} (-ᶜ x) x≤y)


negᶜ-pres≤ᶜ :
  {x y : ℝᶜ} →
  x ≤ᶜ y →
  (-ᶜ y) ≤ᶜ (-ᶜ x)
negᶜ-pres≤ᶜ {x = x} {y = y} x≤y =
  diffᶜ-nonnegative→≤ᶜ {x = -ᶜ y} {y = -ᶜ x}
      (subst
        (0ᶜ ≤ᶜ_)
      (add-comm y (-ᶜ x) ∙
       cong ((-ᶜ x) +ᶜ_) (sym (neg-involutive y)))
      (≤ᶜ→diffᶜ-nonnegative {x = x} {y = y} x≤y))


negᶜ-reverse<ᶜ :
  {x y : ℝᶜ} →
  x <ᶜ y →
  (-ᶜ y) <ᶜ (-ᶜ x)
negᶜ-reverse<ᶜ {x = x} {y = y} x<y =
  subst PositiveSepᶜ
    (add-comm y (-ᶜ x) ∙
     cong ((-ᶜ x) +ᶜ_) (sym (neg-involutive y)))
    x<y


negativeᶜ→positive-negᶜ :
  (x : ℝᶜ) →
  x <ᶜ 0ᶜ →
  0ᶜ <ᶜ (-ᶜ x)
negativeᶜ→positive-negᶜ x x<0 =
  subst
    (λ w → w <ᶜ (-ᶜ x))
    negative-zeroᶜ
    (negᶜ-reverse<ᶜ {x = x} {y = 0ᶜ} x<0)
  where
  negative-zeroᶜ : -ᶜ 0ᶜ ≡ 0ᶜ
  negative-zeroᶜ =
    inverse-unique-right 0ᶜ 0ᶜ (add-zero-right 0ᶜ)


positive-negᶜ→negativeᶜ :
  (x : ℝᶜ) →
  0ᶜ <ᶜ (-ᶜ x) →
  x <ᶜ 0ᶜ
positive-negᶜ→negativeᶜ x 0<-x =
  subst2 _<ᶜ_
    (neg-involutive x)
    negative-zeroᶜ
    (negᶜ-reverse<ᶜ {x = 0ᶜ} {y = -ᶜ x} 0<-x)
  where
  negative-zeroᶜ : -ᶜ 0ᶜ ≡ 0ᶜ
  negative-zeroᶜ =
    inverse-unique-right 0ᶜ 0ᶜ (add-zero-right 0ᶜ)


negative-upper-bound→positive-negᶜ :
  (x : ℝᶜ) (ε : ℚ⁺) →
  x ≤ᶜ rational (ℚ.- radius ε) →
  PositiveSepᶜ (-ᶜ x)
negative-upper-bound→positive-negᶜ x ε x≤-ε =
  ∣ ε ,
    subst
      (λ w → w ≤ᶜ (-ᶜ x))
      (cong rational (ℚ.-Invol (radius ε)))
      (negᶜ-pres≤ᶜ {x = x} {y = rational (ℚ.- radius ε)} x≤-ε)
  ∣₁


<ᶜ-trans : {x y z : ℝᶜ} → x <ᶜ y → y <ᶜ z → x <ᶜ z
<ᶜ-trans {x = x} {y = y} {z = z} x<y y<z =
  subst PositiveSepᶜ
    (diffᶜ-sum x y z)
    (positiveSepᶜ-add
      {x = y +ᶜ (-ᶜ x)}
      {y = z +ᶜ (-ᶜ y)}
      x<y
      y<z)


<ᶜ-asym : (x y : ℝᶜ) → x <ᶜ y → ¬ (y <ᶜ x)
<ᶜ-asym x y x<y y<x =
  <ᶜ-irrefl x (<ᶜ-trans {x = x} {y = y} {z = x} x<y y<x)


≤ᶜ→¬>ᶜ : (x y : ℝᶜ) → x ≤ᶜ y → ¬ (y <ᶜ x)
≤ᶜ→¬>ᶜ x y x≤y y<x =
  <ᶜ-irrefl y
    (subst
      (λ z → y <ᶜ z)
      (sym
        (≤ᶜ-antisym
          {x = y}
          {y = x}
          (<ᶜ→≤ᶜ {x = y} {y = x} y<x)
          x≤y))
      y<x)


<ᶜ-≤ᶜ-trans :
  (x y z : ℝᶜ) →
  x <ᶜ y →
  y ≤ᶜ z →
  x <ᶜ z
<ᶜ-≤ᶜ-trans x y z x<y y≤z =
  subst PositiveSepᶜ
    (diffᶜ-sum x y z)
    (positiveSepᶜ-add-nonnegative
      {x = y +ᶜ (-ᶜ x)}
      {y = z +ᶜ (-ᶜ y)}
      x<y
      (≤ᶜ→diffᶜ-nonnegative {x = y} {y = z} y≤z))


≤ᶜ-<ᶜ-trans :
  (x y z : ℝᶜ) →
  x ≤ᶜ y →
  y <ᶜ z →
  x <ᶜ z
≤ᶜ-<ᶜ-trans x y z x≤y y<z =
  subst PositiveSepᶜ
    (diffᶜ-sum x y z)
    (nonnegative-positiveSepᶜ-add
      {x = y +ᶜ (-ᶜ x)}
      {y = z +ᶜ (-ᶜ y)}
      (≤ᶜ→diffᶜ-nonnegative {x = x} {y = y} x≤y)
      y<z)


addᶜ-pres<ᶜ-right :
  {x y : ℝᶜ} →
  (z : ℝᶜ) →
  x <ᶜ y →
  (x +ᶜ z) <ᶜ (y +ᶜ z)
addᶜ-pres<ᶜ-right {x = x} {y = y} z x<y =
  subst PositiveSepᶜ
    (sym (diffᶜ-translate-right x y z))
    x<y


addᶜ-reflect<ᶜ-right :
  {x y : ℝᶜ} →
  (z : ℝᶜ) →
  (x +ᶜ z) <ᶜ (y +ᶜ z) →
  x <ᶜ y
addᶜ-reflect<ᶜ-right {x = x} {y = y} z x+z<y+z =
  subst PositiveSepᶜ
    (diffᶜ-translate-right x y z)
    x+z<y+z


addᶜ-pres<ᶜ-left :
  {x y : ℝᶜ} →
  (z : ℝᶜ) →
  x <ᶜ y →
  (z +ᶜ x) <ᶜ (z +ᶜ y)
addᶜ-pres<ᶜ-left {x = x} {y = y} z x<y =
  subst2 _<ᶜ_
    (add-comm x z)
    (add-comm y z)
    (addᶜ-pres<ᶜ-right {x = x} {y = y} z x<y)


addᶜ-reflect<ᶜ-left :
  {x y : ℝᶜ} →
  (z : ℝᶜ) →
  (z +ᶜ x) <ᶜ (z +ᶜ y) →
  x <ᶜ y
addᶜ-reflect<ᶜ-left {x = x} {y = y} z z+x<z+y =
  addᶜ-reflect<ᶜ-right {x = x} {y = y} z
    (subst2 _<ᶜ_
      (add-comm z x)
      (add-comm z y)
      z+x<z+y)


diff≤half-gap→<ᶜ :
  (x y z : ℝᶜ) (ε : ℚ⁺) →
  rational (radius ε) ≤ᶜ (y +ᶜ (-ᶜ x)) →
  (z +ᶜ (-ᶜ x)) ≤ᶜ rational (radius (half⁺ ε)) →
  z <ᶜ y
diff≤half-gap→<ᶜ x y z ε ε≤y-x z-x≤half =
  ≤ᶜ-<ᶜ-trans z (x +ᶜ rational (radius halfε)) y z≤x+half x+half<y
  where
  halfε : ℚ⁺
  halfε = half⁺ ε

  half<εᶜ : rational (radius halfε) <ᶜ rational (radius ε)
  half<εᶜ =
    <ℚ→<ᶜ {q = radius halfε} {r = radius ε} (half< ε)

  half<y-x : rational (radius halfε) <ᶜ (y +ᶜ (-ᶜ x))
  half<y-x =
    <ᶜ-≤ᶜ-trans
      (rational (radius halfε))
      (rational (radius ε))
      (y +ᶜ (-ᶜ x))
      half<εᶜ
      ε≤y-x

  x+half<y : (x +ᶜ rational (radius halfε)) <ᶜ y
  x+half<y =
    subst2 _<ᶜ_
      (add-comm (rational (radius halfε)) x)
      (minus-plus-cancel-right y x)
      (addᶜ-pres<ᶜ-right
        {x = rational (radius halfε)}
        {y = y +ᶜ (-ᶜ x)}
        x
        half<y-x)

  z≤x+half : z ≤ᶜ (x +ᶜ rational (radius halfε))
  z≤x+half =
    subst2 _≤ᶜ_
      (minus-plus-cancel-right z x)
      (add-comm (rational (radius halfε)) x)
      (addᶜ-pres≤ᶜ-right
        {x = z +ᶜ (-ᶜ x)}
        {y = rational (radius halfε)}
        x
        z-x≤half)


_#ᶜ_ : ℝᶜ → ℝᶜ → Type₀
x #ᶜ y = (x <ᶜ y) ⊎ (y <ᶜ x)


isProp#ᶜ : (x y : ℝᶜ) → isProp (x #ᶜ y)
isProp#ᶜ x y = isProp⊎ (isProp<ᶜ x y) (isProp<ᶜ y x) (<ᶜ-asym x y)


#ᶜ-sym : {x y : ℝᶜ} → x #ᶜ y → y #ᶜ x
#ᶜ-sym (inl x<y) = inr x<y
#ᶜ-sym (inr y<x) = inl y<x


<ᶜ-rational→<ℚ :
  {q r : ℚ} →
  rational q <ᶜ rational r →
  q ℚOrder.< r
<ᶜ-rational→<ℚ {q = q} {r = r} =
  Prop.rec (ℚOrder.isProp< q r) step
  where
  step :
    Σ[ ε ∈ ℚ⁺ ] rational (radius ε) ≤ᶜ rational (r ℚ.- q) →
    q ℚOrder.< r
  step (ε , ε≤r-q) =
    subst (q ℚOrder.<_)
      (Rational.p+[q-p]≡q q r)
      (Rational.q<q+positive q (r ℚ.- q) 0<r-q)
    where
    ε≤r-qℚ : radius ε ℚOrder.≤ r ℚ.- q
    ε≤r-qℚ =
      rational≤ᶜ→≤ℚ ε≤r-q

    0<r-q : 0ℚ ℚOrder.< r ℚ.- q
    0<r-q =
      Rational.<≤-trans
        {p = 0ℚ}
        {q = radius ε}
        {r = r ℚ.- q}
        (ε .snd)
        ε≤r-qℚ


0ᶜ<1ᶜ : 0ᶜ <ᶜ 1ᶜ
0ᶜ<1ᶜ =
  <ℚ→<ᶜ {q = 0ℚ} {r = 1ℚ} zero-<sucPos
