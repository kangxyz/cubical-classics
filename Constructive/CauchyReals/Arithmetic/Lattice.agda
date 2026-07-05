{-

Lattice operations on HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Arithmetic.Lattice where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness.Properties
open import Constructive.CauchyReals.Continuity
open import Constructive.CauchyReals.Extension.Properties
import Constructive.Rationals as Rational


private
  q<ε+q : (q : ℚ) (ε : ℚ⁺) → q ℚOrder.< radius ε ℚ.+ q
  q<ε+q q ε =
    subst
      (λ r → q ℚOrder.< r)
      (ℚ.+Comm q (radius ε))
      (Rational.q<q+positive q (radius ε) (ε .snd))

  min-right-path :
    (q r : ℚ) →
    r ℚOrder.≤ q →
    ℚ.min q r ≡ r
  min-right-path q r r≤q =
    ℚ.minComm q r ∙
    ℚOrder.≤→min r q r≤q

  max-left-path :
    (q r : ℚ) →
    r ℚOrder.≤ q →
    ℚ.max q r ≡ q
  max-left-path q r r≤q =
    ℚ.maxComm q r ∙
    ℚOrder.≤→max r q r≤q

  min-left-upper :
    (q r s : ℚ) (ε : ℚ⁺) →
    Closeℚ q ε r →
    ℚ.min q s ℚOrder.< radius ε ℚ.+ ℚ.min r s
  min-left-upper q r s ε q∼r with r ℚOrder.≟ s
  ... | ℚOrder.lt r<s =
    subst
      (λ t → ℚ.min q s ℚOrder.< radius ε ℚ.+ t)
      (sym (ℚOrder.≤→min r s (ℚOrder.<Weaken≤ r s r<s)))
      (ℚOrder.isTrans≤<
        (ℚ.min q s)
        q
        (radius ε ℚ.+ r)
        (ℚOrder.min≤ q s)
        (Rational.diff<→right+< q (radius ε) r (q∼r .fst)))
  ... | ℚOrder.eq r≡s =
    subst
      (λ t → ℚ.min q s ℚOrder.< radius ε ℚ.+ t)
      (sym (ℚOrder.≤→min r s (ℚOrder.≡Weaken≤ r s r≡s)))
      (ℚOrder.isTrans≤<
        (ℚ.min q s)
        q
        (radius ε ℚ.+ r)
        (ℚOrder.min≤ q s)
        (Rational.diff<→right+< q (radius ε) r (q∼r .fst)))
  ... | ℚOrder.gt s<r =
    subst
      (λ t → ℚ.min q s ℚOrder.< radius ε ℚ.+ t)
      (sym (min-right-path r s (ℚOrder.<Weaken≤ s r s<r)))
      (ℚOrder.isTrans≤<
        (ℚ.min q s)
        s
        (radius ε ℚ.+ s)
        (Rational.min≤r q s)
        (q<ε+q s ε))

  rational-close-min-left :
    (q r s : ℚ) (ε : ℚ⁺) →
    Closeℚ q ε r →
    Closeℚ (ℚ.min q s) ε (ℚ.min r s)
  rational-close-min-left q r s ε q∼r =
    Rational.<+→diff<
      (ℚ.min q s)
      (radius ε)
      (ℚ.min r s)
      (min-left-upper q r s ε q∼r) ,
    Rational.<+→diff<
      (ℚ.min r s)
      (radius ε)
      (ℚ.min q s)
      (min-left-upper r q s ε (rational-close-sym q r ε q∼r))

  rational-close-min-right :
    (q r s : ℚ) (ε : ℚ⁺) →
    Closeℚ r ε s →
    Closeℚ (ℚ.min q r) ε (ℚ.min q s)
  rational-close-min-right q r s ε r∼s =
    subst2
      (λ a b → Closeℚ a ε b)
      (ℚ.minComm r q)
      (ℚ.minComm s q)
      (rational-close-min-left r s q ε r∼s)

  max-left-upper :
    (q r s : ℚ) (ε : ℚ⁺) →
    Closeℚ q ε r →
    ℚ.max q s ℚOrder.< radius ε ℚ.+ ℚ.max r s
  max-left-upper q r s ε q∼r =
    Rational.max<
      {r = q}
      {s = s}
      {q = radius ε ℚ.+ ℚ.max r s}
      q<ε+max
      s<ε+max
    where
    q<ε+r : q ℚOrder.< radius ε ℚ.+ r
    q<ε+r =
      Rational.diff<→right+< q (radius ε) r (q∼r .fst)

    ε+r≤ε+max : radius ε ℚ.+ r ℚOrder.≤ radius ε ℚ.+ ℚ.max r s
    ε+r≤ε+max =
      ℚOrder.≤-o+ r (ℚ.max r s) (radius ε) (ℚOrder.≤max r s)

    q<ε+max : q ℚOrder.< radius ε ℚ.+ ℚ.max r s
    q<ε+max =
      ℚOrder.isTrans<≤
        q
        (radius ε ℚ.+ r)
        (radius ε ℚ.+ ℚ.max r s)
        q<ε+r
        ε+r≤ε+max

    s≤max : s ℚOrder.≤ ℚ.max r s
    s≤max =
      Rational.≤max-r r s

    s<ε+max : s ℚOrder.< radius ε ℚ.+ ℚ.max r s
    s<ε+max =
      ℚOrder.isTrans≤<
        s
        (ℚ.max r s)
        (radius ε ℚ.+ ℚ.max r s)
        s≤max
        (q<ε+q (ℚ.max r s) ε)

  rational-close-max-left :
    (q r s : ℚ) (ε : ℚ⁺) →
    Closeℚ q ε r →
    Closeℚ (ℚ.max q s) ε (ℚ.max r s)
  rational-close-max-left q r s ε q∼r =
    Rational.<+→diff<
      (ℚ.max q s)
      (radius ε)
      (ℚ.max r s)
      (max-left-upper q r s ε q∼r) ,
    Rational.<+→diff<
      (ℚ.max r s)
      (radius ε)
      (ℚ.max q s)
      (max-left-upper r q s ε (rational-close-sym q r ε q∼r))

  rational-close-max-right :
    (q r s : ℚ) (ε : ℚ⁺) →
    Closeℚ r ε s →
    Closeℚ (ℚ.max q r) ε (ℚ.max q s)
  rational-close-max-right q r s ε r∼s =
    subst2
      (λ a b → Closeℚ a ε b)
      (ℚ.maxComm r q)
      (ℚ.maxComm s q)
      (rational-close-max-left r s q ε r∼s)

  rational-min rational-max : ℚ → ℚ → ℝᶜ
  rational-min q r =
    rational (ℚ.min q r)
  rational-max q r =
    rational (ℚ.max q r)

  min-left-ne : IsBinaryRationalNonexpandingLeft rational-min
  min-left-ne q r s ε q∼r =
    rational-rational-close
      (ℚ.min q s)
      (ℚ.min r s)
      ε
      (rational-close-min-left q r s ε q∼r)

  min-right-ne : IsBinaryRationalNonexpandingRight rational-min
  min-right-ne q r s ε r∼s =
    rational-rational-close
      (ℚ.min q r)
      (ℚ.min q s)
      ε
      (rational-close-min-right q r s ε r∼s)

  max-left-ne : IsBinaryRationalNonexpandingLeft rational-max
  max-left-ne q r s ε q∼r =
    rational-rational-close
      (ℚ.max q s)
      (ℚ.max r s)
      ε
      (rational-close-max-left q r s ε q∼r)

  max-right-ne : IsBinaryRationalNonexpandingRight rational-max
  max-right-ne q r s ε r∼s =
    rational-rational-close
      (ℚ.max q r)
      (ℚ.max q s)
      ε
      (rational-close-max-right q r s ε r∼s)


infixl 7 _⊓ᶜ_
infixl 6 _⊔ᶜ_

_⊓ᶜ_ : ℝᶜ → ℝᶜ → ℝᶜ
_⊓ᶜ_ =
  extendBinaryNonexpanding rational-min min-left-ne min-right-ne


_⊔ᶜ_ : ℝᶜ → ℝᶜ → ℝᶜ
_⊔ᶜ_ =
  extendBinaryNonexpanding rational-max max-left-ne max-right-ne


min-rational :
  (q r : ℚ) →
  rational q ⊓ᶜ rational r ≡ rational (ℚ.min q r)
min-rational q r =
  refl


min-rational-left :
  (q : ℚ) (y : ℝᶜ) →
  rational q ⊓ᶜ y ≡
  extendNonexpanding (rational-min q) (min-right-ne q) y
min-rational-left q y =
  refl


min-rational-right :
  (x : ℝᶜ) (r : ℚ) →
  x ⊓ᶜ rational r ≡
  extendNonexpanding
    (λ q → rational-min q r)
    (λ q s ε q∼s → min-left-ne q s r ε q∼s)
    x
min-rational-right =
  extendBinaryNonexpanding-rational-right
    rational-min
    min-left-ne
    min-right-ne


max-rational :
  (q r : ℚ) →
  rational q ⊔ᶜ rational r ≡ rational (ℚ.max q r)
max-rational q r =
  refl


max-rational-left :
  (q : ℚ) (y : ℝᶜ) →
  rational q ⊔ᶜ y ≡
  extendNonexpanding (rational-max q) (max-right-ne q) y
max-rational-left q y =
  refl


max-rational-right :
  (x : ℝᶜ) (r : ℚ) →
  x ⊔ᶜ rational r ≡
  extendNonexpanding
    (λ q → rational-max q r)
    (λ q s ε q∼s → max-left-ne q s r ε q∼s)
    x
max-rational-right =
  extendBinaryNonexpanding-rational-right
    rational-max
    max-left-ne
    max-right-ne


min-close-left :
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  (z : ℝᶜ) →
  (x ⊓ᶜ z) ∼[ ε ] (y ⊓ᶜ z)
min-close-left =
  extendBinaryNonexpanding-close-left
    rational-min
    min-left-ne
    min-right-ne


min-close-right :
  (x : ℝᶜ) →
  {y z : ℝᶜ} {ε : ℚ⁺} →
  y ∼[ ε ] z →
  (x ⊓ᶜ y) ∼[ ε ] (x ⊓ᶜ z)
min-close-right =
  extendBinaryNonexpanding-close-right
    rational-min
    min-left-ne
    min-right-ne


min-close :
  {x y z w : ℝᶜ} {η ε : ℚ⁺} →
  x ∼[ η ] y →
  z ∼[ ε ] w →
  (x ⊓ᶜ z) ∼[ η +⁺ ε ] (y ⊓ᶜ w)
min-close =
  extendBinaryNonexpanding-close
    rational-min
    min-left-ne
    min-right-ne


max-close-left :
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  (z : ℝᶜ) →
  (x ⊔ᶜ z) ∼[ ε ] (y ⊔ᶜ z)
max-close-left =
  extendBinaryNonexpanding-close-left
    rational-max
    max-left-ne
    max-right-ne


max-close-right :
  (x : ℝᶜ) →
  {y z : ℝᶜ} {ε : ℚ⁺} →
  y ∼[ ε ] z →
  (x ⊔ᶜ y) ∼[ ε ] (x ⊔ᶜ z)
max-close-right =
  extendBinaryNonexpanding-close-right
    rational-max
    max-left-ne
    max-right-ne


max-close :
  {x y z w : ℝᶜ} {η ε : ℚ⁺} →
  x ∼[ η ] y →
  z ∼[ ε ] w →
  (x ⊔ᶜ z) ∼[ η +⁺ ε ] (y ⊔ᶜ w)
max-close =
  extendBinaryNonexpanding-close
    rational-max
    max-left-ne
    max-right-ne


min-nonexpanding-left :
  (z : ℝᶜ) →
  IsNonexpanding (λ x → x ⊓ᶜ z)
min-nonexpanding-left z x∼y =
  min-close-left x∼y z


min-nonexpanding-right :
  (x : ℝᶜ) →
  IsNonexpanding (λ y → x ⊓ᶜ y)
min-nonexpanding-right x =
  min-close-right x


max-nonexpanding-left :
  (z : ℝᶜ) →
  IsNonexpanding (λ x → x ⊔ᶜ z)
max-nonexpanding-left z x∼y =
  max-close-left x∼y z


max-nonexpanding-right :
  (x : ℝᶜ) →
  IsNonexpanding (λ y → x ⊔ᶜ y)
max-nonexpanding-right x =
  max-close-right x


min-continuous-left :
  (z : ℝᶜ) →
  IsContinuous (λ x → x ⊓ᶜ z)
min-continuous-left z =
  nonexpanding→continuous (min-nonexpanding-left z)


min-continuous-right :
  (x : ℝᶜ) →
  IsContinuous (λ y → x ⊓ᶜ y)
min-continuous-right x =
  nonexpanding→continuous (min-nonexpanding-right x)


max-continuous-left :
  (z : ℝᶜ) →
  IsContinuous (λ x → x ⊔ᶜ z)
max-continuous-left z =
  nonexpanding→continuous (max-nonexpanding-left z)


max-continuous-right :
  (x : ℝᶜ) →
  IsContinuous (λ y → x ⊔ᶜ y)
max-continuous-right x =
  nonexpanding→continuous (max-nonexpanding-right x)


min-comm-rational-left :
  (q : ℚ) (y : ℝᶜ) →
  rational q ⊓ᶜ y ≡ y ⊓ᶜ rational q
min-comm-rational-left q =
  nonexpanding-equal
    (λ y → rational q ⊓ᶜ y)
    (λ y → y ⊓ᶜ rational q)
    (min-nonexpanding-right (rational q))
    (min-nonexpanding-left (rational q))
    (λ r → cong rational (ℚ.minComm q r))


min-comm :
  (x y : ℝᶜ) →
  x ⊓ᶜ y ≡ y ⊓ᶜ x
min-comm x y =
  nonexpanding-equal
    (λ z → z ⊓ᶜ y)
    (λ z → y ⊓ᶜ z)
    (min-nonexpanding-left y)
    (min-nonexpanding-right y)
    (λ q → min-comm-rational-left q y)
    x


max-comm-rational-left :
  (q : ℚ) (y : ℝᶜ) →
  rational q ⊔ᶜ y ≡ y ⊔ᶜ rational q
max-comm-rational-left q =
  nonexpanding-equal
    (λ y → rational q ⊔ᶜ y)
    (λ y → y ⊔ᶜ rational q)
    (max-nonexpanding-right (rational q))
    (max-nonexpanding-left (rational q))
    (λ r → cong rational (ℚ.maxComm q r))


max-comm :
  (x y : ℝᶜ) →
  x ⊔ᶜ y ≡ y ⊔ᶜ x
max-comm x y =
  nonexpanding-equal
    (λ z → z ⊔ᶜ y)
    (λ z → y ⊔ᶜ z)
    (max-nonexpanding-left y)
    (max-nonexpanding-right y)
    (λ q → max-comm-rational-left q y)
    x


min-assoc-rational-rational-left :
  (q r : ℚ) (z : ℝᶜ) →
  rational q ⊓ᶜ (rational r ⊓ᶜ z) ≡
  (rational q ⊓ᶜ rational r) ⊓ᶜ z
min-assoc-rational-rational-left q r =
  nonexpanding-equal
    (λ z → rational q ⊓ᶜ (rational r ⊓ᶜ z))
    (λ z → (rational q ⊓ᶜ rational r) ⊓ᶜ z)
    (comp-nonexpanding
      (min-nonexpanding-right (rational q))
      (min-nonexpanding-right (rational r)))
    (min-nonexpanding-right (rational q ⊓ᶜ rational r))
    (λ s → cong rational (ℚ.minAssoc q r s))


min-assoc-rational-left :
  (q : ℚ) (y z : ℝᶜ) →
  rational q ⊓ᶜ (y ⊓ᶜ z) ≡
  (rational q ⊓ᶜ y) ⊓ᶜ z
min-assoc-rational-left q y z =
  nonexpanding-equal
    (λ w → rational q ⊓ᶜ (w ⊓ᶜ z))
    (λ w → (rational q ⊓ᶜ w) ⊓ᶜ z)
    (comp-nonexpanding
      (min-nonexpanding-right (rational q))
      (min-nonexpanding-left z))
    (comp-nonexpanding
      (min-nonexpanding-left z)
      (min-nonexpanding-right (rational q)))
    (λ r → min-assoc-rational-rational-left q r z)
    y


min-assoc :
  (x y z : ℝᶜ) →
  x ⊓ᶜ (y ⊓ᶜ z) ≡ (x ⊓ᶜ y) ⊓ᶜ z
min-assoc x y z =
  nonexpanding-equal
    (λ w → w ⊓ᶜ (y ⊓ᶜ z))
    (λ w → (w ⊓ᶜ y) ⊓ᶜ z)
    (min-nonexpanding-left (y ⊓ᶜ z))
    (comp-nonexpanding
      (min-nonexpanding-left z)
      (min-nonexpanding-left y))
    (λ q → min-assoc-rational-left q y z)
    x


max-assoc-rational-rational-left :
  (q r : ℚ) (z : ℝᶜ) →
  rational q ⊔ᶜ (rational r ⊔ᶜ z) ≡
  (rational q ⊔ᶜ rational r) ⊔ᶜ z
max-assoc-rational-rational-left q r =
  nonexpanding-equal
    (λ z → rational q ⊔ᶜ (rational r ⊔ᶜ z))
    (λ z → (rational q ⊔ᶜ rational r) ⊔ᶜ z)
    (comp-nonexpanding
      (max-nonexpanding-right (rational q))
      (max-nonexpanding-right (rational r)))
    (max-nonexpanding-right (rational q ⊔ᶜ rational r))
    (λ s → cong rational (ℚ.maxAssoc q r s))


max-assoc-rational-left :
  (q : ℚ) (y z : ℝᶜ) →
  rational q ⊔ᶜ (y ⊔ᶜ z) ≡
  (rational q ⊔ᶜ y) ⊔ᶜ z
max-assoc-rational-left q y z =
  nonexpanding-equal
    (λ w → rational q ⊔ᶜ (w ⊔ᶜ z))
    (λ w → (rational q ⊔ᶜ w) ⊔ᶜ z)
    (comp-nonexpanding
      (max-nonexpanding-right (rational q))
      (max-nonexpanding-left z))
    (comp-nonexpanding
      (max-nonexpanding-left z)
      (max-nonexpanding-right (rational q)))
    (λ r → max-assoc-rational-rational-left q r z)
    y


max-assoc :
  (x y z : ℝᶜ) →
  x ⊔ᶜ (y ⊔ᶜ z) ≡ (x ⊔ᶜ y) ⊔ᶜ z
max-assoc x y z =
  nonexpanding-equal
    (λ w → w ⊔ᶜ (y ⊔ᶜ z))
    (λ w → (w ⊔ᶜ y) ⊔ᶜ z)
    (max-nonexpanding-left (y ⊔ᶜ z))
    (comp-nonexpanding
      (max-nonexpanding-left z)
      (max-nonexpanding-left y))
    (λ q → max-assoc-rational-left q y z)
    x


min-diagonal-continuous :
  IsContinuous (λ x → x ⊓ᶜ x)
min-diagonal-continuous ε =
  δ , closeAt
  where
  δ : ℚ⁺
  δ = half⁺ ε

  closeAt :
    {x y : ℝᶜ} →
    x ∼[ δ ] y →
    (x ⊓ᶜ x) ∼[ ε ] (y ⊓ᶜ y)
  closeAt {x = x} {y = y} x∼y =
    subst
      (λ ρ → (x ⊓ᶜ x) ∼[ ρ ] (y ⊓ᶜ y))
      (half⁺+half⁺≡ ε)
      (min-close x∼y x∼y)


max-diagonal-continuous :
  IsContinuous (λ x → x ⊔ᶜ x)
max-diagonal-continuous ε =
  δ , closeAt
  where
  δ : ℚ⁺
  δ = half⁺ ε

  closeAt :
    {x y : ℝᶜ} →
    x ∼[ δ ] y →
    (x ⊔ᶜ x) ∼[ ε ] (y ⊔ᶜ y)
  closeAt {x = x} {y = y} x∼y =
    subst
      (λ ρ → (x ⊔ᶜ x) ∼[ ρ ] (y ⊔ᶜ y))
      (half⁺+half⁺≡ ε)
      (max-close x∼y x∼y)


min-idem :
  (x : ℝᶜ) →
  x ⊓ᶜ x ≡ x
min-idem =
  continuous-equal
    (λ x → x ⊓ᶜ x)
    (λ x → x)
    min-diagonal-continuous
    (nonexpanding→continuous id-nonexpanding)
    (λ q → cong rational (ℚ.minIdem q))


max-idem :
  (x : ℝᶜ) →
  x ⊔ᶜ x ≡ x
max-idem =
  continuous-equal
    (λ x → x ⊔ᶜ x)
    (λ x → x)
    max-diagonal-continuous
    (nonexpanding→continuous id-nonexpanding)
    (λ q → cong rational (ℚ.maxIdem q))


min-absorb-max-rational-left :
  (q : ℚ) (y : ℝᶜ) →
  rational q ⊓ᶜ (rational q ⊔ᶜ y) ≡ rational q
min-absorb-max-rational-left q =
  nonexpanding-equal
    (λ y → rational q ⊓ᶜ (rational q ⊔ᶜ y))
    (λ _ → rational q)
    (comp-nonexpanding
      (min-nonexpanding-right (rational q))
      (max-nonexpanding-right (rational q)))
    (constant-nonexpanding (rational q))
    (λ r → cong rational (ℚ.minAbsorbLMax q r))


max-absorb-min-rational-left :
  (q : ℚ) (y : ℝᶜ) →
  rational q ⊔ᶜ (rational q ⊓ᶜ y) ≡ rational q
max-absorb-min-rational-left q =
  nonexpanding-equal
    (λ y → rational q ⊔ᶜ (rational q ⊓ᶜ y))
    (λ _ → rational q)
    (comp-nonexpanding
      (max-nonexpanding-right (rational q))
      (min-nonexpanding-right (rational q)))
    (constant-nonexpanding (rational q))
    (λ r → cong rational (ℚ.maxAbsorbLMin q r))


min-absorb-max-continuous :
  (y : ℝᶜ) →
  IsContinuous (λ x → x ⊓ᶜ (x ⊔ᶜ y))
min-absorb-max-continuous y ε =
  δ , closeAt
  where
  δ : ℚ⁺
  δ = half⁺ ε

  closeAt :
    {x z : ℝᶜ} →
    x ∼[ δ ] z →
    (x ⊓ᶜ (x ⊔ᶜ y)) ∼[ ε ] (z ⊓ᶜ (z ⊔ᶜ y))
  closeAt {x = x} {z = z} x∼z =
    subst
      (λ ρ → (x ⊓ᶜ (x ⊔ᶜ y)) ∼[ ρ ] (z ⊓ᶜ (z ⊔ᶜ y)))
      (half⁺+half⁺≡ ε)
      (min-close x∼z (max-close-left x∼z y))


max-absorb-min-continuous :
  (y : ℝᶜ) →
  IsContinuous (λ x → x ⊔ᶜ (x ⊓ᶜ y))
max-absorb-min-continuous y ε =
  δ , closeAt
  where
  δ : ℚ⁺
  δ = half⁺ ε

  closeAt :
    {x z : ℝᶜ} →
    x ∼[ δ ] z →
    (x ⊔ᶜ (x ⊓ᶜ y)) ∼[ ε ] (z ⊔ᶜ (z ⊓ᶜ y))
  closeAt {x = x} {z = z} x∼z =
    subst
      (λ ρ → (x ⊔ᶜ (x ⊓ᶜ y)) ∼[ ρ ] (z ⊔ᶜ (z ⊓ᶜ y)))
      (half⁺+half⁺≡ ε)
      (max-close x∼z (min-close-left x∼z y))


min-absorb-max :
  (x y : ℝᶜ) →
  x ⊓ᶜ (x ⊔ᶜ y) ≡ x
min-absorb-max x y =
  continuous-equal
    (λ z → z ⊓ᶜ (z ⊔ᶜ y))
    (λ z → z)
    (min-absorb-max-continuous y)
    (nonexpanding→continuous id-nonexpanding)
    (λ q → min-absorb-max-rational-left q y)
    x


max-absorb-min :
  (x y : ℝᶜ) →
  x ⊔ᶜ (x ⊓ᶜ y) ≡ x
max-absorb-min x y =
  continuous-equal
    (λ z → z ⊔ᶜ (z ⊓ᶜ y))
    (λ z → z)
    (max-absorb-min-continuous y)
    (nonexpanding→continuous id-nonexpanding)
    (λ q → max-absorb-min-rational-left q y)
    x
