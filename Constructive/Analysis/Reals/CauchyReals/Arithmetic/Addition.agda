{-

Addition on HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Extension
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace


private
  rational-add : ℚ → ℚ → ℝᶜ
  rational-add q r =
    rational (q ℚ.+ r)

  rational-close-translate-left :
    (q r s : ℚ) (ε : ℚ⁺) →
    Closeℚ r ε s →
    Closeℚ (q ℚ.+ r) ε (q ℚ.+ s)
  rational-close-translate-left q r s ε r∼s =
    subst2
      (λ a b → Closeℚ a ε b)
      (ℚ.+Comm r q)
      (ℚ.+Comm s q)
      (rational-close-translate r s q ε r∼s)

  add-left-ne : IsBinaryRationalNonexpandingLeft rational-add
  add-left-ne q r s ε q∼r =
    point-point-close
      (q ℚ.+ s)
      (r ℚ.+ s)
      ε
      (rational-close-translate q r s ε q∼r)

  add-right-ne : IsBinaryRationalNonexpandingRight rational-add
  add-right-ne q r s ε r∼s =
    point-point-close
      (q ℚ.+ r)
      (q ℚ.+ s)
      ε
      (rational-close-translate-left q r s ε r∼s)


infixl 6 _+ᶜ_

_+ᶜ_ : ℝᶜ → ℝᶜ → ℝᶜ
_+ᶜ_ =
  extendBinaryNonexpanding rational-add add-left-ne add-right-ne


add-rational :
  (q r : ℚ) →
  rational q +ᶜ rational r ≡ rational (q ℚ.+ r)
add-rational q r =
  refl


add-rational-left :
  (q : ℚ) (y : ℝᶜ) →
  rational q +ᶜ y ≡
  extendNonexpanding (rational-add q) (add-right-ne q) y
add-rational-left q y =
  refl


add-rational-right :
  (x : ℝᶜ) (r : ℚ) →
  x +ᶜ rational r ≡
  extendNonexpanding
    (λ q → rational-add q r)
    (λ q s ε q∼s → add-left-ne q s r ε q∼s)
    x
add-rational-right =
  extendBinaryNonexpanding-rational-right
    rational-add
    add-left-ne
    add-right-ne


add-close-left :
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  (z : ℝᶜ) →
  (x +ᶜ z) ∼[ ε ] (y +ᶜ z)
add-close-left =
  extendBinaryNonexpanding-close-left
    rational-add
    add-left-ne
    add-right-ne


add-close-right :
  (x : ℝᶜ) →
  {y z : ℝᶜ} {ε : ℚ⁺} →
  y ∼[ ε ] z →
  (x +ᶜ y) ∼[ ε ] (x +ᶜ z)
add-close-right =
  extendBinaryNonexpanding-close-right
    rational-add
    add-left-ne
    add-right-ne


add-close :
  {x y z w : ℝᶜ} {η ε : ℚ⁺} →
  x ∼[ η ] y →
  z ∼[ ε ] w →
  (x +ᶜ z) ∼[ η +⁺ ε ] (y +ᶜ w)
add-close =
  extendBinaryNonexpanding-close
    rational-add
    add-left-ne
    add-right-ne


add-nonexpanding-left :
  (z : ℝᶜ) →
  IsNonexpanding CauchyRealsMetricSpace CauchyRealsMetricSpace (λ x → x +ᶜ z)
add-nonexpanding-left z x∼y =
  add-close-left x∼y z


add-nonexpanding-right :
  (x : ℝᶜ) →
  IsNonexpanding CauchyRealsMetricSpace CauchyRealsMetricSpace (λ y → x +ᶜ y)
add-nonexpanding-right x =
  add-close-right x


add-continuous-left :
  (z : ℝᶜ) →
  IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (λ x → x +ᶜ z)
add-continuous-left z =
  nonexpanding→uniformlyContinuous
    {𝓧 = CauchyRealsMetricSpace}
    {𝓨 = CauchyRealsMetricSpace}
    {f = λ x → x +ᶜ z}
    (add-nonexpanding-left z)


add-continuous-right :
  (x : ℝᶜ) →
  IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (λ y → x +ᶜ y)
add-continuous-right x =
  nonexpanding→uniformlyContinuous
    {𝓧 = CauchyRealsMetricSpace}
    {𝓨 = CauchyRealsMetricSpace}
    {f = λ y → x +ᶜ y}
    (add-nonexpanding-right x)


add-zero-right : (x : ℝᶜ) → x +ᶜ 0ᶜ ≡ x
add-zero-right =
  nonexpanding-equal
    (λ x → x +ᶜ 0ᶜ)
    (λ x → x)
    (add-nonexpanding-left 0ᶜ)
    (id-nonexpanding CauchyRealsMetricSpace)
    λ q →
      add-rational q 0ℚ ∙
      cong rational (ℚ.+IdR q)


add-zero-left : (x : ℝᶜ) → 0ᶜ +ᶜ x ≡ x
add-zero-left =
  nonexpanding-equal
    (λ x → 0ᶜ +ᶜ x)
    (λ x → x)
    (add-nonexpanding-right 0ᶜ)
    (id-nonexpanding CauchyRealsMetricSpace)
    λ q →
      add-rational 0ℚ q ∙
      cong rational (ℚ.+IdL q)


add-comm :
  (x y : ℝᶜ) →
  x +ᶜ y ≡ y +ᶜ x
add-comm =
  binary-nonexpanding-equal
    _+ᶜ_
    (λ x y → y +ᶜ x)
    add-nonexpanding-left
    add-nonexpanding-right
    add-nonexpanding-right
    add-nonexpanding-left
    λ q r → cong rational (ℚ.+Comm q r)


add-assoc-rational-rational-left :
  (q r : ℚ) (z : ℝᶜ) →
  rational q +ᶜ (rational r +ᶜ z) ≡
  (rational q +ᶜ rational r) +ᶜ z
add-assoc-rational-rational-left q r =
  nonexpanding-equal
    (λ z → rational q +ᶜ (rational r +ᶜ z))
    (λ z → (rational q +ᶜ rational r) +ᶜ z)
    (comp-nonexpanding
      {𝓧 = CauchyRealsMetricSpace}
      {𝓨 = CauchyRealsMetricSpace}
      {𝓩 = CauchyRealsMetricSpace}
      (add-nonexpanding-right (rational q))
      (add-nonexpanding-right (rational r)))
    (add-nonexpanding-right (rational q +ᶜ rational r))
    (λ s → cong rational (ℚ.+Assoc q r s))


add-assoc-rational-left :
  (q : ℚ) (y z : ℝᶜ) →
  rational q +ᶜ (y +ᶜ z) ≡
  (rational q +ᶜ y) +ᶜ z
add-assoc-rational-left q y z =
  nonexpanding-equal
    (λ w → rational q +ᶜ (w +ᶜ z))
    (λ w → (rational q +ᶜ w) +ᶜ z)
    (comp-nonexpanding
      {𝓧 = CauchyRealsMetricSpace}
      {𝓨 = CauchyRealsMetricSpace}
      {𝓩 = CauchyRealsMetricSpace}
      (add-nonexpanding-right (rational q))
      (add-nonexpanding-left z))
    (comp-nonexpanding
      {𝓧 = CauchyRealsMetricSpace}
      {𝓨 = CauchyRealsMetricSpace}
      {𝓩 = CauchyRealsMetricSpace}
      (add-nonexpanding-left z)
      (add-nonexpanding-right (rational q)))
    (λ r → add-assoc-rational-rational-left q r z)
    y


add-assoc :
  (x y z : ℝᶜ) →
  x +ᶜ (y +ᶜ z) ≡ (x +ᶜ y) +ᶜ z
add-assoc x y z =
  nonexpanding-equal
    (λ w → w +ᶜ (y +ᶜ z))
    (λ w → (w +ᶜ y) +ᶜ z)
    (add-nonexpanding-left (y +ᶜ z))
    (comp-nonexpanding
      {𝓧 = CauchyRealsMetricSpace}
      {𝓨 = CauchyRealsMetricSpace}
      {𝓩 = CauchyRealsMetricSpace}
      (add-nonexpanding-left z)
      (add-nonexpanding-left y))
    (λ q → add-assoc-rational-left q y z)
    x


add-inverse-right-continuous :
  IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (λ x → x +ᶜ (-ᶜ x))
add-inverse-right-continuous =
  (λ ε → half⁺ ε) , closeAt
  where
  closeAt :
    (ε : ℚ⁺) →
    {x y : ℝᶜ} →
    x ∼[ half⁺ ε ] y →
    (x +ᶜ (-ᶜ x)) ∼[ ε ] (y +ᶜ (-ᶜ y))
  closeAt ε {x = x} {y = y} x∼y =
    subst
      (λ ρ → (x +ᶜ (-ᶜ x)) ∼[ ρ ] (y +ᶜ (-ᶜ y)))
      (half⁺+half⁺≡ ε)
      (add-close x∼y (neg-close x∼y))


add-inverse-right :
  (x : ℝᶜ) →
  x +ᶜ (-ᶜ x) ≡ 0ᶜ
add-inverse-right =
  continuous-constant-equal
    (λ x → x +ᶜ (-ᶜ x))
    0ᶜ
    add-inverse-right-continuous
    (λ q → cong rational (ℚ.+InvR q))


add-inverse-left :
  (x : ℝᶜ) →
  (-ᶜ x) +ᶜ x ≡ 0ᶜ
add-inverse-left x =
  add-comm (-ᶜ x) x ∙
  add-inverse-right x
