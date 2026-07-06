{-

Global multiplication for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Arithmetic.Multiplication where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ; Σ-syntax; _,_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Constructive.CauchyReals.Arithmetic.Addition
open import Constructive.CauchyReals.Arithmetic.Base
open import Constructive.CauchyReals.Arithmetic.Internal.BoundedMultiplication
open import Constructive.CauchyReals.Arithmetic.Negation
open import Constructive.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.CauchyReals.Base
open import Constructive.Analysis.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.CauchyReals.Extension
open import Constructive.CauchyReals.Order.Bounded
open import Constructive.CauchyReals.Order.Density
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  BoundedEvidenceᶜ : ℝᶜ → Type₀
  BoundedEvidenceᶜ x =
    Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ x

  mulWithBoundᶜ :
    (x y : ℝᶜ) →
    BoundedEvidenceᶜ x →
    ℝᶜ
  mulWithBoundᶜ x y (κ , x-bound) =
    boundedMulᶜ κ x x-bound y

  mulWithBoundᶜ-constant :
    (x y : ℝᶜ) →
    (b c : BoundedEvidenceᶜ x) →
    mulWithBoundᶜ x y b ≡ mulWithBoundᶜ x y c
  mulWithBoundᶜ-constant x y (κ , κ-bound) (μ , μ-bound) =
    boundedMulᶜ-bound-independent κ μ x κ-bound μ-bound y

  mulFromBoundsᶜ :
    (x y : ℝᶜ) →
    ∥ BoundedEvidenceᶜ x ∥₁ →
    ℝᶜ
  mulFromBoundsᶜ x y =
    Prop.rec→Set
      isSetCompletion
      (mulWithBoundᶜ x y)
      (mulWithBoundᶜ-constant x y)

  scale-precision-cancel :
    (κ ε : ℚ⁺) →
    κ *⁺ (posInv⁺ κ *⁺ ε) ≡ ε
  scale-precision-cancel κ ε =
    sym (*⁺-assoc κ (posInv⁺ κ) ε) ∙
    cong (λ ρ → ρ *⁺ ε) (*⁺-posInv-right κ) ∙
    *⁺-identity-left ε

  scale-precision-mono :
    (κ ε δ : ℚ⁺) →
    ε <⁺ δ →
    κ *⁺ ε <⁺ κ *⁺ δ
  scale-precision-mono κ ε δ ε<δ =
    Rational.mul-left-positive-<
      {a = radius κ}
      {b = radius ε}
      {c = radius δ}
      (κ .snd)
      ε<δ

  four-eighths< :
    (ε : ℚ⁺) →
    let α = quarter⁺ (half⁺ ε) in
    (α +⁺ α) +⁺ (α +⁺ α) <⁺ ε
  four-eighths< ε =
    half<ε
    where
    α : ℚ⁺
    α = quarter⁺ (half⁺ ε)

    αα<halfε : α +⁺ α <⁺ half⁺ ε
    αα<halfε =
      quarter-sum< (half⁺ ε)

    αα+αα<half+half : radius ((α +⁺ α) +⁺ (α +⁺ α)) ℚOrder.< radius (half⁺ ε +⁺ half⁺ ε)
    αα+αα<half+half =
      ℚOrder.<Monotone+
        (radius (α +⁺ α))
        (radius (half⁺ ε))
        (radius (α +⁺ α))
        (radius (half⁺ ε))
        αα<halfε
        αα<halfε

    half<ε : radius ((α +⁺ α) +⁺ (α +⁺ α)) ℚOrder.< radius ε
    half<ε =
      subst
        (λ ρ → radius ((α +⁺ α) +⁺ (α +⁺ α)) ℚOrder.< ρ)
        (cong radius (half⁺+half⁺≡ ε))
        αα+αα<half+half

  smallPrecision :
    (κ ρ α φ : ℚ⁺) →
    ℚ⁺
  smallPrecision κ ρ α φ =
    half⁺ (min⁺ φ (min⁺ (posInv⁺ κ *⁺ α) (posInv⁺ ρ *⁺ α)))

  smallPrecision<φ :
    (κ ρ α φ : ℚ⁺) →
    smallPrecision κ ρ α φ <⁺ φ
  smallPrecision<φ κ ρ α φ =
    half-min⁺<left φ (min⁺ (posInv⁺ κ *⁺ α) (posInv⁺ ρ *⁺ α))

  smallPrecision<left :
    (κ ρ α φ : ℚ⁺) →
    smallPrecision κ ρ α φ <⁺ posInv⁺ κ *⁺ α
  smallPrecision<left κ ρ α φ =
    Rational.<≤-trans
      {p = radius (smallPrecision κ ρ α φ)}
      {q = radius (min⁺ (posInv⁺ κ *⁺ α) (posInv⁺ ρ *⁺ α))}
      {r = radius (posInv⁺ κ *⁺ α)}
      (half-min⁺<right φ (min⁺ (posInv⁺ κ *⁺ α) (posInv⁺ ρ *⁺ α)))
      (min⁺≤left (posInv⁺ κ *⁺ α) (posInv⁺ ρ *⁺ α))

  smallPrecision<right :
    (κ ρ α φ : ℚ⁺) →
    smallPrecision κ ρ α φ <⁺ posInv⁺ ρ *⁺ α
  smallPrecision<right κ ρ α φ =
    Rational.<≤-trans
      {p = radius (smallPrecision κ ρ α φ)}
      {q = radius (min⁺ (posInv⁺ κ *⁺ α) (posInv⁺ ρ *⁺ α))}
      {r = radius (posInv⁺ ρ *⁺ α)}
      (half-min⁺<right φ (min⁺ (posInv⁺ κ *⁺ α) (posInv⁺ ρ *⁺ α)))
      (min⁺≤right (posInv⁺ κ *⁺ α) (posInv⁺ ρ *⁺ α))

  scale-smallPrecision-left :
    (κ ρ α φ : ℚ⁺) →
    κ *⁺ smallPrecision κ ρ α φ <⁺ α
  scale-smallPrecision-left κ ρ α φ =
    subst
      (λ θ → κ *⁺ smallPrecision κ ρ α φ <⁺ θ)
      (scale-precision-cancel κ α)
      (scale-precision-mono
        κ
        (smallPrecision κ ρ α φ)
        (posInv⁺ κ *⁺ α)
        (smallPrecision<left κ ρ α φ))

  scale-smallPrecision-right :
    (κ ρ α φ : ℚ⁺) →
    ρ *⁺ smallPrecision κ ρ α φ <⁺ α
  scale-smallPrecision-right κ ρ α φ =
    subst
      (λ θ → ρ *⁺ smallPrecision κ ρ α φ <⁺ θ)
      (scale-precision-cancel ρ α)
      (scale-precision-mono
        ρ
        (smallPrecision κ ρ α φ)
        (posInv⁺ ρ *⁺ α)
        (smallPrecision<right κ ρ α φ))


infixl 7 _·ᶜ_

_·ᶜ_ : ℝᶜ → ℝᶜ → ℝᶜ
x ·ᶜ y =
  mulFromBoundsᶜ x y (merely-boundedᶜ x)


mulᶜ-bound :
  (κ : ℚ⁺) (x : ℝᶜ) →
  (x-bound : BoundedByᶜ κ x) →
  (y : ℝᶜ) →
  x ·ᶜ y ≡ boundedMulᶜ κ x x-bound y
mulᶜ-bound κ x x-bound y =
  Prop.elim
    {P = λ bounds →
      mulFromBoundsᶜ x y bounds ≡ boundedMulᶜ κ x x-bound y}
    (λ _ → isSetCompletion _ _)
    step
    (merely-boundedᶜ x)
  where
  step :
    (bounds : BoundedEvidenceᶜ x) →
    mulFromBoundsᶜ x y ∣ bounds ∣₁ ≡ boundedMulᶜ κ x x-bound y
  step (μ , μ-bound) =
    boundedMulᶜ-bound-independent μ κ x μ-bound x-bound y


mulᶜ-rational-left :
  (q : ℚ) (y : ℝᶜ) →
  rational q ·ᶜ y ≡ scalarMulᶜ q y
mulᶜ-rational-left q y =
  mulᶜ-bound
    (scalar-bound q)
    (rational q)
    q-bound
    y ∙
  boundedMulᶜ-rational-left-from-bounded
    (scalar-bound q)
    q
    q-bound
    y
  where
  q-bound : BoundedByᶜ (scalar-bound q) (rational q)
  q-bound =
    rational-bound→boundedᶜ
      (scalar-bound q)
      q
      (scalar-bound-rational-boundᶜ q)


mulᶜ-rational-right :
  (x : ℝᶜ) (q : ℚ) →
  x ·ᶜ rational q ≡ scalarMulᶜ q x
mulᶜ-rational-right x q =
  Prop.elim
    {P = λ bounds →
      mulFromBoundsᶜ x (rational q) bounds ≡ scalarMulᶜ q x}
    (λ _ → isSetCompletion _ _)
    step
    (merely-boundedᶜ x)
  where
  step :
    (bounds : BoundedEvidenceᶜ x) →
    mulFromBoundsᶜ x (rational q) ∣ bounds ∣₁ ≡ scalarMulᶜ q x
  step (κ , x-bound) =
    boundedMulᶜ-rational κ x x-bound q


mulᶜ-rational-rational :
  (q r : ℚ) →
  rational q ·ᶜ rational r ≡ rational (q ℚ.· r)
mulᶜ-rational-rational q r =
  mulᶜ-rational-left q (rational r) ∙
  scalarMulᶜ-rational q r


mulᶜ-comm-rational-left :
  (q : ℚ) (x : ℝᶜ) →
  rational q ·ᶜ x ≡ x ·ᶜ rational q
mulᶜ-comm-rational-left q x =
  mulᶜ-rational-left q x ∙
  sym (mulᶜ-rational-right x q)


mulᶜ-comm-rational-right :
  (x : ℝᶜ) (q : ℚ) →
  x ·ᶜ rational q ≡ rational q ·ᶜ x
mulᶜ-comm-rational-right x q =
  sym (mulᶜ-comm-rational-left q x)


mulᶜ-zero-left :
  (x : ℝᶜ) →
  0ᶜ ·ᶜ x ≡ 0ᶜ
mulᶜ-zero-left x =
  mulᶜ-rational-left 0ℚ x ∙
  scalarMulᶜ-zero x


mulᶜ-zero-right :
  (x : ℝᶜ) →
  x ·ᶜ 0ᶜ ≡ 0ᶜ
mulᶜ-zero-right x =
  mulᶜ-rational-right x 0ℚ ∙
  scalarMulᶜ-zero x


mulᶜ-one-left :
  (x : ℝᶜ) →
  1ᶜ ·ᶜ x ≡ x
mulᶜ-one-left x =
  mulᶜ-rational-left 1ℚ x ∙
  scalarMulᶜ-one x


mulᶜ-one-right :
  (x : ℝᶜ) →
  x ·ᶜ 1ᶜ ≡ x
mulᶜ-one-right x =
  mulᶜ-rational-right x 1ℚ ∙
  scalarMulᶜ-one x


mulᶜ-neg-right :
  (x y : ℝᶜ) →
  x ·ᶜ (-ᶜ y) ≡ -ᶜ (x ·ᶜ y)
mulᶜ-neg-right x y =
  Prop.elim
    {P = λ bounds →
      mulFromBoundsᶜ x (-ᶜ y) bounds ≡
      -ᶜ (mulFromBoundsᶜ x y bounds)}
    (λ _ → isSetCompletion _ _)
    step
    (merely-boundedᶜ x)
  where
  step :
    (bounds : BoundedEvidenceᶜ x) →
    mulFromBoundsᶜ x (-ᶜ y) ∣ bounds ∣₁ ≡
    -ᶜ (mulFromBoundsᶜ x y ∣ bounds ∣₁)
  step (κ , x-bound) =
    boundedMulᶜ-neg-right κ x x-bound y


mulᶜ-distrib-right :
  (x y z : ℝᶜ) →
  x ·ᶜ (y +ᶜ z) ≡
  x ·ᶜ y +ᶜ x ·ᶜ z
mulᶜ-distrib-right x y z =
  Prop.elim
    {P = λ bounds →
      mulFromBoundsᶜ x (y +ᶜ z) bounds ≡
      mulFromBoundsᶜ x y bounds +ᶜ mulFromBoundsᶜ x z bounds}
    (λ _ → isSetCompletion _ _)
    step
    (merely-boundedᶜ x)
  where
  step :
    (bounds : BoundedEvidenceᶜ x) →
    mulFromBoundsᶜ x (y +ᶜ z) ∣ bounds ∣₁ ≡
    mulFromBoundsᶜ x y ∣ bounds ∣₁ +ᶜ
    mulFromBoundsᶜ x z ∣ bounds ∣₁
  step (κ , x-bound) =
    boundedMulᶜ-distrib-real-add κ x x-bound y z


mulᶜ-distrib-rational-left :
  (q : ℚ) (x y : ℝᶜ) →
  rational q ·ᶜ (x +ᶜ y) ≡
  rational q ·ᶜ x +ᶜ rational q ·ᶜ y
mulᶜ-distrib-rational-left q x y =
  mulᶜ-rational-left q (x +ᶜ y) ∙
  scalarMulᶜ-distrib-real-add q x y ∙
  cong₂ _+ᶜ_
    (sym (mulᶜ-rational-left q x))
    (sym (mulᶜ-rational-left q y))


mulᶜ-rational-left-assoc :
  (q r : ℚ) (x : ℝᶜ) →
  rational q ·ᶜ (rational r ·ᶜ x) ≡
  rational (q ℚ.· r) ·ᶜ x
mulᶜ-rational-left-assoc q r x =
  mulᶜ-rational-left q (rational r ·ᶜ x) ∙
  cong (scalarMulᶜ q) (mulᶜ-rational-left r x) ∙
  scalarMulᶜ-assoc q r x ∙
  sym (mulᶜ-rational-left (q ℚ.· r) x)


mulᶜ-rational-right-assoc :
  (x : ℝᶜ) (q r : ℚ) →
  (x ·ᶜ rational q) ·ᶜ rational r ≡
  x ·ᶜ rational (q ℚ.· r)
mulᶜ-rational-right-assoc x q r =
  mulᶜ-rational-right (x ·ᶜ rational q) r ∙
  cong (scalarMulᶜ r) (mulᶜ-rational-right x q) ∙
  scalarMulᶜ-assoc r q x ∙
  cong (λ s → scalarMulᶜ s x) (ℚ.·Comm r q) ∙
  sym (mulᶜ-rational-right x (q ℚ.· r))


mulᶜ-continuous-rational-left :
  (q : ℚ) →
  IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (λ x → rational q ·ᶜ x)
mulᶜ-continuous-rational-left q =
  δ , closeAt
  where
  scalar-cont : IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (scalarMulᶜ q)
  scalar-cont =
    scalarMulᶜ-continuous q

  δ : ℚ⁺ → ℚ⁺
  δ =
    fst scalar-cont

  scalar-close :
    (ε : ℚ⁺) →
    {x y : ℝᶜ} →
    x ∼[ δ ε ] y →
    scalarMulᶜ q x ∼[ ε ] scalarMulᶜ q y
  scalar-close =
    snd scalar-cont

  closeAt :
    (ε : ℚ⁺) →
    {x y : ℝᶜ} →
    x ∼[ δ ε ] y →
    rational q ·ᶜ x ∼[ ε ] rational q ·ᶜ y
  closeAt ε {x = x} {y = y} x∼y =
    subst2
      (λ u v → u ∼[ ε ] v)
      (sym (mulᶜ-rational-left q x))
      (sym (mulᶜ-rational-left q y))
      (scalar-close ε x∼y)


mulᶜ-continuous-rational-right :
  (q : ℚ) →
  IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (λ x → x ·ᶜ rational q)
mulᶜ-continuous-rational-right q =
  δ , closeAt
  where
  scalar-cont : IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (scalarMulᶜ q)
  scalar-cont =
    scalarMulᶜ-continuous q

  δ : ℚ⁺ → ℚ⁺
  δ =
    fst scalar-cont

  scalar-close :
    (ε : ℚ⁺) →
    {x y : ℝᶜ} →
    x ∼[ δ ε ] y →
    scalarMulᶜ q x ∼[ ε ] scalarMulᶜ q y
  scalar-close =
    snd scalar-cont

  closeAt :
    (ε : ℚ⁺) →
    {x y : ℝᶜ} →
    x ∼[ δ ε ] y →
    x ·ᶜ rational q ∼[ ε ] y ·ᶜ rational q
  closeAt ε {x = x} {y = y} x∼y =
    subst2
      (λ u v → u ∼[ ε ] v)
      (sym (mulᶜ-rational-right x q))
      (sym (mulᶜ-rational-right y q))
      (scalar-close ε x∼y)


mulᶜ-continuous-right-with-bound :
  (κ : ℚ⁺) (x : ℝᶜ) →
  BoundedByᶜ κ x →
  IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (λ y → x ·ᶜ y)
mulᶜ-continuous-right-with-bound κ x x-bound =
  δ , closeAt
  where
  local-cont : IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (boundedMulᶜ κ x x-bound)
  local-cont =
    boundedMulᶜ-continuous κ x x-bound

  δ : ℚ⁺ → ℚ⁺
  δ =
    fst local-cont

  local-close :
    (ε : ℚ⁺) →
    {y z : ℝᶜ} →
    y ∼[ δ ε ] z →
    boundedMulᶜ κ x x-bound y ∼[ ε ] boundedMulᶜ κ x x-bound z
  local-close =
    snd local-cont

  closeAt :
    (ε : ℚ⁺) →
    {y z : ℝᶜ} →
    y ∼[ δ ε ] z →
    x ·ᶜ y ∼[ ε ] x ·ᶜ z
  closeAt ε {y = y} {z = z} y∼z =
    subst2
      (λ u v → u ∼[ ε ] v)
      (sym (mulᶜ-bound κ x x-bound y))
      (sym (mulᶜ-bound κ x x-bound z))
      (local-close ε y∼z)


mulᶜ-comm-close-with-bounds :
  (κ μ : ℚ⁺) (x y : ℝᶜ) →
  BoundedByᶜ κ x →
  BoundedByᶜ μ y →
  (ε : ℚ⁺) →
  (x ·ᶜ y) ∼[ ε ] (y ·ᶜ x)
mulᶜ-comm-close-with-bounds κ μ x y x-bound y-bound ε =
  Prop.rec squash stepY (rational-approximation y θy)
  where
  α φ η ρκ ρμ θx θy : ℚ⁺
  α = quarter⁺ (half⁺ ε)
  φ = quarter⁺ α
  η = half⁺ α
  ρκ = κ +⁺ η
  ρμ = μ +⁺ η
  θx = smallPrecision μ ρμ α φ
  θy = smallPrecision κ ρκ α φ

  φ<η : φ <⁺ η
  φ<η =
    half< (half⁺ α)

  θx<φ : θx <⁺ φ
  θx<φ =
    smallPrecision<φ μ ρμ α φ

  θy<φ : θy <⁺ φ
  θy<φ =
    smallPrecision<φ κ ρκ α φ

  μθx<α : μ *⁺ θx <⁺ α
  μθx<α =
    scale-smallPrecision-left μ ρμ α φ

  ρμθx<α : ρμ *⁺ θx <⁺ α
  ρμθx<α =
    scale-smallPrecision-right μ ρμ α φ

  κθy<α : κ *⁺ θy <⁺ α
  κθy<α =
    scale-smallPrecision-left κ ρκ α φ

  ρκθy<α : ρκ *⁺ θy <⁺ α
  ρκθy<α =
    scale-smallPrecision-right κ ρκ α φ

  stepY :
    Σ[ r ∈ ℚ ] y ∼[ θy ] rational r →
    (x ·ᶜ y) ∼[ ε ] (y ·ᶜ x)
  stepY (r , y∼r) =
    Prop.rec squash (stepX r y∼r r-bound) (rational-approximation x θx)
    where
    r-bound : RationalBoundᶜ ρμ r
    r-bound =
      bounded-approximation-rational-boundᶜ
        μ
        φ
        η
        θy
        y
        r
        θy<φ
        φ<η
        y-bound
        y∼r

    stepX :
      (r : ℚ) →
      y ∼[ θy ] rational r →
      RationalBoundᶜ ρμ r →
      Σ[ q ∈ ℚ ] x ∼[ θx ] rational q →
      (x ·ᶜ y) ∼[ ε ] (y ·ᶜ x)
    stepX r y∼r r-bound (q , x∼q) =
      close-mono
        {ε = (α +⁺ α) +⁺ (α +⁺ α)}
        {δ = ε}
        (four-eighths< ε)
        (close-triangle xy∼rq (close-sym yx∼rq))
      where
      q-bound : RationalBoundᶜ ρκ q
      q-bound =
        bounded-approximation-rational-boundᶜ
          κ
          φ
          η
          θx
          x
          q
          θx<φ
          φ<η
          x-bound
          x∼q

      xy∼rx-raw :
        (x ·ᶜ y) ∼[ κ *⁺ θy ] scalarMulᶜ r x
      xy∼rx-raw =
        subst2
          (λ u v → u ∼[ κ *⁺ θy ] v)
          (sym (mulᶜ-bound κ x x-bound y))
          (boundedMulᶜ-rational κ x x-bound r)
          (boundedMulᶜ-close κ x x-bound y∼r)

      xy∼rx :
        (x ·ᶜ y) ∼[ α ] scalarMulᶜ r x
      xy∼rx =
        close-mono κθy<α xy∼rx-raw

      rx∼rq-raw :
        scalarMulᶜ r x ∼[ ρμ *⁺ θx ] scalarMulᶜ r (rational q)
      rx∼rq-raw =
        scalarMulᶜ-close-rational-bound r ρμ r-bound x∼q

      rx∼rq :
        scalarMulᶜ r x ∼[ α ] rational (r ℚ.· q)
      rx∼rq =
        close-mono
          ρμθx<α
          (subst
            (λ z → scalarMulᶜ r x ∼[ ρμ *⁺ θx ] z)
            (scalarMulᶜ-rational r q)
            rx∼rq-raw)

      xy∼rq :
        (x ·ᶜ y) ∼[ α +⁺ α ] rational (r ℚ.· q)
      xy∼rq =
        close-triangle xy∼rx rx∼rq

      yx∼qy-raw :
        (y ·ᶜ x) ∼[ μ *⁺ θx ] scalarMulᶜ q y
      yx∼qy-raw =
        subst2
          (λ u v → u ∼[ μ *⁺ θx ] v)
          (sym (mulᶜ-bound μ y y-bound x))
          (boundedMulᶜ-rational μ y y-bound q)
          (boundedMulᶜ-close μ y y-bound x∼q)

      yx∼qy :
        (y ·ᶜ x) ∼[ α ] scalarMulᶜ q y
      yx∼qy =
        close-mono μθx<α yx∼qy-raw

      qy∼qr-raw :
        scalarMulᶜ q y ∼[ ρκ *⁺ θy ] scalarMulᶜ q (rational r)
      qy∼qr-raw =
        scalarMulᶜ-close-rational-bound q ρκ q-bound y∼r

      qy∼qr :
        scalarMulᶜ q y ∼[ α ] rational (q ℚ.· r)
      qy∼qr =
        close-mono
          ρκθy<α
          (subst
            (λ z → scalarMulᶜ q y ∼[ ρκ *⁺ θy ] z)
            (scalarMulᶜ-rational q r)
            qy∼qr-raw)

      qy∼rq :
        scalarMulᶜ q y ∼[ α ] rational (r ℚ.· q)
      qy∼rq =
        subst
          (λ z → scalarMulᶜ q y ∼[ α ] z)
          (cong rational (ℚ.·Comm q r))
          qy∼qr

      yx∼rq :
        (y ·ᶜ x) ∼[ α +⁺ α ] rational (r ℚ.· q)
      yx∼rq =
        close-triangle yx∼qy qy∼rq


mulᶜ-comm :
  (x y : ℝᶜ) →
  x ·ᶜ y ≡ y ·ᶜ x
mulᶜ-comm x y =
  path (x ·ᶜ y) (y ·ᶜ x) λ ε →
    Prop.rec2
      squash
      (λ (κ , x-bound) (μ , y-bound) →
        mulᶜ-comm-close-with-bounds κ μ x y x-bound y-bound ε)
      (merely-boundedᶜ x)
      (merely-boundedᶜ y)


mulᶜ-continuous-left-with-bound :
  (κ : ℚ⁺) (y : ℝᶜ) →
  BoundedByᶜ κ y →
  IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (λ x → x ·ᶜ y)
mulᶜ-continuous-left-with-bound κ y y-bound =
  δ , closeAt
  where
  local-cont : IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (λ x → y ·ᶜ x)
  local-cont =
    mulᶜ-continuous-right-with-bound κ y y-bound

  δ : ℚ⁺ → ℚ⁺
  δ =
    fst local-cont

  local-close :
    (ε : ℚ⁺) →
    {x z : ℝᶜ} →
    x ∼[ δ ε ] z →
    (y ·ᶜ x) ∼[ ε ] (y ·ᶜ z)
  local-close =
    snd local-cont

  closeAt :
    (ε : ℚ⁺) →
    {x z : ℝᶜ} →
    x ∼[ δ ε ] z →
    x ·ᶜ y ∼[ ε ] z ·ᶜ y
  closeAt ε {x = x} {z = z} x∼z =
    subst2
      (λ u v → u ∼[ ε ] v)
      (sym (mulᶜ-comm x y))
      (sym (mulᶜ-comm z y))
      (local-close ε x∼z)


mulᶜ-distrib-left :
  (x y z : ℝᶜ) →
  (x +ᶜ y) ·ᶜ z ≡
  x ·ᶜ z +ᶜ y ·ᶜ z
mulᶜ-distrib-left x y z =
  mulᶜ-comm (x +ᶜ y) z ∙
  mulᶜ-distrib-right z x y ∙
  cong₂ _+ᶜ_
    (mulᶜ-comm z x)
    (mulᶜ-comm z y)


mulᶜ-assoc-rational-left :
  (q : ℚ) (x y : ℝᶜ) →
  rational q ·ᶜ (x ·ᶜ y) ≡
  (rational q ·ᶜ x) ·ᶜ y
mulᶜ-assoc-rational-left q x y =
  Prop.rec
    (isSetCompletion _ _)
    step
    (merely-boundedᶜ x)
  where
  step :
    BoundedEvidenceᶜ x →
    rational q ·ᶜ (x ·ᶜ y) ≡
    (rational q ·ᶜ x) ·ᶜ y
  step (κ , x-bound) =
    continuous-equal
      (λ z → rational q ·ᶜ (x ·ᶜ z))
      (λ z → (rational q ·ᶜ x) ·ᶜ z)
      left-cont
      right-cont
      rational-path
      y
    where
    q-bound : RationalBoundᶜ (scalar-bound q) q
    q-bound =
      scalar-bound-rational-boundᶜ q

    qx-bound-scalar :
      BoundedByᶜ (scalar-bound q *⁺ κ) (scalarMulᶜ q x)
    qx-bound-scalar =
      bounded-byᶜ-scale-rational-bound
        q
        κ
        (scalar-bound q)
        x
        q-bound
        x-bound

    qx-bound :
      BoundedByᶜ (scalar-bound q *⁺ κ) (rational q ·ᶜ x)
    qx-bound =
      subst
        (BoundedByᶜ (scalar-bound q *⁺ κ))
        (sym (mulᶜ-rational-left q x))
        qx-bound-scalar

    left-cont :
      IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (λ z → rational q ·ᶜ (x ·ᶜ z))
    left-cont =
      comp-uniformlyContinuous {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
        (mulᶜ-continuous-rational-left q)
        (mulᶜ-continuous-right-with-bound κ x x-bound)

    right-cont :
      IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (λ z → (rational q ·ᶜ x) ·ᶜ z)
    right-cont =
      mulᶜ-continuous-right-with-bound
        (scalar-bound q *⁺ κ)
        (rational q ·ᶜ x)
        qx-bound

    rational-path :
      (r : ℚ) →
      rational q ·ᶜ (x ·ᶜ rational r) ≡
      (rational q ·ᶜ x) ·ᶜ rational r
    rational-path r =
      left-path ∙ sym right-path
      where
      left-path :
        rational q ·ᶜ (x ·ᶜ rational r) ≡
        scalarMulᶜ (q ℚ.· r) x
      left-path =
        mulᶜ-rational-left q (x ·ᶜ rational r) ∙
        cong (scalarMulᶜ q) (mulᶜ-rational-right x r) ∙
        scalarMulᶜ-assoc q r x

      right-path :
        (rational q ·ᶜ x) ·ᶜ rational r ≡
        scalarMulᶜ (q ℚ.· r) x
      right-path =
        mulᶜ-rational-right (rational q ·ᶜ x) r ∙
        cong (scalarMulᶜ r) (mulᶜ-rational-left q x) ∙
        scalarMulᶜ-assoc r q x ∙
        cong (λ s → scalarMulᶜ s x) (ℚ.·Comm r q)


mulᶜ-assoc :
  (x y z : ℝᶜ) →
  x ·ᶜ (y ·ᶜ z) ≡ (x ·ᶜ y) ·ᶜ z
mulᶜ-assoc x y z =
  Prop.rec
    (isSetCompletion _ _)
    stepY
    (merely-boundedᶜ y)
  where
  stepY :
    BoundedEvidenceᶜ y →
    x ·ᶜ (y ·ᶜ z) ≡ (x ·ᶜ y) ·ᶜ z
  stepY (μ , y-bound) =
    Prop.rec
      (isSetCompletion _ _)
      stepZ
      (merely-boundedᶜ z)
    where
    stepZ :
      BoundedEvidenceᶜ z →
      x ·ᶜ (y ·ᶜ z) ≡ (x ·ᶜ y) ·ᶜ z
    stepZ (ν , z-bound) =
      Prop.rec
        (isSetCompletion _ _)
        stepYZ
        (merely-boundedᶜ (y ·ᶜ z))
      where
      stepYZ :
        BoundedEvidenceᶜ (y ·ᶜ z) →
        x ·ᶜ (y ·ᶜ z) ≡ (x ·ᶜ y) ·ᶜ z
      stepYZ (ρ , yz-bound) =
        continuous-equal
          (λ w → w ·ᶜ (y ·ᶜ z))
          (λ w → (w ·ᶜ y) ·ᶜ z)
          left-cont
          right-cont
          (λ q → mulᶜ-assoc-rational-left q y z)
          x
        where
        left-cont :
          IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (λ w → w ·ᶜ (y ·ᶜ z))
        left-cont =
          mulᶜ-continuous-left-with-bound ρ (y ·ᶜ z) yz-bound

        right-cont :
          IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (λ w → (w ·ᶜ y) ·ᶜ z)
        right-cont =
          comp-uniformlyContinuous {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
            (mulᶜ-continuous-left-with-bound ν z z-bound)
            (mulᶜ-continuous-left-with-bound μ y y-bound)
