{-

Rational-endpoint interval grids

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Interval.Grid.Rational where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; _×_)

open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Interval.Base
open import Constructive.Analysis.Reals.Interval.Grid.Base
open import Constructive.Data.PositiveRationals
open import Constructive.Data.Rationals.Closeness
import Constructive.Data.Rationals as Rational


private
  p≤p+nonnegative :
    {p q : ℚ} →
    Rational.0ℚ ℚOrder.≤ q →
    p ℚOrder.≤ p ℚ.+ q
  p≤p+nonnegative {p = p} {q = q} 0≤q =
    subst
      (λ r → r ℚOrder.≤ p ℚ.+ q)
      (ℚ.+IdR p)
      (ℚOrder.≤Monotone+
        p p
        Rational.0ℚ q
        (ℚOrder.isRefl≤ p)
        0≤q)

  grid-one :
    (a δ : ℚ) →
    Rational.grid a δ (suc zero) ≡ a ℚ.+ δ
  grid-one a δ =
    Rational.grid-suc a δ zero ∙
    cong (λ q → q ℚ.+ δ) (Rational.grid-zero a δ)

  step-closeℚ :
    (a : ℚ) →
    (δ : ℚ⁺) →
    Closeℚ a (δ +⁺ δ) (a ℚ.+ radius δ)
  step-closeℚ a δ =
    subst2
      (λ q r → Closeℚ q (δ +⁺ δ) r)
      (ℚ.+IdL a)
      (ℚ.+Comm (radius δ) a)
      (rational-close-translate Rational.0ℚ (radius δ) a (δ +⁺ δ) close-zero-step)
    where
    close-zero-step : Closeℚ Rational.0ℚ (δ +⁺ δ) (radius δ)
    close-zero-step =
      subst
        (λ q → q ℚOrder.< radius (δ +⁺ δ))
        (sym (ℚ.+IdL (ℚ.- radius δ)))
        -δ<δ+δ ,
      subst
        (λ q → q ℚOrder.< radius (δ +⁺ δ))
        (sym (cong (radius δ ℚ.+_) Rational.neg-zero ∙ ℚ.+IdR (radius δ)))
        δ<δ+δ
      where
      δ<δ+δ : radius δ ℚOrder.< radius (δ +⁺ δ)
      δ<δ+δ =
        Rational.q<q+positive (radius δ) (radius δ) (δ .snd)

      -δ<0 : ℚ.- radius δ ℚOrder.< Rational.0ℚ
      -δ<0 =
        subst
          (λ q → ℚ.- radius δ ℚOrder.< q)
          Rational.neg-zero
          (Rational.negReverse< {p = Rational.0ℚ} {q = radius δ} (δ .snd))

      0<δ+δ : Rational.0ℚ ℚOrder.< radius (δ +⁺ δ)
      0<δ+δ =
        Rational.positive-sum {p = radius δ} {q = radius δ} (δ .snd) (δ .snd)

      -δ<δ+δ : ℚ.- radius δ ℚOrder.< radius (δ +⁺ δ)
      -δ<δ+δ =
        ℚOrder.isTrans< (ℚ.- radius δ) Rational.0ℚ (radius (δ +⁺ δ)) -δ<0 0<δ+δ

  step-closeᶜ :
    (a : ℚ) →
    (δ : ℚ⁺) →
    rational a ∼[ δ +⁺ δ ] rational (Rational.grid a (radius δ) (suc zero))
  step-closeᶜ a δ =
    subst
      (λ r → rational a ∼[ δ +⁺ δ ] rational r)
      (sym (grid-one a (radius δ)))
      (point-point-close a (a ℚ.+ radius δ) (δ +⁺ δ) (step-closeℚ a δ))


gridLower≤ℚ :
  (a : ℚ) →
  (δ : ℚ⁺) →
  (n : ℕ) →
  a ℚOrder.≤ Rational.grid a (radius δ) n
gridLower≤ℚ a δ n =
  p≤p+nonnegative
    {p = a}
    {q = Rational.natMul n (radius δ)}
    (Rational.natMul-nonnegative n (δ .snd))


gridLower≤ᶜ :
  (a : ℚ) →
  (δ : ℚ⁺) →
  (n : ℕ) →
  rational a ≤ᶜ rational (Rational.grid a (radius δ) n)
gridLower≤ᶜ a δ n =
  ≤ℚ→rational≤ᶜ (gridLower≤ℚ a δ n)


gridLowerWithRight≤ᶜ :
  (a b : ℚ) →
  (δ : ℚ⁺) →
  (n : ℕ) →
  Rational.grid a (radius δ) n ≡ b →
  rational a ≤ᶜ rational b
gridLowerWithRight≤ᶜ a b δ n right-path =
  subst
    (rational a ≤ᶜ_)
    (cong rational right-path)
    (gridLower≤ᶜ a δ n)


grid-shift :
  (a : ℚ) →
  (δ : ℚ⁺) →
  (n : ℕ) →
  Rational.grid (Rational.grid a (radius δ) (suc zero)) (radius δ) n ≡
  Rational.grid a (radius δ) (suc n)
grid-shift a δ zero =
  Rational.grid-zero (Rational.grid a (radius δ) (suc zero)) (radius δ)
grid-shift a δ (suc n) =
  Rational.grid-suc (Rational.grid a (radius δ) (suc zero)) (radius δ) n ∙
  cong (λ q → q ℚ.+ radius δ) (grid-shift a δ n) ∙
  sym (Rational.grid-suc a (radius δ) (suc n))


rationalStepGrid :
  (a : ℚ) →
  (δ : ℚ⁺) →
  (n : ℕ) →
  Grid
    (rational a)
    (rational (Rational.grid a (radius δ) n))
    (gridLower≤ᶜ a δ n)
    n
rationalStepGrid a δ zero =
  make-grid endpoint refl (cong rational (sym (Rational.grid-zero a (radius δ))))
  where
  endpoint : Fin (suc zero) → [ rational a , rational (Rational.grid a (radius δ) zero) ]ᶜ
  endpoint Fin.zero =
    leftEndpoint {a = rational a} {b = rational (Rational.grid a (radius δ) zero)}
      (gridLower≤ᶜ a δ zero)
rationalStepGrid a δ (suc n) =
  make-grid endpoint refl right-path
  where
  a₁ : ℚ
  a₁ = Rational.grid a (radius δ) (suc zero)

  tail : Grid
    (rational a₁)
    (rational (Rational.grid a₁ (radius δ) n))
    (gridLower≤ᶜ a₁ δ n)
    n
  tail =
    rationalStepGrid a₁ δ n

  a≤a₁ : rational a ≤ᶜ rational a₁
  a≤a₁ =
    gridLower≤ᶜ a δ (suc zero)

  tail-upper-path :
    rational (Rational.grid a₁ (radius δ) n) ≡
    rational (Rational.grid a (radius δ) (suc n))
  tail-upper-path =
    cong rational (grid-shift a δ n)

  embed-tail :
    [ rational a₁ , rational (Rational.grid a₁ (radius δ) n) ]ᶜ →
    [ rational a , rational (Rational.grid a (radius δ) (suc n)) ]ᶜ
  embed-tail (x , a₁≤x , x≤tail) =
    x ,
    ≤ᶜ-trans {x = rational a} {y = rational a₁} {z = x} a≤a₁ a₁≤x ,
    subst (x ≤ᶜ_) tail-upper-path x≤tail

  endpoint :
    Fin (suc (suc n)) →
    [ rational a , rational (Rational.grid a (radius δ) (suc n)) ]ᶜ
  endpoint Fin.zero =
    leftEndpoint
      {a = rational a}
      {b = rational (Rational.grid a (radius δ) (suc n))}
      (gridLower≤ᶜ a δ (suc n))
  endpoint (Fin.suc i) =
    embed-tail (Grid.point tail i)

  right-path :
    pointᶜ
      {a = rational a}
      {b = rational (Rational.grid a (radius δ) (suc n))}
      (endpoint (Fin.fromℕ (suc n))) ≡
    rational (Rational.grid a (radius δ) (suc n))
  right-path =
    Grid.right-point tail ∙ tail-upper-path


rationalStepGridAdjacentClose :
  (a : ℚ) →
  (δ : ℚ⁺) →
  (n : ℕ) →
  AdjacentClose (rationalStepGrid a δ n) (δ +⁺ δ)
rationalStepGridAdjacentClose a δ zero ()
rationalStepGridAdjacentClose a δ (suc n) Fin.zero =
  subst
    (λ y → rational a ∼[ δ +⁺ δ ] y)
    (sym (Grid.left-point tail))
    (step-closeᶜ a δ)
  where
  a₁ : ℚ
  a₁ = Rational.grid a (radius δ) (suc zero)

  tail : Grid
    (rational a₁)
    (rational (Rational.grid a₁ (radius δ) n))
    (gridLower≤ᶜ a₁ δ n)
    n
  tail =
    rationalStepGrid a₁ δ n
rationalStepGridAdjacentClose a δ (suc n) (Fin.suc i) =
  rationalStepGridAdjacentClose a₁ δ n i
  where
  a₁ : ℚ
  a₁ = Rational.grid a (radius δ) (suc zero)


rationalStepGridWithRight :
  (a b : ℚ) →
  (δ : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid a (radius δ) n ≡ b) →
  Grid
    (rational a)
    (rational b)
    (gridLowerWithRight≤ᶜ a b δ n right-path)
    n
rationalStepGridWithRight a b δ n right-path =
  make-grid point (Grid.left-point base-grid) right-point
  where
  base-grid :
    Grid
      (rational a)
      (rational (Rational.grid a (radius δ) n))
      (gridLower≤ᶜ a δ n)
      n
  base-grid =
    rationalStepGrid a δ n

  upper-path :
    rational (Rational.grid a (radius δ) n) ≡ rational b
  upper-path =
    cong rational right-path

  basePoint :
    Fin (suc n) →
    [ rational a , rational (Rational.grid a (radius δ) n) ]ᶜ
  basePoint =
    Grid.point base-grid

  point :
    Fin (suc n) →
    [ rational a , rational b ]ᶜ
  point i =
    pointᶜ
      {a = rational a}
      {b = rational (Rational.grid a (radius δ) n)}
      (basePoint i) ,
    lowerBoundᶜ
      {a = rational a}
      {b = rational (Rational.grid a (radius δ) n)}
      (basePoint i) ,
    subst
      (pointᶜ
        {a = rational a}
        {b = rational (Rational.grid a (radius δ) n)}
        (basePoint i) ≤ᶜ_)
      upper-path
      (upperBoundᶜ
        {a = rational a}
        {b = rational (Rational.grid a (radius δ) n)}
        (basePoint i))

  right-point :
    pointᶜ
      {a = rational a}
      {b = rational b}
      (point (Fin.fromℕ n)) ≡
    rational b
  right-point =
    Grid.right-point base-grid ∙ upper-path


rationalStepGridPointPath :
  (a : ℚ) →
  (δ : ℚ⁺) →
  (n : ℕ) →
  (i : Fin (suc n)) →
  pointᶜ
    {a = rational a}
    {b = rational (Rational.grid a (radius δ) n)}
    (Grid.point (rationalStepGrid a δ n) i) ≡
  rational (Rational.grid a (radius δ) (Fin.toℕ i))
rationalStepGridPointPath a δ zero Fin.zero =
  cong rational (sym (Rational.grid-zero a (radius δ)))
rationalStepGridPointPath a δ (suc n) Fin.zero =
  cong rational (sym (Rational.grid-zero a (radius δ)))
rationalStepGridPointPath a δ (suc n) (Fin.suc i) =
  rationalStepGridPointPath a₁ δ n i ∙
  cong rational (grid-shift a δ (Fin.toℕ i))
  where
  a₁ : ℚ
  a₁ =
    Rational.grid a (radius δ) (suc zero)


rationalStepGridWithRightPointPath :
  (a b : ℚ) →
  (δ : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid a (radius δ) n ≡ b) →
  (i : Fin (suc n)) →
  pointᶜ
    {a = rational a}
    {b = rational b}
    (Grid.point (rationalStepGridWithRight a b δ n right-path) i) ≡
  rational (Rational.grid a (radius δ) (Fin.toℕ i))
rationalStepGridWithRightPointPath a b δ n right-path i =
  rationalStepGridPointPath a δ n i


rationalStepGridAdjacentCloseℚ :
  (a : ℚ) →
  (δ : ℚ⁺) →
  (n : ℕ) →
  (i : Fin n) →
  Closeℚ
    (Rational.grid a (radius δ) (Fin.toℕ (Fin.weakenFin i)))
    (δ +⁺ δ)
    (Rational.grid a (radius δ) (Fin.toℕ (Fin.suc i)))
rationalStepGridAdjacentCloseℚ a δ zero ()
rationalStepGridAdjacentCloseℚ a δ (suc n) Fin.zero =
  subst2
    (λ q r → Closeℚ q (δ +⁺ δ) r)
    (sym (Rational.grid-zero a (radius δ)))
    (sym (grid-one a (radius δ)))
    (step-closeℚ a δ)
rationalStepGridAdjacentCloseℚ a δ (suc n) (Fin.suc i) =
  subst2
    (λ q r → Closeℚ q (δ +⁺ δ) r)
    (grid-shift a δ (Fin.toℕ (Fin.weakenFin i)))
    (grid-shift a δ (Fin.toℕ (Fin.suc i)))
    (rationalStepGridAdjacentCloseℚ a₁ δ n i)
  where
  a₁ : ℚ
  a₁ =
    Rational.grid a (radius δ) (suc zero)


rationalStepGridWithRightAdjacentClose :
  (a b : ℚ) →
  (δ : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid a (radius δ) n ≡ b) →
  AdjacentClose
    (rationalStepGridWithRight a b δ n right-path)
    (δ +⁺ δ)
rationalStepGridWithRightAdjacentClose a b δ n right-path =
  rationalStepGridAdjacentClose a δ n


rationalStepGridWithRightAdjacentCloseℚ :
  (a b : ℚ) →
  (δ : ℚ⁺) →
  (n : ℕ) →
  (right-path : Rational.grid a (radius δ) n ≡ b) →
  (i : Fin n) →
  Closeℚ
    (Rational.grid a (radius δ) (Fin.toℕ (Fin.weakenFin i)))
    (δ +⁺ δ)
    (Rational.grid a (radius δ) (Fin.toℕ (Fin.suc i)))
rationalStepGridWithRightAdjacentCloseℚ a b δ n right-path =
  rationalStepGridAdjacentCloseℚ a δ n


rationalExactStep :
  (a b : ℚ) →
  a ℚOrder.< b →
  ℕ →
  ℚ⁺
rationalExactStep a b a<b n =
  Rational.divideBySuc (b ℚ.- a) n ,
  Rational.divideBySuc-positive
    {q = b ℚ.- a}
    (Rational.diff-positive {p = a} {q = b} a<b)
    n


rationalExactStepRight :
  (a b : ℚ) →
  (a<b : a ℚOrder.< b) →
  (n : ℕ) →
  Rational.grid a (radius (rationalExactStep a b a<b n)) (suc n) ≡ b
rationalExactStepRight a b a<b n =
  cong (a ℚ.+_) (Rational.natMul-divideBySuc (b ℚ.- a) n) ∙
  Rational.p+[q-p]≡q a b


rationalExactStepGridData :
  (a b : ℚ) →
  (a<b : a ℚOrder.< b) →
  (mesh : ℚ⁺) →
  Σ[ n ∈ ℕ ]
    (Rational.grid a (radius (rationalExactStep a b a<b n)) (suc n) ≡ b) ×
    (rationalExactStep a b a<b n +⁺ rationalExactStep a b a<b n <⁺ mesh)
rationalExactStepGridData a b a<b mesh =
  n , rationalExactStepRight a b a<b n , step+step<mesh
  where
  gap : ℚ
  gap =
    b ℚ.- a

  0<gap : Rational.0ℚ ℚOrder.< gap
  0<gap =
    Rational.diff-positive {p = a} {q = b} a<b

  doubleGap : ℚ
  doubleGap =
    gap ℚ.+ gap

  0<doubleGap : Rational.0ℚ ℚOrder.< doubleGap
  0<doubleGap =
    Rational.positive-sum {p = gap} {q = gap} 0<gap 0<gap

  scale : ℚ
  scale =
    Rational.scaleByPositive (radius mesh) doubleGap 0<doubleGap

  0<scale : Rational.0ℚ ℚOrder.< scale
  0<scale =
    Rational.scaleByPositive-positive
      {ε = radius mesh}
      {M = doubleGap}
      (mesh .snd)
      0<doubleGap

  search : Σ[ k ∈ ℕ ] Rational.unitFraction k ℚOrder.< scale
  search =
    Rational.archimedean-unit-fraction scale 0<scale

  n : ℕ
  n =
    search .fst

  unit<scale : Rational.unitFraction n ℚOrder.< scale
  unit<scale =
    search .snd

  scaledUnit<mesh :
    doubleGap ℚ.· Rational.unitFraction n ℚOrder.< radius mesh
  scaledUnit<mesh =
    subst
      (doubleGap ℚ.· Rational.unitFraction n ℚOrder.<_)
      (Rational.scaleByPositive-cancelL (radius mesh) doubleGap 0<doubleGap)
      (Rational.mul-left-positive-< {a = doubleGap}
        {b = Rational.unitFraction n}
        {c = scale}
        0<doubleGap
        unit<scale)

  stepRadiusPath :
    radius (rationalExactStep a b a<b n) ≡
    gap ℚ.· Rational.unitFraction n
  stepRadiusPath =
    Rational.divideBySuc-as-unitFraction gap n

  doubleStepPath :
    radius (rationalExactStep a b a<b n +⁺ rationalExactStep a b a<b n) ≡
    doubleGap ℚ.· Rational.unitFraction n
  doubleStepPath =
    cong₂ ℚ._+_ stepRadiusPath stepRadiusPath ∙
    sym (ℚ.·DistR+ gap gap (Rational.unitFraction n))

  step+step<mesh :
    rationalExactStep a b a<b n +⁺ rationalExactStep a b a<b n <⁺ mesh
  step+step<mesh =
    subst
      (λ q → q ℚOrder.< radius mesh)
      (sym doubleStepPath)
      scaledUnit<mesh
