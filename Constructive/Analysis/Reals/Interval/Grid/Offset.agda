{-

Rational offset grids for bounded closed intervals

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Interval.Grid.Offset where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Metric.Base
import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Lattice
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Density
open import Constructive.Analysis.Reals.CauchyReals.Order.Properties
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
  using (≤ᶜ→diffᶜ-nonnegative)
open import Constructive.Analysis.Reals.Interval.Base
open import Constructive.Analysis.Reals.Interval.Grid.Base
open import Constructive.Analysis.Reals.Interval.Grid.Cover
open import Constructive.Analysis.Reals.Interval.Grid.Rational
  using (rationalExactStep ; rationalExactStepGridData)
open import Constructive.Analysis.Reals.Interval.Order
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals.Archimedean as RationalArch
import Constructive.Data.Rationals.Base as RationalBase
import Constructive.Data.Rationals.Bounds as RationalBounds
import Constructive.Data.Rationals.Grid as RationalGrid


private
  radius-+⁺ :
    (ε δ : ℚ⁺) →
    radius (ε +⁺ δ) ≡ radius ε ℚ.+ radius δ
  radius-+⁺ ε δ =
    refl

  step+step-positive :
    (step : ℚ⁺) →
    RationalBase.0ℚ ℚOrder.< radius (step +⁺ step)
  step+step-positive step =
    RationalBase.positive-sum {p = radius step} {q = radius step}
      (step .snd)
      (step .snd)

  step<step+step :
    (step : ℚ⁺) →
    radius step ℚOrder.< radius (step +⁺ step)
  step<step+step step =
    RationalBase.q<q+positive (radius step) (radius step) (step .snd)

  zero-close-from-upper :
    (step : ℚ⁺) →
    (q : ℚ.ℚ) →
    RationalBase.0ℚ ℚOrder.≤ q →
    q ℚOrder.≤ radius step →
    Closeℚ RationalBase.0ℚ (step +⁺ step) q
  zero-close-from-upper step q 0≤q q≤step =
    0-q<step+step ,
    q-0<step+step
    where
    -q≤0 : ℚ.- q ℚOrder.≤ RationalBase.0ℚ
    -q≤0 =
      RationalBase.neg-nonpositive 0≤q

    0-q<step+step :
      RationalBase.0ℚ ℚ.- q ℚOrder.< radius (step +⁺ step)
    0-q<step+step =
      subst
        (λ r → r ℚOrder.< radius (step +⁺ step))
        (sym (ℚ.+IdL (ℚ.- q)))
        (RationalBase.≤<-trans -q≤0 (step+step-positive step))

    q<step+step : q ℚOrder.< radius (step +⁺ step)
    q<step+step =
      RationalBase.≤<-trans q≤step (step<step+step step)

    q-0<step+step :
      q ℚ.- RationalBase.0ℚ ℚOrder.< radius (step +⁺ step)
    q-0<step+step =
      subst
        (λ r → r ℚOrder.< radius (step +⁺ step))
        (sym (cong (q ℚ.+_) RationalBase.neg-zero ∙ ℚ.+IdR q))
        q<step+step

  grid-sub-step-path :
    (step : ℚ⁺) →
    (n : ℕ) →
    RationalGrid.grid RationalBase.0ℚ (radius step) (suc n) ℚ.- radius step ≡
    RationalGrid.grid RationalBase.0ℚ (radius step) n
  grid-sub-step-path step n =
    cong (λ r → r ℚ.- radius step)
      (RationalGrid.grid-suc RationalBase.0ℚ (radius step) n) ∙
    RationalBase.[p+q]-q≡p
      (RationalGrid.grid RationalBase.0ℚ (radius step) n)
      (radius step)

  rationalStepGridCovers :
    (step : ℚ⁺) →
    (n : ℕ) →
    (q : ℚ.ℚ) →
    RationalBase.0ℚ ℚOrder.≤ q →
    q ℚOrder.≤ RationalGrid.grid RationalBase.0ℚ (radius step) n →
    ∥ Σ[ i ∈ Fin (suc n) ]
        Closeℚ
          (RationalGrid.grid RationalBase.0ℚ (radius step) (Fin.toℕ i))
          (step +⁺ step)
          q ∥₁
  rationalStepGridCovers step zero q 0≤q q≤last =
    ∣ Fin.zero ,
      subst
        (λ r →
          Closeℚ
            (RationalGrid.grid RationalBase.0ℚ (radius step) (Fin.toℕ Fin.zero))
            (step +⁺ step)
            r)
        (sym q≡0)
        (subst
          (λ r → Closeℚ r (step +⁺ step) RationalBase.0ℚ)
          (sym (RationalGrid.grid-zero RationalBase.0ℚ (radius step)))
          (rational-close-refl RationalBase.0ℚ (step +⁺ step)))
    ∣₁
    where
    q≤0 : q ℚOrder.≤ RationalBase.0ℚ
    q≤0 =
      subst
        (q ℚOrder.≤_)
        (RationalGrid.grid-zero RationalBase.0ℚ (radius step))
        q≤last

    q≡0 : q ≡ RationalBase.0ℚ
    q≡0 =
      ℚOrder.isAntisym≤ q RationalBase.0ℚ q≤0 0≤q
  rationalStepGridCovers step (suc n) q 0≤q q≤last with q ℚOrder.≟ radius step
  ... | ℚOrder.lt q<step =
    ∣ Fin.zero ,
      subst
        (λ r → Closeℚ r (step +⁺ step) q)
        (sym (RationalGrid.grid-zero RationalBase.0ℚ (radius step)))
        (zero-close-from-upper
          step
          q
          0≤q
          (RationalBase.<→≤ q<step))
    ∣₁
  ... | ℚOrder.eq q≡step =
    ∣ Fin.zero ,
      subst
        (λ r → Closeℚ r (step +⁺ step) q)
        (sym (RationalGrid.grid-zero RationalBase.0ℚ (radius step)))
        (zero-close-from-upper
          step
          q
          0≤q
          (ℚOrder.≡Weaken≤ q (radius step) q≡step))
    ∣₁
  ... | ℚOrder.gt step<q =
    Prop.map stepCover
      (rationalStepGridCovers step n q-step 0≤q-step q-step≤last)
    where
    q-step : ℚ.ℚ
    q-step =
      q ℚ.- radius step

    0<q-step : RationalBase.0ℚ ℚOrder.< q-step
    0<q-step =
      RationalBase.diff-positive {p = radius step} {q = q} step<q

    0≤q-step : RationalBase.0ℚ ℚOrder.≤ q-step
    0≤q-step =
      RationalBase.<→≤ {p = RationalBase.0ℚ} {q = q-step} 0<q-step

    q-step≤last :
      q-step ℚOrder.≤ RationalGrid.grid RationalBase.0ℚ (radius step) n
    q-step≤last =
      subst
        (q-step ℚOrder.≤_)
        (grid-sub-step-path step n)
        (ℚOrder.≤-+o
          q
          (RationalGrid.grid RationalBase.0ℚ (radius step) (suc n))
          (ℚ.- radius step)
          q≤last)

    stepCover :
      Σ[ i ∈ Fin (suc n) ]
        Closeℚ
          (RationalGrid.grid RationalBase.0ℚ (radius step) (Fin.toℕ i))
          (step +⁺ step)
          q-step →
      Σ[ i ∈ Fin (suc (suc n)) ]
        Closeℚ
          (RationalGrid.grid RationalBase.0ℚ (radius step) (Fin.toℕ i))
          (step +⁺ step)
          q
    stepCover (i , grid∼q-step) =
      Fin.suc i ,
      subst2
        (λ r s → Closeℚ r (step +⁺ step) s)
        (sym (RationalGrid.grid-suc RationalBase.0ℚ (radius step) (Fin.toℕ i)))
        (RationalBase.[p-q]+q≡p q (radius step))
        (rational-close-translate
          (RationalGrid.grid RationalBase.0ℚ (radius step) (Fin.toℕ i))
          q-step
          (radius step)
          (step +⁺ step)
          grid∼q-step)

  clampℚ :
    ℚ⁺ →
    ℚ.ℚ →
    ℚ.ℚ
  clampℚ κ q =
    ℚ.max RationalBase.0ℚ (ℚ.min q (radius κ))

  clampℚ-lower :
    (κ : ℚ⁺) →
    (q : ℚ.ℚ) →
    RationalBase.0ℚ ℚOrder.≤ clampℚ κ q
  clampℚ-lower κ q =
    ℚOrder.≤max RationalBase.0ℚ (ℚ.min q (radius κ))

  clampℚ-upper :
    (κ : ℚ⁺) →
    (q : ℚ.ℚ) →
    clampℚ κ q ℚOrder.≤ radius κ
  clampℚ-upper κ q =
    subst
      (clampℚ κ q ℚOrder.≤_)
      (ℚ.maxIdem (radius κ))
      (ℚOrder.≤MonotoneMax
        RationalBase.0ℚ
        (radius κ)
        (ℚ.min q (radius κ))
        (radius κ)
        (RationalBase.<→≤ {p = RationalBase.0ℚ} {q = radius κ} (κ .snd))
        (RationalBounds.min≤r q (radius κ)))

  clampᶜ :
    ℚ⁺ →
    ℝᶜ →
    ℝᶜ
  clampᶜ κ x =
    0ᶜ ⊔ᶜ (x ⊓ᶜ rational (radius κ))

  clampᶜ-rational :
    (κ : ℚ⁺) →
    (q : ℚ.ℚ) →
    clampᶜ κ (rational q) ≡ rational (clampℚ κ q)
  clampᶜ-rational κ q =
    cong (0ᶜ ⊔ᶜ_) (min-rational q (radius κ)) ∙
    max-rational RationalBase.0ℚ (ℚ.min q (radius κ))

  clampᶜ-fixed :
    (κ : ℚ⁺) →
    (x : ℝᶜ) →
    0ᶜ ≤ᶜ x →
    x ≤ᶜ rational (radius κ) →
    clampᶜ κ x ≡ x
  clampᶜ-fixed κ x 0≤x x≤κ =
    cong (0ᶜ ⊔ᶜ_) x≤κ ∙
    ≤ᶜ→maxᶜ 0≤x

  clampᶜ-close :
    (κ : ℚ⁺) →
    {x y : ℝᶜ} {η : ℚ⁺} →
    x ∼[ η ] y →
    clampᶜ κ x ∼[ η ] clampᶜ κ y
  clampᶜ-close κ x∼y =
    max-close-right
      0ᶜ
      (min-close-left x∼y (rational (radius κ)))


offsetPointᶜ :
  (a b : ℝᶜ) →
  ℚ.ℚ →
  ℝᶜ
offsetPointᶜ a b q =
  (a +ᶜ rational q) ⊓ᶜ b


offsetPoint :
  (a b : ℝᶜ) →
  (a≤b : a ≤ᶜ b) →
  (q : ℚ.ℚ) →
  RationalBase.0ℚ ℚOrder.≤ q →
  [ a , b ]ᶜ
offsetPoint a b a≤b q 0≤q =
  offsetPointᶜ a b q ,
  ≤ᶜ⊓ᶜ
    {x = a +ᶜ rational q}
    {y = b}
    {z = a}
    a≤a+q
    a≤b ,
  ⊓ᶜ≤right (a +ᶜ rational q) b
  where
  a≤a+q : a ≤ᶜ (a +ᶜ rational q)
  a≤a+q =
    subst
      (_≤ᶜ (a +ᶜ rational q))
      (add-zero-right a)
      (addᶜ-pres≤ᶜ-left
        {x = 0ᶜ}
        {y = rational q}
        a
        (≤ℚ→rational≤ᶜ 0≤q))


offsetPointZero :
  (a b : ℝᶜ) →
  (a≤b : a ≤ᶜ b) →
  offsetPointᶜ a b RationalBase.0ℚ ≡ a
offsetPointZero a b a≤b =
  cong (_⊓ᶜ b) (add-zero-right a) ∙
  a≤b


offsetPointRight :
  (a b : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (gapᶜ a b) →
  offsetPointᶜ a b (radius κ) ≡ b
offsetPointRight a b κ gap-bound =
  min-comm (a +ᶜ rational (radius κ)) b ∙
  b≤a+κ
  where
  b≤a+κ : b ≤ᶜ (a +ᶜ rational (radius κ))
  b≤a+κ =
    subst
      (_≤ᶜ (a +ᶜ rational (radius κ)))
      (leftPlusGapᶜ a b)
      (addᶜ-pres≤ᶜ-left
        {x = gapᶜ a b}
        {y = rational (radius κ)}
        a
        (upperᶜ gap-bound))


boundedOffsetGridWithRight :
  (a b : ℝᶜ) →
  (a≤b : a ≤ᶜ b) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (gapᶜ a b) →
  (step : ℚ⁺) →
  (n : ℕ) →
  RationalGrid.grid RationalBase.0ℚ (radius step) n ≡ radius κ →
  Grid a b a≤b n
boundedOffsetGridWithRight a b a≤b κ gap-bound step n right-path =
  make-grid point left-path right-pathᶜ
  where
  coeff : Fin (suc n) → ℚ.ℚ
  coeff i =
    RationalGrid.grid RationalBase.0ℚ (radius step) (Fin.toℕ i)

  coeff-lower :
    (i : Fin (suc n)) →
    RationalBase.0ℚ ℚOrder.≤ coeff i
  coeff-lower i =
    RationalBase.q≤q+nonnegative
      RationalBase.0ℚ
      (RationalArch.natMul (Fin.toℕ i) (radius step))
      (RationalArch.natMul-nonnegative (Fin.toℕ i) (step .snd))

  point : Fin (suc n) → [ a , b ]ᶜ
  point i =
    offsetPoint a b a≤b (coeff i) (coeff-lower i)

  left-path :
    pointᶜ {a = a} {b = b} (point Fin.zero) ≡ a
  left-path =
    cong (offsetPointᶜ a b)
      (RationalGrid.grid-zero RationalBase.0ℚ (radius step)) ∙
    offsetPointZero a b a≤b

  right-coeff-path :
    coeff (Fin.fromℕ n) ≡ radius κ
  right-coeff-path =
    subst
      (λ k → RationalGrid.grid RationalBase.0ℚ (radius step) k ≡ radius κ)
      (sym (Fin.toFromId n))
      right-path

  right-pathᶜ :
    pointᶜ {a = a} {b = b} (point (Fin.fromℕ n)) ≡ b
  right-pathᶜ =
    cong (offsetPointᶜ a b) right-coeff-path ∙
    offsetPointRight a b κ gap-bound


boundedOffsetGridData :
  (a b : ℝᶜ) →
  (a≤b : a ≤ᶜ b) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (gapᶜ a b) →
  (mesh : ℚ⁺) →
  Σ[ n ∈ ℕ ] Grid a b a≤b (suc n)
boundedOffsetGridData a b a≤b κ gap-bound mesh =
  n , boundedOffsetGridWithRight a b a≤b κ gap-bound step (suc n) right-path
  where
  stepData :
    Σ[ k ∈ ℕ ]
      (RationalGrid.grid RationalBase.0ℚ
        (radius (rationalExactStep RationalBase.0ℚ (radius κ) (κ .snd) k))
        (suc k) ≡ radius κ) ×
      (rationalExactStep RationalBase.0ℚ (radius κ) (κ .snd) k +⁺
       rationalExactStep RationalBase.0ℚ (radius κ) (κ .snd) k <⁺ mesh)
  stepData =
    rationalExactStepGridData RationalBase.0ℚ (radius κ) (κ .snd) mesh

  n : ℕ
  n =
    stepData .fst

  step : ℚ⁺
  step =
    rationalExactStep RationalBase.0ℚ (radius κ) (κ .snd) n

  right-path :
    RationalGrid.grid RationalBase.0ℚ (radius step) (suc n) ≡ radius κ
  right-path =
    stepData .snd .fst


offset-diffᶜ :
  (a x : ℝᶜ) →
  ℝᶜ
offset-diffᶜ a x =
  x +ᶜ (-ᶜ a)


leftPlusOffsetDiffᶜ :
  (a x : ℝᶜ) →
  a +ᶜ offset-diffᶜ a x ≡ x
leftPlusOffsetDiffᶜ a x =
  add-comm a (offset-diffᶜ a x) ∙
  minus-plus-cancel-right x a


offsetPointClose :
  {a b : ℝᶜ} →
  (a≤b : a ≤ᶜ b) →
  (x : [ a , b ]ᶜ) →
  (q : ℚ.ℚ) →
  (0≤q : RationalBase.0ℚ ℚOrder.≤ q) →
  (η : ℚ⁺) →
  MetricSpace.Close
    CauchyRealsMetricSpace
    (rational q)
    η
    (offset-diffᶜ a (pointᶜ {a = a} {b = b} x)) →
  MetricSpace.Close
    (IntervalMetric a b)
    (offsetPoint a b a≤b q 0≤q)
    η
    x
offsetPointClose {a = a} {b = b} a≤b x q 0≤q η q∼x-a =
  subst
    (MetricSpace.Close CauchyRealsMetricSpace (offsetPointᶜ a b q) η)
    (upperBoundᶜ {a = a} {b = b} x)
    (min-close-left a+q∼x b)
  where
  a+q∼x :
    MetricSpace.Close
      CauchyRealsMetricSpace
      (a +ᶜ rational q)
      η
      (pointᶜ {a = a} {b = b} x)
  a+q∼x =
    subst
      (MetricSpace.Close CauchyRealsMetricSpace (a +ᶜ rational q) η)
      (leftPlusOffsetDiffᶜ a (pointᶜ {a = a} {b = b} x))
      (add-close-right a q∼x-a)


boundedOffsetGridCoversFromRationalCover :
  (a b : ℝᶜ) →
  (a≤b : a ≤ᶜ b) →
  (κ : ℚ⁺) →
  (gap-bound : BoundedByᶜ κ (gapᶜ a b)) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (right-path : RationalGrid.grid RationalBase.0ℚ (radius step) n ≡ radius κ) →
  (η ν ε : ℚ⁺) →
  radius (ν +⁺ η) ℚOrder.≤ radius ε →
  ((x : [ a , b ]ᶜ) →
   (q : ℚ.ℚ) →
   MetricSpace.Close
     CauchyRealsMetricSpace
     (offset-diffᶜ a (pointᶜ {a = a} {b = b} x))
     η
     (rational q) →
   ∥ Σ[ i ∈ Fin (suc n) ]
       Closeℚ
         (RationalGrid.grid RationalBase.0ℚ (radius step) (Fin.toℕ i))
         ν
         q ∥₁) →
  GridCovers
    (boundedOffsetGridWithRight a b a≤b κ gap-bound step n right-path)
    ε
boundedOffsetGridCoversFromRationalCover
    a b a≤b κ gap-bound step n right-path η ν ε ν+η≤ε rationalCover x =
  Prop.rec squash₁ approximateStep
    (rational-approximation (offset-diffᶜ a (pointᶜ {a = a} {b = b} x)) η)
  where
  G : Grid a b a≤b n
  G =
    boundedOffsetGridWithRight a b a≤b κ gap-bound step n right-path

  coeff : Fin (suc n) → ℚ.ℚ
  coeff i =
    RationalGrid.grid RationalBase.0ℚ (radius step) (Fin.toℕ i)

  coeff-lower :
    (i : Fin (suc n)) →
    RationalBase.0ℚ ℚOrder.≤ coeff i
  coeff-lower i =
    RationalBase.q≤q+nonnegative
      RationalBase.0ℚ
      (RationalArch.natMul (Fin.toℕ i) (radius step))
      (RationalArch.natMul-nonnegative (Fin.toℕ i) (step .snd))

  coverStep :
    (q : ℚ.ℚ) →
    MetricSpace.Close
      CauchyRealsMetricSpace
      (offset-diffᶜ a (pointᶜ {a = a} {b = b} x))
      η
      (rational q) →
    Σ[ i ∈ Fin (suc n) ] Closeℚ (coeff i) ν q →
    Σ[ i ∈ Fin (suc n) ]
      MetricSpace.Close
        (IntervalMetric a b)
        (Grid.point G i)
        ε
        x
  coverStep q x-a∼q (i , coeff∼q) =
    i ,
    MetricCauchy.close-mono-≤
      (IntervalMetric a b)
      ν+η≤ε
      (offsetPointClose
        a≤b
        x
        (coeff i)
        (coeff-lower i)
        (ν +⁺ η)
        coeff∼x-a)
    where
    coeff∼qᶜ :
      MetricSpace.Close CauchyRealsMetricSpace (rational (coeff i)) ν (rational q)
    coeff∼qᶜ =
      point-point-close (coeff i) q ν coeff∼q

    q∼x-a :
      MetricSpace.Close
        CauchyRealsMetricSpace
        (rational q)
        η
        (offset-diffᶜ a (pointᶜ {a = a} {b = b} x))
    q∼x-a =
      MetricSpace.close-sym CauchyRealsMetricSpace x-a∼q

    coeff∼x-a :
      MetricSpace.Close
        CauchyRealsMetricSpace
        (rational (coeff i))
        (ν +⁺ η)
        (offset-diffᶜ a (pointᶜ {a = a} {b = b} x))
    coeff∼x-a =
      MetricSpace.close-triangle CauchyRealsMetricSpace coeff∼qᶜ q∼x-a

  approximateStep :
    Σ[ q ∈ ℚ.ℚ ]
      MetricSpace.Close
        CauchyRealsMetricSpace
        (offset-diffᶜ a (pointᶜ {a = a} {b = b} x))
        η
        (rational q) →
    ∥ Σ[ i ∈ Fin (suc n) ]
        MetricSpace.Close
          (IntervalMetric a b)
          (Grid.point G i)
          ε
          x ∥₁
  approximateStep (q , x-a∼q) =
    Prop.map
      (coverStep q x-a∼q)
      (rationalCover x q x-a∼q)


BoundedOffsetApproximation :
  {a b : ℝᶜ} →
  (κ : ℚ⁺) →
  [ a , b ]ᶜ →
  ℚ⁺ →
  Type₀
BoundedOffsetApproximation {a = a} {b = b} κ x η =
  Σ[ q ∈ ℚ.ℚ ]
    (MetricSpace.Close
      CauchyRealsMetricSpace
      (offset-diffᶜ a (pointᶜ {a = a} {b = b} x))
      η
      (rational q))
    ×
    (RationalBase.0ℚ ℚOrder.≤ q)
    ×
    (q ℚOrder.≤ radius κ)


boundedOffsetApproximations :
  {a b : ℝᶜ} →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (gapᶜ a b) →
  (η : ℚ⁺) →
  (x : [ a , b ]ᶜ) →
  ∥ BoundedOffsetApproximation κ x η ∥₁
boundedOffsetApproximations {a = a} {b = b} κ gap-bound η x =
  Prop.map approximateStep
    (rational-approximation (offset-diffᶜ a (pointᶜ {a = a} {b = b} x)) η)
  where
  y : ℝᶜ
  y =
    offset-diffᶜ a (pointᶜ {a = a} {b = b} x)

  0≤y : 0ᶜ ≤ᶜ y
  0≤y =
    ≤ᶜ→diffᶜ-nonnegative (lowerBoundᶜ {a = a} {b = b} x)

  y≤κ : y ≤ᶜ rational (radius κ)
  y≤κ =
    ≤ᶜ-trans y≤gap (upperᶜ gap-bound)
    where
    y≤gap : y ≤ᶜ gapᶜ a b
    y≤gap =
      addᶜ-pres≤ᶜ-right
        (-ᶜ a)
        (upperBoundᶜ {a = a} {b = b} x)

  y-fixed : clampᶜ κ y ≡ y
  y-fixed =
    clampᶜ-fixed κ y 0≤y y≤κ

  approximateStep :
    Σ[ q ∈ ℚ.ℚ ] y ∼[ η ] rational q →
    BoundedOffsetApproximation κ x η
  approximateStep (q , y∼q) =
    clampℚ κ q ,
    subst2
      (λ u v → u ∼[ η ] v)
      y-fixed
      (clampᶜ-rational κ q)
      (clampᶜ-close κ y∼q) ,
    clampℚ-lower κ q ,
    clampℚ-upper κ q


boundedOffsetGridCoversFromBoundedApproximations :
  (a b : ℝᶜ) →
  (a≤b : a ≤ᶜ b) →
  (κ : ℚ⁺) →
  (gap-bound : BoundedByᶜ κ (gapᶜ a b)) →
  (step : ℚ⁺) →
  (n : ℕ) →
  (right-path : RationalGrid.grid RationalBase.0ℚ (radius step) n ≡ radius κ) →
  (η ε : ℚ⁺) →
  radius ((step +⁺ step) +⁺ η) ℚOrder.≤ radius ε →
  ((x : [ a , b ]ᶜ) → ∥ BoundedOffsetApproximation κ x η ∥₁) →
  GridCovers
    (boundedOffsetGridWithRight a b a≤b κ gap-bound step n right-path)
    ε
boundedOffsetGridCoversFromBoundedApproximations
    a b a≤b κ gap-bound step n right-path η ε step+step+η≤ε approximates x =
  Prop.rec squash₁ approximateStep (approximates x)
  where
  G : Grid a b a≤b n
  G =
    boundedOffsetGridWithRight a b a≤b κ gap-bound step n right-path

  coeff : Fin (suc n) → ℚ.ℚ
  coeff i =
    RationalGrid.grid RationalBase.0ℚ (radius step) (Fin.toℕ i)

  coeff-lower :
    (i : Fin (suc n)) →
    RationalBase.0ℚ ℚOrder.≤ coeff i
  coeff-lower i =
    RationalBase.q≤q+nonnegative
      RationalBase.0ℚ
      (RationalArch.natMul (Fin.toℕ i) (radius step))
      (RationalArch.natMul-nonnegative (Fin.toℕ i) (step .snd))

  coverStep :
    (q : ℚ.ℚ) →
    MetricSpace.Close
      CauchyRealsMetricSpace
      (offset-diffᶜ a (pointᶜ {a = a} {b = b} x))
      η
      (rational q) →
    Σ[ i ∈ Fin (suc n) ] Closeℚ (coeff i) (step +⁺ step) q →
    Σ[ i ∈ Fin (suc n) ]
      MetricSpace.Close
        (IntervalMetric a b)
        (Grid.point G i)
        ε
        x
  coverStep q x-a∼q (i , coeff∼q) =
    i ,
    MetricCauchy.close-mono-≤
      (IntervalMetric a b)
      step+step+η≤ε
      (offsetPointClose
        a≤b
        x
        (coeff i)
        (coeff-lower i)
        ((step +⁺ step) +⁺ η)
        coeff∼x-a)
    where
    coeff∼qᶜ :
      MetricSpace.Close
        CauchyRealsMetricSpace
        (rational (coeff i))
        (step +⁺ step)
        (rational q)
    coeff∼qᶜ =
      point-point-close (coeff i) q (step +⁺ step) coeff∼q

    q∼x-a :
      MetricSpace.Close
        CauchyRealsMetricSpace
        (rational q)
        η
        (offset-diffᶜ a (pointᶜ {a = a} {b = b} x))
    q∼x-a =
      MetricSpace.close-sym CauchyRealsMetricSpace x-a∼q

    coeff∼x-a :
      MetricSpace.Close
        CauchyRealsMetricSpace
        (rational (coeff i))
        ((step +⁺ step) +⁺ η)
        (offset-diffᶜ a (pointᶜ {a = a} {b = b} x))
    coeff∼x-a =
      MetricSpace.close-triangle CauchyRealsMetricSpace coeff∼qᶜ q∼x-a

  approximateStep :
    BoundedOffsetApproximation κ x η →
    ∥ Σ[ i ∈ Fin (suc n) ]
        MetricSpace.Close
          (IntervalMetric a b)
          (Grid.point G i)
          ε
          x ∥₁
  approximateStep (q , x-a∼q , 0≤q , q≤κ) =
    Prop.map
      (coverStep q x-a∼q)
      (rationalStepGridCovers step n q 0≤q q≤last)
    where
    q≤last :
      q ℚOrder.≤ RationalGrid.grid RationalBase.0ℚ (radius step) n
    q≤last =
      subst
        (q ℚOrder.≤_)
        (sym right-path)
        q≤κ


boundedOffsetGridCoverData :
  {a b : ℝᶜ} →
  (a≤b : a ≤ᶜ b) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (gapᶜ a b) →
  (ε : ℚ⁺) →
  Σ[ n ∈ ℕ ] Σ[ G ∈ Grid a b a≤b n ] GridCovers G ε
boundedOffsetGridCoverData {a = a} {b = b} a≤b κ gap-bound ε =
  suc n ,
  G ,
  boundedOffsetGridCoversFromBoundedApproximations
    a
    b
    a≤b
    κ
    gap-bound
    step
    (suc n)
    right-path
    η
    ε
    step+step+η≤ε
    (boundedOffsetApproximations κ gap-bound η)
  where
  mesh η : ℚ⁺
  mesh =
    half⁺ ε
  η =
    half⁺ ε

  stepData :
    Σ[ k ∈ ℕ ]
      (RationalGrid.grid RationalBase.0ℚ
        (radius (rationalExactStep RationalBase.0ℚ (radius κ) (κ .snd) k))
        (suc k) ≡ radius κ) ×
      (rationalExactStep RationalBase.0ℚ (radius κ) (κ .snd) k +⁺
       rationalExactStep RationalBase.0ℚ (radius κ) (κ .snd) k <⁺ mesh)
  stepData =
    rationalExactStepGridData RationalBase.0ℚ (radius κ) (κ .snd) mesh

  n : ℕ
  n =
    stepData .fst

  step : ℚ⁺
  step =
    rationalExactStep RationalBase.0ℚ (radius κ) (κ .snd) n

  right-path :
    RationalGrid.grid RationalBase.0ℚ (radius step) (suc n) ≡ radius κ
  right-path =
    stepData .snd .fst

  step+step<mesh : step +⁺ step <⁺ mesh
  step+step<mesh =
    stepData .snd .snd

  G : Grid a b a≤b (suc n)
  G =
    boundedOffsetGridWithRight
      a
      b
      a≤b
      κ
      gap-bound
      step
      (suc n)
      right-path

  step+step+η<mesh+η :
    radius ((step +⁺ step) +⁺ η) ℚOrder.< radius (mesh +⁺ η)
  step+step+η<mesh+η =
    subst2
      ℚOrder._<_
      (sym (radius-+⁺ (step +⁺ step) η))
      (sym (radius-+⁺ mesh η))
      (ℚOrder.<-+o
        (radius (step +⁺ step))
        (radius mesh)
        (radius η)
        step+step<mesh)

  step+step+η<ε : (step +⁺ step) +⁺ η <⁺ ε
  step+step+η<ε =
    subst
      (λ ρ → radius ((step +⁺ step) +⁺ η) ℚOrder.< ρ)
      (cong radius (half⁺+half⁺≡ ε))
      step+step+η<mesh+η

  step+step+η≤ε :
    radius ((step +⁺ step) +⁺ η) ℚOrder.≤ radius ε
  step+step+η≤ε =
    ℚOrder.<Weaken≤
      (radius ((step +⁺ step) +⁺ η))
      (radius ε)
      step+step+η<ε
