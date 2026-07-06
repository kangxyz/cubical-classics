{-

Endpoint margin data for untruncated IVT grid search

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.IVT.Endpoint where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; _×_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Nullary using (Dec)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude using (neg-zeroᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.Interval
open import Constructive.Analysis.Reals.Interval.Grid
open import Constructive.Analysis.Reals.IVT.Sampling
open import Constructive.Analysis.Reals.IVT.Uniform
open import Constructive.Analysis.Reals.Locator.Base
open import Constructive.Algebra.LinearlyOrderedField.Instances.Rationals
  using (ℚLinearlyOrderedField)
import Constructive.Algebra.LinearlyOrderedField.Properties as LOFProperties
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational
open import Constructive.Preliminary.Nat using (splitSupportΣP)

open ClosenessOf RationalsMetricSpace

private
  module ℚField = LOFProperties.LinearlyOrderedFieldStr ℚLinearlyOrderedField


NegativeMarginᶜ : ℚ⁺ → ℝᶜ → Type₀
NegativeMarginᶜ margin x =
  x ≤ᶜ rational (ℚ.- radius margin)


PositiveMarginᶜ : ℚ⁺ → ℝᶜ → Type₀
PositiveMarginᶜ margin x =
  rational (radius margin) ≤ᶜ x


SignData : ℝᶜ → ℝᶜ → Type₀
SignData x y =
  (Σ[ leftMargin ∈ ℚ⁺ ] NegativeMarginᶜ leftMargin x) ×
  (Σ[ rightMargin ∈ ℚ⁺ ] PositiveMarginᶜ rightMargin y)


private
  reciprocalPrecision : ℕ → ℚ⁺
  reciprocalPrecision n =
    Rational.unitFraction n ,
    Rational.unitFraction-positive n

  searchSamplePrecision : ℕ → ℚ⁺
  searchSamplePrecision n =
    quarter⁺ (reciprocalPrecision n)

  searchCutoffPrecision : ℕ → ℚ⁺
  searchCutoffPrecision n =
    half⁺ (reciprocalPrecision n)

  searchSample<cutoff : (n : ℕ) → searchSamplePrecision n <⁺ searchCutoffPrecision n
  searchSample<cutoff n =
    half< (half⁺ (reciprocalPrecision n))

  searchApproximation :
    (x : ℝᶜ) →
    Locator x →
    (n : ℕ) →
    Σ[ q ∈ ℚ ] x ∼[ searchSamplePrecision n ] rational q
  searchApproximation x loc n =
    Locator.approximate loc (searchSamplePrecision n)

  searchValue :
    (x : ℝᶜ) →
    Locator x →
    ℕ →
    ℚ
  searchValue x loc n =
    searchApproximation x loc n .fst

  searchClose :
    (x : ℝᶜ) →
    (loc : Locator x) →
    (n : ℕ) →
    x ∼[ searchSamplePrecision n ] rational (searchValue x loc n)
  searchClose x loc n =
    searchApproximation x loc n .snd

  NegativeSearchTest : (x : ℝᶜ) → Locator x → ℕ → Type₀
  NegativeSearchTest x loc n =
    searchValue x loc n ℚ.+ radius (searchCutoffPrecision n) ℚOrder.< 0ℚ

  PositiveSearchTest : (x : ℝᶜ) → Locator x → ℕ → Type₀
  PositiveSearchTest x loc n =
    0ℚ ℚOrder.< searchValue x loc n ℚ.- radius (searchCutoffPrecision n)

  isPropNegativeSearchTest :
    (x : ℝᶜ) →
    (loc : Locator x) →
    (n : ℕ) →
    isProp (NegativeSearchTest x loc n)
  isPropNegativeSearchTest x loc n =
    ℚOrder.isProp<
      (searchValue x loc n ℚ.+ radius (searchCutoffPrecision n))
      0ℚ

  isPropPositiveSearchTest :
    (x : ℝᶜ) →
    (loc : Locator x) →
    (n : ℕ) →
    isProp (PositiveSearchTest x loc n)
  isPropPositiveSearchTest x loc n =
    ℚOrder.isProp<
      0ℚ
      (searchValue x loc n ℚ.- radius (searchCutoffPrecision n))

  negativeSearchTest? :
    (x : ℝᶜ) →
    (loc : Locator x) →
    (n : ℕ) →
    Dec (NegativeSearchTest x loc n)
  negativeSearchTest? x loc n =
    ℚField.dec< (searchValue x loc n ℚ.+ radius (searchCutoffPrecision n)) 0ℚ

  positiveSearchTest? :
    (x : ℝᶜ) →
    (loc : Locator x) →
    (n : ℕ) →
    Dec (PositiveSearchTest x loc n)
  positiveSearchTest? x loc n =
    ℚField.dec< 0ℚ (searchValue x loc n ℚ.- radius (searchCutoffPrecision n))


EndpointSignData :
  {a b : ℝᶜ} →
  (a≤b : a ≤ᶜ b) →
  ([ a , b ]ᶜ → ℝᶜ) →
  Type₀
EndpointSignData {a = a} {b = b} a≤b f =
  SignData
    (f (leftEndpoint {a = a} {b = b} a≤b))
    (f (rightEndpoint {a = a} {b = b} a≤b))


negativeStrictMargins :
  (x : ℝᶜ) →
  x <ᶜ 0ᶜ →
  ∥ Σ[ margin ∈ ℚ⁺ ] NegativeMarginᶜ margin x ∥₁
negativeStrictMargins x =
  Prop.map step
  where
  step :
    Σ[ margin ∈ ℚ⁺ ]
      rational (radius margin) ≤ᶜ (0ᶜ +ᶜ (-ᶜ x)) →
    Σ[ margin ∈ ℚ⁺ ] NegativeMarginᶜ margin x
  step (margin , margin≤0-x) =
    margin , x≤-margin
    where
    margin≤-x : rational (radius margin) ≤ᶜ (-ᶜ x)
    margin≤-x =
      subst
        (rational (radius margin) ≤ᶜ_)
        (add-zero-left (-ᶜ x))
        margin≤0-x

    x≤-margin : NegativeMarginᶜ margin x
    x≤-margin =
      subst2
        _≤ᶜ_
        (neg-involutive x)
        (neg-rational (radius margin))
        (negᶜ-pres≤ᶜ
          {x = rational (radius margin)}
          {y = -ᶜ x}
          margin≤-x)


positiveStrictMargins :
  (x : ℝᶜ) →
  0ᶜ <ᶜ x →
  ∥ Σ[ margin ∈ ℚ⁺ ] PositiveMarginᶜ margin x ∥₁
positiveStrictMargins x =
  Prop.map step
  where
  step :
    Σ[ margin ∈ ℚ⁺ ]
      rational (radius margin) ≤ᶜ (x +ᶜ (-ᶜ 0ᶜ)) →
    Σ[ margin ∈ ℚ⁺ ] PositiveMarginᶜ margin x
  step (margin , margin≤x-0) =
    margin ,
    subst
      (rational (radius margin) ≤ᶜ_)
      (cong (x +ᶜ_) neg-zeroᶜ ∙ add-zero-right x)
      margin≤x-0


strictSignData∥∥ :
  (x y : ℝᶜ) →
  x <ᶜ 0ᶜ →
  0ᶜ <ᶜ y →
  ∥ SignData x y ∥₁
strictSignData∥∥ x y x<0 0<y =
  Prop.rec2 squash₁ combine (negativeStrictMargins x x<0) (positiveStrictMargins y 0<y)
  where
  combine :
    Σ[ leftMargin ∈ ℚ⁺ ] NegativeMarginᶜ leftMargin x →
    Σ[ rightMargin ∈ ℚ⁺ ] PositiveMarginᶜ rightMargin y →
    ∥ SignData x y ∥₁
  combine leftData rightData =
    ∣ leftData , rightData ∣₁


negativeApproxMargin :
  (x : ℝᶜ) →
  (q : ℚ) →
  (samplePrecision cutoff : ℚ⁺) →
  samplePrecision <⁺ cutoff →
  x ∼[ samplePrecision ] rational q →
  q ℚ.+ radius cutoff ℚOrder.< 0ℚ →
  Σ[ margin ∈ ℚ⁺ ] NegativeMarginᶜ margin x
negativeApproxMargin x q samplePrecision cutoff sample<cutoff x∼q q+cutoff<0 =
  margin ,
  subst
    (x ≤ᶜ_)
    (cong rational (sym (ℚ.-Invol (q ℚ.+ radius cutoff))))
    x≤q+cutoff
  where
  margin : ℚ⁺
  margin =
    ℚ.- (q ℚ.+ radius cutoff) ,
    Rational.neg-positive {q = q ℚ.+ radius cutoff} q+cutoff<0

  x≤q+cutoff : x ≤ᶜ rational (q ℚ.+ radius cutoff)
  x≤q+cutoff =
    close-rational-upper-bound
      x
      q
      samplePrecision
      cutoff
      sample<cutoff
      x∼q


positiveApproxMargin :
  (x : ℝᶜ) →
  (q : ℚ) →
  (samplePrecision cutoff : ℚ⁺) →
  samplePrecision <⁺ cutoff →
  x ∼[ samplePrecision ] rational q →
  0ℚ ℚOrder.< q ℚ.- radius cutoff →
  Σ[ margin ∈ ℚ⁺ ] PositiveMarginᶜ margin x
positiveApproxMargin x q samplePrecision cutoff sample<cutoff x∼q 0<q-cutoff =
  (q ℚ.- radius cutoff , 0<q-cutoff) ,
  close-rational-lower-bound
    x
    q
    samplePrecision
    cutoff
    sample<cutoff
    x∼q


private
  diff≤→≤+ :
    (q δ φ : ℚ) →
    q ℚ.- φ ℚOrder.≤ δ →
    q ℚOrder.≤ δ ℚ.+ φ
  diff≤→≤+ q δ φ q-φ≤δ =
    subst
      (λ s → s ℚOrder.≤ δ ℚ.+ φ)
      (Rational.[p-q]+q≡p q φ)
      (ℚOrder.≤-+o (q ℚ.- φ) δ φ q-φ≤δ)

  ≤+→diff≤ :
    (m q φ : ℚ) →
    m ℚOrder.≤ q ℚ.+ φ →
    m ℚ.- φ ℚOrder.≤ q
  ≤+→diff≤ m q φ m≤q+φ =
    subst
      (λ s → m ℚ.- φ ℚOrder.≤ s)
      (Rational.[p+q]-q≡p q φ)
      (ℚOrder.≤-+o m (q ℚ.+ φ) (ℚ.- φ) m≤q+φ)

  left-diff<0 :
    {η μ : ℚ⁺} →
    η <⁺ μ →
    radius η ℚ.- radius μ ℚOrder.< 0ℚ
  left-diff<0 {η = η} {μ = μ} η<μ =
    subst
      (λ r → radius η ℚ.- radius μ ℚOrder.< r)
      (ℚ.+InvR (radius μ))
      (ℚOrder.<-+o
        (radius η)
        (radius μ)
        (ℚ.- radius μ)
        η<μ)

  negative-upper<0 :
    {η μ : ℚ⁺} →
    η <⁺ μ →
    (ℚ.- radius μ) ℚ.+ radius η ℚOrder.< 0ℚ
  negative-upper<0 {η = η} {μ = μ} η<μ =
    subst
      (λ r → r ℚOrder.< 0ℚ)
      (ℚ.+Comm (radius η) (ℚ.- radius μ))
      (left-diff<0 {η = η} {μ = μ} η<μ)


negativeMarginSearchTest :
  (x : ℝᶜ) →
  (q : ℚ) →
  (basePrecision margin : ℚ⁺) →
  basePrecision <⁺ margin →
  NegativeMarginᶜ margin x →
  x ∼[ quarter⁺ basePrecision ] rational q →
  q ℚ.+ radius (half⁺ basePrecision) ℚOrder.< 0ℚ
negativeMarginSearchTest x q basePrecision margin base<margin x≤-margin x∼q =
  Rational.≤<-trans
    {p = q ℚ.+ h}
    {q = (ℚ.- radius margin ℚ.+ h) ℚ.+ h}
    {r = 0ℚ}
    q+h≤-margin+h+h
    -margin+h+h<0
  where
  h : ℚ
  h =
    radius (half⁺ basePrecision)

  half+half<margin : half⁺ basePrecision +⁺ half⁺ basePrecision <⁺ margin
  half+half<margin =
    subst
      (λ ρ → ρ <⁺ margin)
      (sym (half⁺+half⁺≡ basePrecision))
      base<margin

  q-half≤x : rational (q ℚ.- h) ≤ᶜ x
  q-half≤x =
    close-rational-lower-bound
      x
      q
      (quarter⁺ basePrecision)
      (half⁺ basePrecision)
      (half< (half⁺ basePrecision))
      x∼q

  q-half≤-margin : rational (q ℚ.- h) ≤ᶜ rational (ℚ.- radius margin)
  q-half≤-margin =
    ≤ᶜ-trans
      {x = rational (q ℚ.- h)}
      {y = x}
      {z = rational (ℚ.- radius margin)}
      q-half≤x
      x≤-margin

  q≤-margin+h : q ℚOrder.≤ ℚ.- radius margin ℚ.+ h
  q≤-margin+h =
    diff≤→≤+
      q
      (ℚ.- radius margin)
      h
      (rational≤ᶜ→≤ℚ q-half≤-margin)

  q+h≤-margin+h+h :
    q ℚ.+ h ℚOrder.≤ (ℚ.- radius margin ℚ.+ h) ℚ.+ h
  q+h≤-margin+h+h =
    ℚOrder.≤-+o q (ℚ.- radius margin ℚ.+ h) h q≤-margin+h

  -margin+h+h<0 : (ℚ.- radius margin ℚ.+ h) ℚ.+ h ℚOrder.< 0ℚ
  -margin+h+h<0 =
    subst
      (λ r → r ℚOrder.< 0ℚ)
      (ℚ.+Assoc (ℚ.- radius margin) h h)
      (negative-upper<0 {η = half⁺ basePrecision +⁺ half⁺ basePrecision}
        {μ = margin}
        half+half<margin)


positiveMarginSearchTest :
  (x : ℝᶜ) →
  (q : ℚ) →
  (basePrecision margin : ℚ⁺) →
  basePrecision <⁺ margin →
  PositiveMarginᶜ margin x →
  x ∼[ quarter⁺ basePrecision ] rational q →
  0ℚ ℚOrder.< q ℚ.- radius (half⁺ basePrecision)
positiveMarginSearchTest x q basePrecision margin base<margin margin≤x x∼q =
  Rational.diff-positive {p = h} {q = q} h<q
  where
  h : ℚ
  h =
    radius (half⁺ basePrecision)

  half+half<margin : half⁺ basePrecision +⁺ half⁺ basePrecision <⁺ margin
  half+half<margin =
    subst
      (λ ρ → ρ <⁺ margin)
      (sym (half⁺+half⁺≡ basePrecision))
      base<margin

  x≤q+half : x ≤ᶜ rational (q ℚ.+ h)
  x≤q+half =
    close-rational-upper-bound
      x
      q
      (quarter⁺ basePrecision)
      (half⁺ basePrecision)
      (half< (half⁺ basePrecision))
      x∼q

  margin≤q+half : rational (radius margin) ≤ᶜ rational (q ℚ.+ h)
  margin≤q+half =
    ≤ᶜ-trans
      {x = rational (radius margin)}
      {y = x}
      {z = rational (q ℚ.+ h)}
      margin≤x
      x≤q+half

  half+half<q+half :
    radius (half⁺ basePrecision +⁺ half⁺ basePrecision) ℚOrder.< q ℚ.+ h
  half+half<q+half =
    Rational.<≤-trans
      {p = radius (half⁺ basePrecision +⁺ half⁺ basePrecision)}
      {q = radius margin}
      {r = q ℚ.+ h}
      half+half<margin
      (rational≤ᶜ→≤ℚ margin≤q+half)

  h<q : h ℚOrder.< q
  h<q =
    subst
      (λ r → r ℚOrder.< q)
      (Rational.[p+q]-q≡p h h)
      (Rational.<+→diff<
        (radius (half⁺ basePrecision +⁺ half⁺ basePrecision))
        q
        h
        half+half<q+half)


negativeLocatedSearchExists :
  (x : ℝᶜ) →
  (loc : Locator x) →
  x <ᶜ 0ᶜ →
  ∥ Σ[ n ∈ ℕ ] NegativeSearchTest x loc n ∥₁
negativeLocatedSearchExists x loc x<0 =
  Prop.map fromMargin (negativeStrictMargins x x<0)
  where
  fromMargin :
    Σ[ margin ∈ ℚ⁺ ] NegativeMarginᶜ margin x →
    Σ[ n ∈ ℕ ] NegativeSearchTest x loc n
  fromMargin (margin , x≤-margin) =
    n ,
    negativeMarginSearchTest
      x
      (searchValue x loc n)
      (reciprocalPrecision n)
      margin
      base<margin
      x≤-margin
      (searchClose x loc n)
    where
    nData : Σ[ k ∈ ℕ ] Rational.unitFraction k ℚOrder.< radius margin
    nData =
      Rational.archimedean-unit-fraction (radius margin) (margin .snd)

    n : ℕ
    n =
      nData .fst

    base<margin : reciprocalPrecision n <⁺ margin
    base<margin =
      nData .snd


positiveLocatedSearchExists :
  (x : ℝᶜ) →
  (loc : Locator x) →
  0ᶜ <ᶜ x →
  ∥ Σ[ n ∈ ℕ ] PositiveSearchTest x loc n ∥₁
positiveLocatedSearchExists x loc 0<x =
  Prop.map fromMargin (positiveStrictMargins x 0<x)
  where
  fromMargin :
    Σ[ margin ∈ ℚ⁺ ] PositiveMarginᶜ margin x →
    Σ[ n ∈ ℕ ] PositiveSearchTest x loc n
  fromMargin (margin , margin≤x) =
    n ,
    positiveMarginSearchTest
      x
      (searchValue x loc n)
      (reciprocalPrecision n)
      margin
      base<margin
      margin≤x
      (searchClose x loc n)
    where
    nData : Σ[ k ∈ ℕ ] Rational.unitFraction k ℚOrder.< radius margin
    nData =
      Rational.archimedean-unit-fraction (radius margin) (margin .snd)

    n : ℕ
    n =
      nData .fst

    base<margin : reciprocalPrecision n <⁺ margin
    base<margin =
      nData .snd


negativeSearchTestMargin :
  (x : ℝᶜ) →
  (loc : Locator x) →
  Σ[ n ∈ ℕ ] NegativeSearchTest x loc n →
  Σ[ margin ∈ ℚ⁺ ] NegativeMarginᶜ margin x
negativeSearchTestMargin x loc (n , test) =
  negativeApproxMargin
    x
    (searchValue x loc n)
    (searchSamplePrecision n)
    (searchCutoffPrecision n)
    (searchSample<cutoff n)
    (searchClose x loc n)
    test


negativeLocatedStrictMargin :
  (x : ℝᶜ) →
  Locator x →
  x <ᶜ 0ᶜ →
  Σ[ margin ∈ ℚ⁺ ] NegativeMarginᶜ margin x
negativeLocatedStrictMargin x loc x<0 =
  negativeSearchTestMargin
    x
    loc
    (splitSupportΣP
      (isPropNegativeSearchTest x loc)
      (negativeSearchTest? x loc)
      (negativeLocatedSearchExists x loc x<0))


positiveSearchTestMargin :
  (x : ℝᶜ) →
  (loc : Locator x) →
  Σ[ n ∈ ℕ ] PositiveSearchTest x loc n →
  Σ[ margin ∈ ℚ⁺ ] PositiveMarginᶜ margin x
positiveSearchTestMargin x loc (n , test) =
  positiveApproxMargin
    x
    (searchValue x loc n)
    (searchSamplePrecision n)
    (searchCutoffPrecision n)
    (searchSample<cutoff n)
    (searchClose x loc n)
    test


positiveLocatedStrictMargin :
  (x : ℝᶜ) →
  Locator x →
  0ᶜ <ᶜ x →
  Σ[ margin ∈ ℚ⁺ ] PositiveMarginᶜ margin x
positiveLocatedStrictMargin x loc 0<x =
  positiveSearchTestMargin
    x
    loc
    (splitSupportΣP
      (isPropPositiveSearchTest x loc)
      (positiveSearchTest? x loc)
      (positiveLocatedSearchExists x loc 0<x))


locatedStrictSignData :
  (x y : ℝᶜ) →
  Locator x →
  Locator y →
  x <ᶜ 0ᶜ →
  0ᶜ <ᶜ y →
  SignData x y
locatedStrictSignData x y loc-x loc-y x<0 0<y =
  negativeLocatedStrictMargin x loc-x x<0 ,
  positiveLocatedStrictMargin y loc-y 0<y


negativeMarginSample<0 :
  (x : ℝᶜ) →
  (q : ℚ) →
  (samplePrecision cutoff margin : ℚ⁺) →
  samplePrecision <⁺ cutoff →
  cutoff <⁺ margin →
  NegativeMarginᶜ margin x →
  x ∼[ samplePrecision ] rational q →
  q ℚOrder.< 0ℚ
negativeMarginSample<0 x q samplePrecision cutoff margin
    sample<cutoff cutoff<margin x≤-margin x∼q =
  Rational.≤<-trans
    {p = q}
    {q = (ℚ.- radius margin) ℚ.+ radius cutoff}
    {r = 0ℚ}
    q≤-margin+cutoff
    (negative-upper<0 {η = cutoff} {μ = margin} cutoff<margin)
  where
  q-cutoff≤x : rational (q ℚ.- radius cutoff) ≤ᶜ x
  q-cutoff≤x =
    close-rational-lower-bound
      x
      q
      samplePrecision
      cutoff
      sample<cutoff
      x∼q

  q-cutoff≤-margin :
    rational (q ℚ.- radius cutoff) ≤ᶜ rational (ℚ.- radius margin)
  q-cutoff≤-margin =
    ≤ᶜ-trans
      {x = rational (q ℚ.- radius cutoff)}
      {y = x}
      {z = rational (ℚ.- radius margin)}
      q-cutoff≤x
      x≤-margin

  q≤-margin+cutoff :
    q ℚOrder.≤ (ℚ.- radius margin) ℚ.+ radius cutoff
  q≤-margin+cutoff =
    diff≤→≤+
      q
      (ℚ.- radius margin)
      (radius cutoff)
      (rational≤ᶜ→≤ℚ q-cutoff≤-margin)


positiveMarginSample0≤ :
  (x : ℝᶜ) →
  (q : ℚ) →
  (samplePrecision cutoff margin : ℚ⁺) →
  samplePrecision <⁺ cutoff →
  cutoff <⁺ margin →
  PositiveMarginᶜ margin x →
  x ∼[ samplePrecision ] rational q →
  0ℚ ℚOrder.≤ q
positiveMarginSample0≤ x q samplePrecision cutoff margin
    sample<cutoff cutoff<margin margin≤x x∼q =
  Rational.≤-trans
    {p = 0ℚ}
    {q = radius margin ℚ.- radius cutoff}
    {r = q}
    (Rational.<→≤
      {p = 0ℚ}
      {q = radius margin ℚ.- radius cutoff}
      (Rational.diff-positive
        {p = radius cutoff}
        {q = radius margin}
        cutoff<margin))
    margin-cutoff≤q
  where
  x≤q+cutoff : x ≤ᶜ rational (q ℚ.+ radius cutoff)
  x≤q+cutoff =
    close-rational-upper-bound
      x
      q
      samplePrecision
      cutoff
      sample<cutoff
      x∼q

  margin≤q+cutoff :
    rational (radius margin) ≤ᶜ rational (q ℚ.+ radius cutoff)
  margin≤q+cutoff =
    ≤ᶜ-trans
      {x = rational (radius margin)}
      {y = x}
      {z = rational (q ℚ.+ radius cutoff)}
      margin≤x
      x≤q+cutoff

  margin-cutoff≤q :
    radius margin ℚ.- radius cutoff ℚOrder.≤ q
  margin-cutoff≤q =
    ≤+→diff≤
      (radius margin)
      q
      (radius cutoff)
      (rational≤ᶜ→≤ℚ margin≤q+cutoff)


leftEndpointSampleNegative :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b n) →
  (samplePrecision cutoff margin : ℚ⁺) →
  samplePrecision <⁺ cutoff →
  cutoff <⁺ margin →
  NegativeMarginᶜ margin (f (leftEndpoint {a = a} {b = b} a≤b)) →
  gridSampleValues ivtData G samplePrecision Fin.zero ℚOrder.< 0ℚ
leftEndpointSampleNegative {a = a} {b = b} {a≤b = a≤b} {f = f}
    ivtData G samplePrecision cutoff margin sample<cutoff cutoff<margin leftMargin =
  negativeMarginSample<0
    (f (Grid.point G Fin.zero))
    (gridSampleValues ivtData G samplePrecision Fin.zero)
    samplePrecision
    cutoff
    margin
    sample<cutoff
    cutoff<margin
    gridLeftMargin
    (gridSampleClose ivtData G samplePrecision Fin.zero)
  where
  gridLeftMargin : NegativeMarginᶜ margin (f (Grid.point G Fin.zero))
  gridLeftMargin =
    subst
      (λ u → NegativeMarginᶜ margin (f u))
      (sym (gridLeftEndpointPath G))
      leftMargin


rightEndpointSampleNonnegative :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {f : [ a , b ]ᶜ → ℝᶜ} →
  (ivtData : IVTFunctionData a b f) →
  {n : ℕ} →
  (G : Grid a b a≤b n) →
  (samplePrecision cutoff margin : ℚ⁺) →
  samplePrecision <⁺ cutoff →
  cutoff <⁺ margin →
  PositiveMarginᶜ margin (f (rightEndpoint {a = a} {b = b} a≤b)) →
  0ℚ ℚOrder.≤ gridSampleValues ivtData G samplePrecision (Fin.fromℕ n)
rightEndpointSampleNonnegative {a = a} {b = b} {a≤b = a≤b} {f = f}
    ivtData G samplePrecision cutoff margin sample<cutoff cutoff<margin rightMargin =
  positiveMarginSample0≤
    (f (Grid.point G (Fin.fromℕ _)))
    (gridSampleValues ivtData G samplePrecision (Fin.fromℕ _))
    samplePrecision
    cutoff
    margin
    sample<cutoff
    cutoff<margin
    gridRightMargin
    (gridSampleClose ivtData G samplePrecision (Fin.fromℕ _))
  where
  gridRightMargin :
    PositiveMarginᶜ margin (f (Grid.point G (Fin.fromℕ _)))
  gridRightMargin =
    subst
      (λ u → PositiveMarginᶜ margin (f u))
      (sym (gridRightEndpointPath G))
      rightMargin
