{-

Approximate extrema for uniformly continuous maps on closed intervals

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Interval.Extrema where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Metric.TotallyBounded
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Density
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
  using (negᶜ-pres≤ᶜ)
open import Constructive.Analysis.Reals.Interval.Base
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals.Base as RationalBase


ApproxMaximum :
  {a b : ℝᶜ} →
  ([ a , b ]ᶜ → ℝᶜ) →
  ℚ⁺ →
  Type₀
ApproxMaximum {a = a} {b = b} f ε =
  Σ[ value ∈ ℚ ]
    Σ[ nearValue ∈ ∥ Σ[ x ∈ [ a , b ]ᶜ ]
        f x ∼[ ε ] rational value ∥₁ ]
      ((x : [ a , b ]ᶜ) →
        f x ≤ᶜ rational (value ℚ.+ radius ε))


approx-maximum :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} {ε : ℚ⁺} →
  (value : ℚ) →
  ∥ Σ[ x ∈ [ a , b ]ᶜ ] f x ∼[ ε ] rational value ∥₁ →
  ((x : [ a , b ]ᶜ) →
    f x ≤ᶜ rational (value ℚ.+ radius ε)) →
  ApproxMaximum f ε
approx-maximum value nearValue approximateUpper =
  value , nearValue , approximateUpper


module ApproxMaximum where
  value :
    {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} {ε : ℚ⁺} →
    ApproxMaximum f ε →
    ℚ
  value max =
    max .fst

  nearValue :
    {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} {ε : ℚ⁺} →
    (max : ApproxMaximum f ε) →
    ∥ Σ[ x ∈ [ a , b ]ᶜ ] f x ∼[ ε ] rational (value max) ∥₁
  nearValue max =
    max .snd .fst

  approximateUpper :
    {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} {ε : ℚ⁺} →
    (max : ApproxMaximum f ε) →
    (x : [ a , b ]ᶜ) →
    f x ≤ᶜ rational (value max ℚ.+ radius ε)
  approximateUpper max =
    max .snd .snd


ApproxMinimum :
  {a b : ℝᶜ} →
  ([ a , b ]ᶜ → ℝᶜ) →
  ℚ⁺ →
  Type₀
ApproxMinimum {a = a} {b = b} f ε =
  Σ[ value ∈ ℚ ]
    Σ[ nearValue ∈ ∥ Σ[ x ∈ [ a , b ]ᶜ ]
        f x ∼[ ε ] rational value ∥₁ ]
      ((x : [ a , b ]ᶜ) →
        rational (value ℚ.- radius ε) ≤ᶜ f x)


approx-minimum :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} {ε : ℚ⁺} →
  (value : ℚ) →
  ∥ Σ[ x ∈ [ a , b ]ᶜ ] f x ∼[ ε ] rational value ∥₁ →
  ((x : [ a , b ]ᶜ) →
    rational (value ℚ.- radius ε) ≤ᶜ f x) →
  ApproxMinimum f ε
approx-minimum value nearValue approximateLower =
  value , nearValue , approximateLower


module ApproxMinimum where
  value :
    {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} {ε : ℚ⁺} →
    ApproxMinimum f ε →
    ℚ
  value min =
    min .fst

  nearValue :
    {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} {ε : ℚ⁺} →
    (min : ApproxMinimum f ε) →
    ∥ Σ[ x ∈ [ a , b ]ᶜ ] f x ∼[ ε ] rational (value min) ∥₁
  nearValue min =
    min .snd .fst

  approximateLower :
    {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} {ε : ℚ⁺} →
    (min : ApproxMinimum f ε) →
    (x : [ a , b ]ᶜ) →
    rational (value min ℚ.- radius ε) ≤ᶜ f x
  approximateLower min =
    min .snd .snd


private
  finiteTailSeed :
    {n : ℕ} →
    Fin (suc (suc n)) →
    Fin (suc n)
  finiteTailSeed Fin.zero =
    Fin.zero
  finiteTailSeed (Fin.suc i) =
    i

  finiteMaximumFromSeed :
    {n : ℕ} →
    (values : Fin n → ℚ) →
    Fin n →
    Σ[ i ∈ Fin n ] ((j : Fin n) → values j ℚOrder.≤ values i)
  finiteMaximumFromSeed {n = zero} values i =
    Empty.rec (Fin.¬Fin0 i)
  finiteMaximumFromSeed {n = suc zero} values Fin.zero =
    Fin.zero , λ { Fin.zero → RationalBase.≤-refl (values Fin.zero) }
  finiteMaximumFromSeed {n = suc (suc n)} values seed
      with finiteMaximumFromSeed
        (λ i → values (Fin.suc i))
        (finiteTailSeed seed)
  ... | tailIndex , tailUpper with values Fin.zero ℚOrder.≟ values (Fin.suc tailIndex)
  ... | ℚOrder.lt head<tail =
    Fin.suc tailIndex , upper
    where
    upper : (j : Fin (suc (suc n))) →
      values j ℚOrder.≤ values (Fin.suc tailIndex)
    upper Fin.zero =
      RationalBase.<→≤
        {p = values Fin.zero}
        {q = values (Fin.suc tailIndex)}
        head<tail
    upper (Fin.suc j) =
      tailUpper j
  ... | ℚOrder.eq head≡tail =
    Fin.suc tailIndex , upper
    where
    upper : (j : Fin (suc (suc n))) →
      values j ℚOrder.≤ values (Fin.suc tailIndex)
    upper Fin.zero =
      ℚOrder.≡Weaken≤
        (values Fin.zero)
        (values (Fin.suc tailIndex))
        head≡tail
    upper (Fin.suc j) =
      tailUpper j
  ... | ℚOrder.gt tail<head =
    Fin.zero , upper
    where
    tail≤head : values (Fin.suc tailIndex) ℚOrder.≤ values Fin.zero
    tail≤head =
      RationalBase.<→≤
        {p = values (Fin.suc tailIndex)}
        {q = values Fin.zero}
        tail<head

    upper : (j : Fin (suc (suc n))) →
      values j ℚOrder.≤ values Fin.zero
    upper Fin.zero =
      RationalBase.≤-refl (values Fin.zero)
    upper (Fin.suc j) =
      RationalBase.≤-trans
        {p = values (Fin.suc j)}
        {q = values (Fin.suc tailIndex)}
        {r = values Fin.zero}
        (tailUpper j)
        tail≤head

  approxValues∥∥ :
    {n : ℕ} →
    (points : Fin n → ℝᶜ) →
    (ε : ℚ⁺) →
    ∥ Σ[ values ∈ (Fin n → ℚ) ]
        ((i : Fin n) → points i ∼[ ε ] rational (values i)) ∥₁
  approxValues∥∥ {n = zero} points ε =
    ∣ (λ ()) , (λ ()) ∣₁
  approxValues∥∥ {n = suc n} points ε =
    Prop.rec2 squash₁ combine
      (rational-approximation (points Fin.zero) ε)
      (approxValues∥∥ (λ i → points (Fin.suc i)) ε)
    where
    combine :
      Σ[ q ∈ ℚ ] points Fin.zero ∼[ ε ] rational q →
      Σ[ values ∈ (Fin n → ℚ) ]
        ((i : Fin n) → points (Fin.suc i) ∼[ ε ] rational (values i)) →
      ∥ Σ[ values ∈ (Fin (suc n) → ℚ) ]
          ((i : Fin (suc n)) → points i ∼[ ε ] rational (values i)) ∥₁
    combine (q , point∼q) (tailValues , tailClose) =
      ∣ values , valuesClose ∣₁
      where
      values : Fin (suc n) → ℚ
      values Fin.zero =
        q
      values (Fin.suc i) =
        tailValues i

      valuesClose :
        (i : Fin (suc n)) →
        points i ∼[ ε ] rational (values i)
      valuesClose Fin.zero =
        point∼q
      valuesClose (Fin.suc i) =
        tailClose i


approximateMaximum :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
  a ≤ᶜ b →
  IsTotallyBounded (IntervalMetric a b) →
  IsUniformlyContinuous
    (IntervalMetric a b)
    CauchyRealsMetricSpace
    f →
  (ε : ℚ⁺) →
  ∥ ApproxMaximum f ε ∥₁
approximateMaximum {a = a} {b = b} {f = f} a≤b tb (μ , f-cont) ε =
  Prop.rec2 squash₁ combine centerCover valuesData
  where
  sample movement : ℚ⁺
  sample =
    quarter⁺ ε
  movement =
    quarter⁺ ε

  imageNet : ImageFiniteNet (IntervalMetric a b) CauchyRealsMetricSpace f movement
  imageNet =
    uniformlyContinuousImageTotallyBounded tb (μ , f-cont) movement

  centerCover :
    ∥ Σ[ i ∈ Fin (ImageFiniteNet.size imageNet) ]
        ImageFiniteNet.center imageNet i ∼[ movement ]
        f (leftEndpoint {a = a} {b = b} a≤b) ∥₁
  centerCover =
    ImageFiniteNet.covers imageNet (leftEndpoint {a = a} {b = b} a≤b)

  valuesData :
    ∥ Σ[ values ∈ (Fin (ImageFiniteNet.size imageNet) → ℚ) ]
        ((i : Fin (ImageFiniteNet.size imageNet)) →
          ImageFiniteNet.center imageNet i ∼[ sample ] rational (values i)) ∥₁
  valuesData =
    approxValues∥∥ (ImageFiniteNet.center imageNet) sample

  sample+movement<ε : sample +⁺ movement <⁺ ε
  sample+movement<ε =
    quarter-sum< ε

  sample<ε : sample <⁺ ε
  sample<ε =
    quarter< ε

  combine :
    Σ[ seed ∈ Fin (ImageFiniteNet.size imageNet) ]
      ImageFiniteNet.center imageNet seed ∼[ movement ]
      f (leftEndpoint {a = a} {b = b} a≤b) →
    Σ[ values ∈ (Fin (ImageFiniteNet.size imageNet) → ℚ) ]
      ((i : Fin (ImageFiniteNet.size imageNet)) →
        ImageFiniteNet.center imageNet i ∼[ sample ] rational (values i)) →
    ∥ ApproxMaximum f ε ∥₁
  combine (seed , _) (values , valuesClose) =
    ∣ approx-maximum maxValue nearMax upperAt ∣₁
    where
    maxData :
      Σ[ i ∈ Fin (ImageFiniteNet.size imageNet) ]
        ((j : Fin (ImageFiniteNet.size imageNet)) →
          values j ℚOrder.≤ values i)
    maxData =
      finiteMaximumFromSeed values seed

    maxIndex : Fin (ImageFiniteNet.size imageNet)
    maxIndex =
      maxData .fst

    maxValue : ℚ
    maxValue =
      values maxIndex

    maxUpper :
      (j : Fin (ImageFiniteNet.size imageNet)) →
      values j ℚOrder.≤ maxValue
    maxUpper =
      maxData .snd

    nearMax :
      ∥ Σ[ x ∈ [ a , b ]ᶜ ] f x ∼[ ε ] rational maxValue ∥₁
    nearMax =
      ∣ FiniteNet.center (tb (μ movement)) maxIndex ,
        MetricSpace.close-mono
          CauchyRealsMetricSpace
          sample<ε
          (valuesClose maxIndex)
      ∣₁

    upperAt :
      (x : [ a , b ]ᶜ) →
      f x ≤ᶜ rational (maxValue ℚ.+ radius ε)
    upperAt x =
      Prop.rec
        (isProp≤ᶜ (f x) (rational (maxValue ℚ.+ radius ε)))
        upperFromCover
        (ImageFiniteNet.covers imageNet x)
      where
      upperFromCover :
        Σ[ i ∈ Fin (ImageFiniteNet.size imageNet) ]
          ImageFiniteNet.center imageNet i ∼[ movement ] f x →
        f x ≤ᶜ rational (maxValue ℚ.+ radius ε)
      upperFromCover (i , center∼fx) =
        ≤ᶜ-trans
          (close-rational-upper-bound
            (f x)
            (values i)
            (movement +⁺ sample)
            ε
            movement+sample<ε
            fx∼qi)
          qi+ε≤max+ε
        where
        movement+sample<ε : movement +⁺ sample <⁺ ε
        movement+sample<ε =
          subst
            (λ ρ → ρ <⁺ ε)
            (+⁺-comm sample movement)
            sample+movement<ε

        fx∼center :
          f x ∼[ movement ] ImageFiniteNet.center imageNet i
        fx∼center =
          MetricSpace.close-sym CauchyRealsMetricSpace center∼fx

        fx∼qi :
          f x ∼[ movement +⁺ sample ] rational (values i)
        fx∼qi =
          MetricSpace.close-triangle
            CauchyRealsMetricSpace
            fx∼center
            (valuesClose i)

        qi+ε≤max+ε :
          rational (values i ℚ.+ radius ε) ≤ᶜ
          rational (maxValue ℚ.+ radius ε)
        qi+ε≤max+ε =
          ≤ℚ→rational≤ᶜ
            (ℚOrder.≤-+o
              (values i)
              maxValue
              (radius ε)
              (maxUpper i))


approximateMinimum :
  {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ} →
  a ≤ᶜ b →
  IsTotallyBounded (IntervalMetric a b) →
  IsUniformlyContinuous
    (IntervalMetric a b)
    CauchyRealsMetricSpace
    f →
  (ε : ℚ⁺) →
  ∥ ApproxMinimum f ε ∥₁
approximateMinimum {a = a} {b = b} {f = f} a≤b tb (μ , f-cont) ε =
  Prop.map minimumFromMaximum
    (approximateMaximum a≤b tb negf-cont ε)
  where
  negf : [ a , b ]ᶜ → ℝᶜ
  negf x =
    -ᶜ f x

  negf-cont :
    IsUniformlyContinuous
      (IntervalMetric a b)
      CauchyRealsMetricSpace
      negf
  negf-cont =
    μ , λ ε x∼y → neg-close (f-cont ε x∼y)

  neg-sumℚ :
    (q r : ℚ) →
    ℚ.- (q ℚ.+ r) ≡ (ℚ.- q) ℚ.- r
  neg-sumℚ q r =
    ℚ.·DistL+ -1 q r

  minimumFromMaximum :
    ApproxMaximum negf ε →
    ApproxMinimum f ε
  minimumFromMaximum negMax =
    approx-minimum
      (ℚ.- ApproxMaximum.value negMax)
      minNear
      minLower
    where
    minNear :
      ∥ Σ[ x ∈ [ a , b ]ᶜ ]
          f x ∼[ ε ] rational (ℚ.- ApproxMaximum.value negMax) ∥₁
    minNear =
      Prop.map nearStep (ApproxMaximum.nearValue negMax)
      where
      nearStep :
        Σ[ x ∈ [ a , b ]ᶜ ]
          negf x ∼[ ε ] rational (ApproxMaximum.value negMax) →
        Σ[ x ∈ [ a , b ]ᶜ ]
          f x ∼[ ε ] rational (ℚ.- ApproxMaximum.value negMax)
      nearStep (x , negfx∼v) =
        x ,
        subst2
          (λ u v → u ∼[ ε ] v)
          (neg-involutive (f x))
          (neg-rational (ApproxMaximum.value negMax))
          (neg-close negfx∼v)

    minLower :
      (x : [ a , b ]ᶜ) →
      rational ((ℚ.- ApproxMaximum.value negMax) ℚ.- radius ε) ≤ᶜ f x
    minLower x =
      subst2
        _≤ᶜ_
        min-path
        (neg-involutive (f x))
        (negᶜ-pres≤ᶜ (ApproxMaximum.approximateUpper negMax x))
      where
      min-path :
        -ᶜ rational (ApproxMaximum.value negMax ℚ.+ radius ε) ≡
        rational ((ℚ.- ApproxMaximum.value negMax) ℚ.- radius ε)
      min-path =
        neg-rational (ApproxMaximum.value negMax ℚ.+ radius ε) ∙
        cong rational (neg-sumℚ (ApproxMaximum.value negMax) (radius ε))
