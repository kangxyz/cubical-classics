{-

Metric Space

This file contains:
- The definition of metric space;
- Basics of open balls;
- The topology induced from metric structure;
- A metric space is always Hausdorff.

-}
{-# OPTIONS --safe #-}
module Classical.Topology.Metric.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Nullary

open import Classical.Axioms
open import Classical.Foundations.Powerset

open import Classical.Topology.Base
open import Classical.Topology.Properties
open import Classical.Topology.Neighbourhood
open import Classical.Topology.Hausdorff

open import Constructive.Algebra.LinearlyOrderedCommRing
  using (lt ; eq ; gt)
open import Constructive.Algebra.LinearlyOrderedField
open import Classical.Analysis.Real

private
  variable
    ℓ : Level


module _ ⦃ 🤖 : Oracle ⦄ where

  open Oracle 🤖

  open LinearlyOrderedFieldStr (ℝMacNeilleCompleteOrderedField .fst)
  open Topology


  record Metric (X : Type ℓ) : Type (ℓ-suc ℓ) where
    field

      dist : X → X → ℝ
      dist-id   : {x y : X} → dist x y ≡ 0 → x ≡ y
      dist-refl : {x y : X} → x ≡ y → dist x y ≡ 0
      dist-symm : (x y : X) → dist x y ≡ dist y x
      dist-Δ : (x y z : X) → dist x y + dist y z ≥ dist x z


  module _ {X : Type ℓ} ⦃ 𝓂 : Metric X ⦄ where

    private
      variable
        x y z : X

    open Metric 𝓂

    {-

      Basic Properties

    -}

    -- The distance is always non-negative.
    -- Notice that we do not assume non-negativity in the definition,
    -- but it's a corollary.

    dist≥0 : dist x y ≥ 0
    dist≥0 {x = x} {y = y} with trichotomy (dist x y) 0
    ... | gt d>0 = <-≤-weaken d>0
    ... | eq d≡0 = ≤-refl (sym d≡0)
    ... | lt d<0 = Empty.rec (<≤-asym (+-Pres<0 d<0 d<0) d+d≥0)
      where
      d+d≥0 : dist x y + dist x y ≥ 0
      d+d≥0 = transport (λ i → dist x y + dist-symm y x i ≥ dist-refl {x = x} refl i) (dist-Δ _ _ _)


    ¬x≡y→dist>0 : ¬ x ≡ y → dist x y > 0
    ¬x≡y→dist>0 {x = x} {y = y} ¬x≡y with trichotomy (dist x y) 0
    ... | gt d>0 = d>0
    ... | eq d≡0 = Empty.rec (¬x≡y (dist-id d≡0))
    ... | lt d<0 = Empty.rec (<≤-asym d<0 dist≥0)

    dist>0→¬x≡y : dist x y > 0 → ¬ x ≡ y
    dist>0→¬x≡y d>0 x≡y = <-arefl d>0 (sym (dist-refl x≡y))


    -- Under our definition of metric space,
    -- the underlying type is always an h-set.

    discreteMetric : Discrete X
    discreteMetric x y with trichotomy (dist x y) 0
    ... | gt d>0 = no (dist>0→¬x≡y d>0)
    ... | eq d≡0 = yes (dist-id d≡0)
    ... | lt d<0 = Empty.rec (<≤-asym d<0 dist≥0)

    isSetMetric : isSet X
    isSetMetric = Discrete→isSet discreteMetric


    -- If two points are `infinitely close to` each other, then they are equal.

    infinitelyClose→≡ : {x y : X} → ((ε : ℝ) → (ε > 0) → dist x y < ε) → x ≡ y
    infinitelyClose→≡ ∀ε>∣x-y∣ = dist-id (infinitesimal dist≥0 ∀ε>∣x-y∣)

    dist-triangle<ε : {x y z : X}{ε : ℝ} → ε > 0
      → dist x y < middle 0 ε
      → dist y z < middle 0 ε
      → dist x z < ε
    dist-triangle<ε {x = x} {y = y} {z = z} {ε = ε} ε>0 dxy<ε/2 dyz<ε/2 =
      ≤<-trans (dist-Δ x y z)
        (transport (λ i → dist x y + dist y z < x/2+x/2≡x ε i)
          (+-Pres< dxy<ε/2 dyz<ε/2))


    {-

      Open Balls

    -}

    -- An open ball is the collection of points
    -- whose distance to a fixed point is smaller than a given number.

    module _ (x : X)(r : ℝ) ⦃ r>0 : r > 0 ⦄ where

      ball-prop : X → hProp _
      ball-prop y = (dist x y < r) , isProp<

      ℬ : ℙ X
      ℬ = specify ball-prop


    Inhab→∈ℬ : {x y : X}{r : ℝ} ⦃ _ : r > 0 ⦄ → dist x y < r → y ∈ ℬ x r
    Inhab→∈ℬ = Inhab→∈ (ball-prop _ _)

    ∈→Inhabℬ : {x y : X}{r : ℝ} ⦃ _ : r > 0 ⦄ → y ∈ ℬ x r → dist x y < r
    ∈→Inhabℬ = ∈→Inhab (ball-prop _ _)


    x∈ℬxr : {x : X}{r : ℝ} ⦃ _ : r > 0 ⦄ → x ∈ ℬ x r
    x∈ℬxr {x = x} {r = r} ⦃ r>0 ⦄ = Inhab→∈ℬ (subst (_< r) (sym (dist-refl {x = x} refl)) r>0)

    ℬ⊆ : {x : X}{r r' : ℝ} ⦃ _ : r > 0 ⦄ ⦃ _ : r' > 0 ⦄ → r < r' → ℬ x r ⊆ ℬ x r'
    ℬ⊆ r<r' x∈ℬxr = Inhab→∈ℬ (<-trans (∈→Inhabℬ x∈ℬxr) r<r')

    ℬ⊆' : {x y : X}{r r' : ℝ} ⦃ _ : r > 0 ⦄ ⦃ _ : r' > 0 ⦄ → dist x y + r < r' → ℬ x r ⊆ ℬ y r'
    ℬ⊆' {x = x} {y = y} {r' = r'} d+r<r' {x = z} z∈ℬxr = Inhab→∈ℬ (≤<-trans (dist-Δ _ _ _) dyx+dxz<r')
      where
      dyx+dxz<r' : dist y x + dist x z < r'
      dyx+dxz<r' = subst (λ t → t + dist x z < r') (dist-symm _ _)
        (<-trans (+-lPres< (∈→Inhabℬ z∈ℬxr)) d+r<r')


    {-

      Topology Induced by Metric

    ­-}

    private
      𝓂-prop : ℙ X → hProp _
      𝓂-prop A = ((x : X) → x ∈ A → ∥ Σ[ r ∈ ℝ ] Σ[ r>0 ∈ r > 0 ] ℬ x r ⦃ r>0 ⦄ ⊆ A ∥₁) , isPropΠ2 (λ _ _ → squash₁)

    Metric→Topology : Topology X
    Metric→Topology .openset = specify 𝓂-prop
    Metric→Topology .has-∅ = Inhab→∈ 𝓂-prop (λ x x∈∅ → Empty.rec (¬x∈∅ x x∈∅))
    Metric→Topology .has-total = Inhab→∈ 𝓂-prop (λ x _ → ∣ 1 , 1>0 , A⊆total {A = ℬ x 1 ⦃ 1>0 ⦄} ∣₁)
    Metric→Topology .∩-close {A = A} {B = B} A∈Open B∈Open =
      Inhab→∈ 𝓂-prop (λ x x∈A∩B → do
      (r₀ , r₀>0 , ℬxr₀⊆A) ← ∈→Inhab 𝓂-prop A∈Open x (left∈-∩  A B x∈A∩B)
      (r₁ , r₁>0 , ℬxr₁⊆B) ← ∈→Inhab 𝓂-prop B∈Open x (right∈-∩ A B x∈A∩B)
      let (r , r>0 , r<r₀ , r<r₁) = min2 r₀>0 r₁>0
      return (
        r , r>0 , ⊆→⊆∩ A B
        (⊆-trans {A = ℬ x r ⦃ r>0 ⦄} (ℬ⊆ ⦃ r>0 ⦄ ⦃ r₀>0 ⦄ r<r₀) ℬxr₀⊆A)
        (⊆-trans {A = ℬ x r ⦃ r>0 ⦄} (ℬ⊆ ⦃ r>0 ⦄ ⦃ r₁>0 ⦄ r<r₁) ℬxr₁⊆B)))

    Metric→Topology .∪-close {S = S} S⊆Open =
      Inhab→∈ 𝓂-prop (λ x x∈∪S → do
      (A , x∈A , A∈S) ← ∈union→∃ x∈∪S
      (r , r>0 , ℬxr⊆A) ← ∈→Inhab 𝓂-prop (S⊆Open A∈S) x x∈A
      return (r , r>0 , (λ p → ⊆union ℬxr⊆A A∈S p)))


    private
      instance
        MetricTopology : Topology X
        MetricTopology = Metric→Topology


    -- A subset U in a metric space is open
    -- if and only if any point x ∈ U has an open ball centered at x and contained in U.

    module _ {U : ℙ X} where

      ∈→Inhab𝓂 : isOpenSub U → (x : X) → x ∈ U → ∥ Σ[ r ∈ ℝ ] Σ[ r>0 ∈ r > 0 ] ℬ x r ⦃ r>0 ⦄ ⊆ U ∥₁
      ∈→Inhab𝓂 = ∈→Inhab 𝓂-prop

      Inhab→∈𝓂 : ((x : X) → x ∈ U → ∥ Σ[ r ∈ ℝ ] Σ[ r>0 ∈ r > 0 ] ℬ x r ⦃ r>0 ⦄ ⊆ U ∥₁) → isOpenSub U
      Inhab→∈𝓂 = Inhab→∈ 𝓂-prop


    -- Open balls are really open

    isOpenℬ : {x : X}{r : ℝ} ⦃ _ : r > 0 ⦄ → ℬ x r ∈ MetricTopology .openset
    isOpenℬ {x = x} {r = r} =
      Inhab→∈ 𝓂-prop (λ y y∈ℬxr → do
      let r-d = r - dist y x
          r-d>0 : r-d > 0
          r-d>0 = subst (λ t → r - t > 0) (dist-symm _ _) (>→Diff>0 (∈→Inhabℬ y∈ℬxr))
          r' = middle 0 r-d
          r'>0 = middle>l r-d>0
          d+r'<r : dist y x + r' < r
          d+r'<r = subst (_< r) (+Comm _ _) (-MoveRToL< (middle<r r-d>0))
      return (r' , r'>0 , ℬ⊆' ⦃ r'>0 ⦄ d+r'<r))


    {-

      Metric Space is Hausdorff

    -}

    open isHausdorff

    isHausdorffMetric : isHausdorff
    isHausdorffMetric .separate {x = x} {y = y} ¬x≡y =
      ∣ ℬ x d/2 , ℬ y d/2 , makeℕbh x∈ℬxr isOpenℬ , makeℕbh x∈ℬxr isOpenℬ , →∩∅' ∩ℬ≡∅ ∣₁
      where

      d = dist x y
      d/2 = middle 0 d

      instance
        d/2>0 : d/2 > 0
        d/2>0 = middle>l (¬x≡y→dist>0 ¬x≡y)

      module _ (z : X)(z∈ℬx : z ∈ ℬ x d/2)(z∈ℬy : z ∈ ℬ y d/2) where

        dx+dy<d : dist x z + dist z y < dist x y
        dx+dy<d = transport (λ i → dist x z + dist-symm y z i < x/2+x/2≡x d i)
          (+-Pres< (∈→Inhabℬ z∈ℬx) (∈→Inhabℬ z∈ℬy))

        ∩ℬ≡∅ : ⊥
        ∩ℬ≡∅ = Empty.rec (<≤-asym dx+dy<d (dist-Δ _ _ _))
