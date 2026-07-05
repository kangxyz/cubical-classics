{-

Continuous Real-Valued Functions

This file contains:
- Basics of continuous function, using ε-δ as definition;
- The intermediate value theorem.

-}
{-# OPTIONS --safe #-}
module Classical.Analysis.Function.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

open import Classical.Axioms
open import Classical.Foundations.Powerset

open import Constructive.Algebra.LinearlyOrderedCommRing
  using (LinearlyOrderedCommRing→CommRing ; Trichotomy ; lt ; eq ; gt)
open import Constructive.Algebra.LinearlyOrderedCommRing.AbsoluteValue
open import Constructive.Algebra.LinearlyOrderedField
open import Classical.Algebra.OrderedField.Extremum
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Analysis.Real.Base

private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (x : 𝓡 .fst) → x + (1r - x) ≡ 1r
    helper1 _ = solve! 𝓡

    helper2 : (x y : 𝓡 .fst) → x - (x + y) ≡ - y
    helper2 _ _ = solve! 𝓡

    helper3 : (x y : 𝓡 .fst) → x - (x - y) ≡ y
    helper3 _ _ = solve! 𝓡


module _ ⦃ 🤖 : Oracle ⦄ where

  open Oracle 🤖

  open AbsoluteValue   (ℝMacNeilleCompleteOrderedField .fst .fst)
  open LinearlyOrderedFieldStr (ℝMacNeilleCompleteOrderedField .fst)
  open MacNeilleCompleteOrderedField (ℝMacNeilleCompleteOrderedField .fst)


  -- A continuous partial function defined on a subset of ℝ,
  -- using classical ε-δ language.

  record ContinuousFunction (domain : ℙ ℝ) : Type where
    field
      fun : (x : ℝ) ⦃ _ : x ∈ domain ⦄ → ℝ
      cont : (x : ℝ) ⦃ _ : x ∈ domain ⦄ → (ε : ℝ) → ε > 0
        → ∥ Σ[ δ ∈ ℝ ] (δ > 0) × ((y : ℝ) ⦃ _ : y ∈ domain ⦄ → abs (x - y) < δ → abs (fun x - fun y) < ε) ∥₁

  open ContinuousFunction


  {-

    Properties of Continuous Function

  -}

  module _ (𝔻 : ℙ ℝ)(f : ContinuousFunction 𝔻) where

    module _
      (x : ℝ) ⦃ _ : x ∈ 𝔻 ⦄
      (ε : ℝ)(ε>0 : ε > 0) where

      private
        cont-prop : ℝ → Type
        cont-prop δ = (y : ℝ) ⦃ _ : y ∈ 𝔻 ⦄ → abs (x - y) < δ → abs (f .fun x - f .fun y) < ε

        isPropCont : (δ : ℝ) → isProp (cont-prop δ)
        isPropCont δ p q i y -<- = isProp< (p y -<-) (q y -<-) i

        cont-<-close : (δ' δ : ℝ) → δ' > 0 → δ' < δ → cont-prop δ → cont-prop δ'
        cont-<-close δ' δ _ δ'<δ ε-δ y ∣x-y∣<δ' = ε-δ y (<-trans ∣x-y∣<δ' δ'<δ)

      -- The ε-δ formulation can be lifted from mere existence to an explicit δ.

      contΣ : Σ[ δ ∈ ℝ ] (δ > 0) × ((y : ℝ) ⦃ _ : y ∈ 𝔻 ⦄ → abs (x - y) < δ → abs (f .fun x - f .fun y) < ε)
      contΣ = findExplicit
        (ℝMacNeilleCompleteOrderedField .fst)
        (isMacNeilleComplete→isArchimedean (ℝMacNeilleCompleteOrderedField .snd))
        isPropCont (λ _ → decide (isPropCont _)) cont-<-close (f .cont x ε ε>0)


    -- If a continuous function has positive/negative value at some point x,
    -- it has positive/negative values all over a small neighbourhood of x.

    keepSign+ : (x : ℝ) ⦃ _ : x ∈ 𝔻 ⦄ → f .fun x > 0
      → Σ[ δ ∈ ℝ ] (δ > 0) × ((y : ℝ) ⦃ _ : y ∈ 𝔻 ⦄ → abs (x - y) < δ → f .fun y > 0)
    keepSign+ x fx>0 =
      let (δ , δ>0 , ε-δ) = contΣ x (f .fun x) fx>0 in
      δ , δ>0 , (λ y ∣x-y∣<δ → absKeepSign+ fx>0 (ε-δ y ∣x-y∣<δ))

    keepSign- : (x : ℝ) ⦃ _ : x ∈ 𝔻 ⦄ → f .fun x < 0
      → Σ[ δ ∈ ℝ ] (δ > 0) × ((y : ℝ) ⦃ _ : y ∈ 𝔻 ⦄ → abs (x - y) < δ → f .fun y < 0)
    keepSign- x fx<0 =
      let (δ , δ>0 , ε-δ) = contΣ x (- f .fun x) (-Reverse<0 fx<0) in
      δ , δ>0 , (λ y ∣x-y∣<δ → absKeepSign- fx<0 (ε-δ y ∣x-y∣<δ))


  {-

    Intermediate Value Theorem

  -}


  -- The Unit Interval [0,1]

  module _ where

    𝐈-prop : ℝ → hProp _
    𝐈-prop x = (0 ≤ x) × (x ≤ 1) , isProp× isProp≤ isProp≤

    𝐈 : ℙ ℝ
    𝐈 = specify 𝐈-prop

    instance
      0∈𝐈 : 0 ∈ 𝐈
      0∈𝐈 = Inhab→∈ 𝐈-prop (≤-refl refl , <-≤-weaken 1>0)

      1∈𝐈 : 1 ∈ 𝐈
      1∈𝐈 = Inhab→∈ 𝐈-prop (<-≤-weaken 1>0 , ≤-refl refl)


  -- Given a continuous function defined on the unit interval,
  -- if its values at end-points have different signs,
  -- the function admits a zero point inside the interval.
  -- Notice that the zero `really` exists, rather than merely existing.

  findZero : (f : ContinuousFunction 𝐈) → f .fun 0 < 0 → f .fun 1 > 0 → Σ[ x ∈ ℝ ] Σ[ x∈𝐈 ∈ x ∈ 𝐈 ] f .fun x ⦃ x∈𝐈 ⦄ ≡ 0
  findZero f f0<0 f1>0 = x₀ , x₀∈𝐈 , fx₀≡0
    where

    open Helpers  (LinearlyOrderedCommRing→CommRing (ℝMacNeilleCompleteOrderedField .fst .fst))

    open Extremum (ℝMacNeilleCompleteOrderedField .fst)
    open Supremum

    getSup = ℝMacNeilleCompleteOrderedField .snd

    f<0-prop : ℝ → hProp _
    f<0-prop x = (Σ[ x∈𝐈 ∈ x ∈ 𝐈 ] f .fun x ⦃ x∈𝐈 ⦄ < 0) , isPropΣ (isProp∈ 𝐈) (λ _ → isProp<)

    f<0-sub : ℙ ℝ
    f<0-sub = specify f<0-prop

    0≤x∈sub : (x : ℝ) → x ∈ f<0-sub → x ≥ 0
    0≤x∈sub x x∈sub = ∈→Inhab 𝐈-prop (∈→Inhab f<0-prop x∈sub .fst) .fst

    1≥x∈sub : (x : ℝ) → x ∈ f<0-sub → x ≤ 1
    1≥x∈sub x x∈sub = ∈→Inhab 𝐈-prop (∈→Inhab f<0-prop x∈sub .fst) .snd

    f<0-sup : Supremum f<0-sub
    f<0-sup = getSup ∣ 0 , 0∈sub ∣₁ ∣ 1 , 1≥x∈sub ∣₁
      where
      0∈sub : 0 ∈ f<0-sub
      0∈sub = Inhab→∈ f<0-prop (0∈𝐈 , f0<0)

    x₀ = f<0-sup .sup

    0≤x₀ : 0 ≤ x₀
    0≤x₀ = supLowerBounded _ f<0-sup 0≤x∈sub

    x₀≤1 : x₀ ≤ 1
    x₀≤1 = supUpperBounded _ f<0-sup 1≥x∈sub

    instance
      x₀∈𝐈 : x₀ ∈ 𝐈
      x₀∈𝐈 = Inhab→∈ 𝐈-prop (0≤x₀ , x₀≤1)

    module _ (fx₀<0 : f .fun x₀ < 0) where

      x₀<1 : x₀ < 1
      x₀<1 = case-split (trichotomy x₀ 1)
        where
        case-split : Trichotomy (ℝMacNeilleCompleteOrderedField .fst .fst .fst) x₀ 1 → _
        case-split (lt x₀<1) = x₀<1
        case-split (eq x₀≡1) = Empty.rec (<-asym f1>0 f1<0)
          where
          ∈-path : PathP (λ i → x₀≡1 i ∈ 𝐈) x₀∈𝐈 1∈𝐈
          ∈-path = isProp→PathP (λ i → isProp∈ 𝐈) x₀∈𝐈 1∈𝐈
          f1<0 : f .fun 1 ⦃ _ ⦄ < 0
          f1<0 = subst (_< 0) (λ i → f .fun (x₀≡1 i) ⦃ ∈-path i ⦄) fx₀<0
        case-split (gt x₀>1) = Empty.rec (<≤-asym x₀>1 x₀≤1)

      private
        δ₀-triple = keepSign- _ f x₀ fx₀<0
        δ-tetrad = min2 (>→Diff>0 x₀<1) (δ₀-triple .snd .fst)

        δ : ℝ
        δ = δ-tetrad .fst

        δ>0 : δ > 0
        δ>0 = δ-tetrad .snd .fst

        x₀<x₀+δ : x₀ < x₀ + δ
        x₀<x₀+δ = +-rPos→> δ>0

        x₀+δ<1 : x₀ + δ < 1
        x₀+δ<1 = subst (x₀ + δ <_) (helper1 _) (+-lPres< (δ-tetrad .snd .snd .fst))

        instance
          x₀+δ∈𝐈 : (x₀ + δ) ∈ 𝐈
          x₀+δ∈𝐈 = Inhab→∈ 𝐈-prop (<-≤-weaken (≤<-trans 0≤x₀ x₀<x₀+δ) , <-≤-weaken x₀+δ<1)

        abs<δ₀ : abs (x₀ - (x₀ + δ)) < δ₀-triple .fst
        abs<δ₀ = subst (_< δ₀-triple .fst)
          (sym (x>0→abs≡x δ>0) ∙ absx≡→abs-x ∙ (λ i → abs (helper2 x₀ δ (~ i))))
          (δ-tetrad .snd .snd .snd)

      ¬fx₀<0 : ⊥
      ¬fx₀<0 = <≤-asym x₀<x₀+δ (f<0-sup .bound _ (Inhab→∈ f<0-prop (_ , δ₀-triple .snd .snd _ abs<δ₀)))

    module _ (fx₀>0 : f .fun x₀ > 0) where

      x₀>0 : x₀ > 0
      x₀>0 = case-split (trichotomy x₀ 0)
        where
        case-split : Trichotomy (ℝMacNeilleCompleteOrderedField .fst .fst .fst) x₀ 0 → _
        case-split (lt x₀<0) = Empty.rec (<≤-asym x₀<0 0≤x₀)
        case-split (eq x₀≡0) = Empty.rec (<-asym f0>0 f0<0)
          where
          ∈-path : PathP (λ i → x₀≡0 i ∈ 𝐈) x₀∈𝐈 0∈𝐈
          ∈-path = isProp→PathP (λ i → isProp∈ 𝐈) x₀∈𝐈 0∈𝐈
          f0>0 : f .fun 0 ⦃ _ ⦄ > 0
          f0>0 = subst (_> 0) (λ i → f .fun (x₀≡0 i) ⦃ ∈-path i ⦄) fx₀>0
        case-split (gt x₀>0) = x₀>0

      δ₀-triple = keepSign+ _ f x₀ fx₀>0
      δ-tetrad = min2 x₀>0 (δ₀-triple .snd .fst)

      δ₀ : ℝ
      δ₀ = δ₀-triple .fst

      δ : ℝ
      δ = δ-tetrad .fst

      δ>0 : δ > 0
      δ>0 = δ-tetrad .snd .fst

      x₀-δ<x₀ : x₀ - δ < x₀
      x₀-δ<x₀ = -rPos→< δ>0

      0<x₀-δ : 0 < x₀ - δ
      0<x₀-δ = >→Diff>0 (δ-tetrad .snd .snd .fst)

      instance
        x₀+δ∈𝐈 : (x₀ - δ) ∈ 𝐈
        x₀+δ∈𝐈 = Inhab→∈ 𝐈-prop (<-≤-weaken 0<x₀-δ , <-≤-weaken (<≤-trans x₀-δ<x₀ x₀≤1))

      abs<δ₀ : abs (x₀ - (x₀ - δ)) < δ₀
      abs<δ₀ = subst (_< δ₀) (sym (x>0→abs≡x δ>0) ∙ (λ i → abs (helper3 x₀ δ (~ i)))) (δ-tetrad .snd .snd .snd)

      ∃between : ∥ Σ[ x ∈ ℝ ] (x₀ - δ < x) × (x ∈ f<0-sub) ∥₁
      ∃between = <sup→∃∈ _ f<0-sup x₀-δ<x₀

      ¬fx₀>0 : ⊥
      ¬fx₀>0 =
        proof _ , isProp⊥ by do
        (x , x₀-δ<x , x∈sub) ← ∃between
        let x≤x₀ : x ≤ x₀
            x≤x₀ = f<0-sup .bound _ x∈sub
            ∣x-x₀∣<δ₀ : abs (x₀ - x) < δ₀
            ∣x-x₀∣<δ₀ = ≤<-trans (absInBetween δ>0 (<-≤-weaken x₀-δ<x) x≤x₀) (δ-tetrad .snd .snd .snd)
            x-pair = ∈→Inhab f<0-prop x∈sub
            instance
              x∈𝐈 : x ∈ 𝐈
              x∈𝐈 = x-pair .fst
            fx<0 : f .fun x < 0
            fx<0 = x-pair .snd
            fx>0 : f .fun x > 0
            fx>0 = δ₀-triple .snd .snd x ∣x-x₀∣<δ₀
        return (<-asym fx<0 fx>0)

    fx₀≡0 : f .fun x₀ ≡ 0
    fx₀≡0 = case-split (trichotomy (f .fun x₀) 0)
      where
      case-split : Trichotomy (ℝMacNeilleCompleteOrderedField .fst .fst .fst) (f .fun x₀) 0 → _
      case-split (lt fx₀<0) = Empty.rec (¬fx₀<0 fx₀<0)
      case-split (eq fx₀≡0) = fx₀≡0
      case-split (gt fx₀>0) = Empty.rec (¬fx₀>0 fx₀>0)
