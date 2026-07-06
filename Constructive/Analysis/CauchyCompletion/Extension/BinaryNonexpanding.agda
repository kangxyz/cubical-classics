{-

Binary nonexpanding extension over Cauchy completions

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.CauchyCompletion.Extension.BinaryNonexpanding where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.CauchyCompletion.Base
open import Constructive.Analysis.CauchyCompletion.Closeness.ReflexiveSymmetric
open import Constructive.Analysis.CauchyCompletion.Closeness.Internal.Computed
open import Constructive.Analysis.CauchyCompletion.Closeness.Internal.Prelength
open import Constructive.Analysis.CauchyCompletion.Closeness.Rounded
open import Constructive.Analysis.CauchyCompletion.Complete
open import Constructive.Analysis.CauchyCompletion.Extension.Core
open import Constructive.Analysis.CauchyCompletion.Induction
open import Constructive.Data.PositiveRationals

private
  variable
    ℓ ℓ' : Level


module BinaryNonexpandingExtensionOf (𝓜 : MetricSpace ℓ ℓ') where
  open CompletionOf 𝓜
  open ClosenessOf 𝓜
  open ComputedOf 𝓜
    using (close-triangle)
  open RoundedOf 𝓜
  open CompleteOf 𝓜
  open ExtensionOf 𝓜
  open InductionOf 𝓜
  open PrelengthOf 𝓜
    using (difference-from-sum<)

  private
    A : Type ℓ
    A =
      MetricSpace.Carrier 𝓜

    ℓᶜ : Level
    ℓᶜ =
      ℓ-max ℓ ℓ'


  IsBinaryPointNonexpandingLeft :
    (A → A → Completion) →
    Type (ℓ-max ℓ ℓ')
  IsBinaryPointNonexpandingLeft f =
    (a b c : A) (ε : ℚ⁺) →
    MetricSpace.Close 𝓜 a ε b →
    f a c ∼[ ε ] f b c


  IsBinaryPointNonexpandingRight :
    (A → A → Completion) →
    Type (ℓ-max ℓ ℓ')
  IsBinaryPointNonexpandingRight f =
    (a : A) →
    {b c : A} {ε : ℚ⁺} →
    MetricSpace.Close 𝓜 b ε c →
    f a b ∼[ ε ] f a c


  module BinaryNonexpandingExtension
    (f : A → A → Completion)
    (left-ne : IsBinaryPointNonexpandingLeft f)
    (right-ne : IsBinaryPointNonexpandingRight f)
    where

    private
      module Right (a : A) =
        NonexpandingExtension
          CauchyCompletionMetricSpace
          isComplete
          (f a)
          (right-ne a)

      rightExtension : A → Completion → Completion
      rightExtension a =
        Right.extend a

      rightExtension-approx :
        A →
        CauchyApproximation →
        CauchyApproximation
      rightExtension-approx a x =
        cauchy-approximation
          (λ δ → rightExtension a (approximate x δ))
          (λ δ η → Right.extend-close a (isRegular x δ η))

      rounded-gap-step :
        {P : Type ℓᶜ} →
        (ε ζ : ℚ⁺) →
        ζ <⁺ ε →
        (∀ δ →
          (δ+δ<ε : δ +⁺ δ <⁺ ε) →
          ζ <⁺ ε ⊖ (δ +⁺ δ) [ δ+δ<ε ] →
          P) →
        P
      rounded-gap-step ε ζ ζ<ε k =
        k δ δδ<ε ζ<ε-δδ
        where
        gap : ℚ⁺
        gap =
          ε ⊖ ζ [ ζ<ε ]

        δ : ℚ⁺
        δ =
          quarter⁺ gap

        δ+δ : ℚ⁺
        δ+δ =
          δ +⁺ δ

        δ+δ<gap : δ+δ <⁺ gap
        δ+δ<gap =
          quarter-sum< gap

        ζ+δδ<ε : ζ +⁺ δ+δ <⁺ ε
        ζ+δδ<ε =
          sum<from-difference ε ζ δ+δ ζ<ε δ+δ<gap

        δδ<ε : δ+δ <⁺ ε
        δδ<ε =
          <⁺-trans
            {ε = δ+δ}
            {δ = ζ +⁺ δ+δ}
            {η = ε}
            (summand-right<sum ζ δ+δ)
            ζ+δδ<ε

        δδ+ζ<ε : δ+δ +⁺ ζ <⁺ ε
        δδ+ζ<ε =
          subst
            (λ ρ → ρ <⁺ ε)
            (+⁺-comm ζ δ+δ)
            ζ+δδ<ε

        ζ<ε-δδ : ζ <⁺ ε ⊖ δ+δ [ δδ<ε ]
        ζ<ε-δδ =
          difference-from-sum< ε δ+δ ζ δδ+ζ<ε

      rightExtension-left-close :
        (a b : A) (y : Completion) (ε : ℚ⁺) →
        MetricSpace.Close 𝓜 a ε b →
        rightExtension a y ∼[ ε ] rightExtension b y
      rightExtension-left-close a b =
        PropInduction.ind kit
        where
        kit : PropInductionKit ℓᶜ
        kit .PropInductionKit.A y =
          (ε : ℚ⁺) →
          MetricSpace.Close 𝓜 a ε b →
          rightExtension a y ∼[ ε ] rightExtension b y
        kit .PropInductionKit.isPropA y =
          isPropΠ2 λ ε _ →
            squash
        kit .PropInductionKit.point* c ε a∼b =
          left-ne a b c ε a∼b
        kit .PropInductionKit.limit* x closeAt ε a∼b =
          Prop.rec squash step (MetricSpace.close-rounded 𝓜 a∼b)
          where
          step :
            Σ[ ζ ∈ ℚ⁺ ] (ζ <⁺ ε) × MetricSpace.Close 𝓜 a ζ b →
            rightExtension a (limit x) ∼[ ε ] rightExtension b (limit x)
          step (ζ , ζ<ε , a∼bζ) =
            rounded-gap-step ε ζ ζ<ε λ δ δ+δ<ε ζ<ε-δδ →
              limit-limit-intro
                (rightExtension-approx a x)
                (rightExtension-approx b x)
                ε δ δ δ+δ<ε
                (close-mono ζ<ε-δδ (closeAt δ ζ a∼bζ))

    extendBinaryNonexpanding : Completion → Completion → Completion
    extendBinaryNonexpanding x y =
      NonexpandingExtension.extend
        CauchyCompletionMetricSpace
        isComplete
        (λ a → rightExtension a y)
        (λ {x = a} {y = b} {ε = ε} →
          rightExtension-left-close a b y ε)
        x


    extendBinaryNonexpanding-point-left :
      (a : A) (y : Completion) →
      extendBinaryNonexpanding (point a) y ≡
      rightExtension a y
    extendBinaryNonexpanding-point-left a y =
      refl


    extendBinaryNonexpanding-point-point :
      (a b : A) →
      extendBinaryNonexpanding (point a) (point b) ≡ f a b
    extendBinaryNonexpanding-point-point a b =
      refl


    extendBinaryNonexpanding-point-right :
      (x : Completion) (b : A) →
      extendBinaryNonexpanding x (point b) ≡
      NonexpandingExtension.extend
        CauchyCompletionMetricSpace
        isComplete
        (λ a → f a b)
        (λ {x = a} {y = c} {ε = ε} → left-ne a c b ε)
        x
    extendBinaryNonexpanding-point-right x b =
      NonexpandingExtension.extend-unique
        CauchyCompletionMetricSpace
        isComplete
        (λ a → f a b)
        (λ {x = a} {y = c} {ε = ε} → left-ne a c b ε)
        (λ y → extendBinaryNonexpanding y (point b))
        (λ {x = y} {y = z} {ε = ε} →
          NonexpandingExtension.extend-close
            CauchyCompletionMetricSpace
            isComplete
            (λ a → rightExtension a (point b))
            (λ {x = a} {y = c} {ε = ε} →
              rightExtension-left-close a c (point b) ε))
        (λ a → refl)
        x


    extendBinaryNonexpanding-close-left :
      {x y : Completion} {ε : ℚ⁺} →
      x ∼[ ε ] y →
      (z : Completion) →
      extendBinaryNonexpanding x z ∼[ ε ] extendBinaryNonexpanding y z
    extendBinaryNonexpanding-close-left x∼y z =
      NonexpandingExtension.extend-close
        CauchyCompletionMetricSpace
        isComplete
        (λ a → rightExtension a z)
        (λ {x = a} {y = b} {ε = ε} →
          rightExtension-left-close a b z ε)
        x∼y


    private
      binary-left-approx :
        CauchyApproximation →
        Completion →
        CauchyApproximation
      binary-left-approx x y =
        cauchy-approximation
          (λ δ → extendBinaryNonexpanding (approximate x δ) y)
          (λ δ η → extendBinaryNonexpanding-close-left (isRegular x δ η) y)

    extendBinaryNonexpanding-close-right :
      (x : Completion) →
      {y z : Completion} {ε : ℚ⁺} →
      y ∼[ ε ] z →
      extendBinaryNonexpanding x y ∼[ ε ] extendBinaryNonexpanding x z
    extendBinaryNonexpanding-close-right =
      PropInduction.ind kit
      where
      kit : PropInductionKit ℓᶜ
      kit .PropInductionKit.A x =
        {y z : Completion} {ε : ℚ⁺} →
        y ∼[ ε ] z →
        extendBinaryNonexpanding x y ∼[ ε ] extendBinaryNonexpanding x z
      kit .PropInductionKit.isPropA x =
        isPropImplicitΠ3 λ y z ε →
          isPropΠ λ _ →
            squash
      kit .PropInductionKit.point* a =
        Right.extend-close a
      kit .PropInductionKit.limit* x closeAt {y = y} {z = z} {ε = ε} y∼z =
        Prop.rec squash step (close-rounded y∼z)
        where
        step :
          Σ[ ζ ∈ ℚ⁺ ] (ζ <⁺ ε) × (y ∼[ ζ ] z) →
          extendBinaryNonexpanding (limit x) y
            ∼[ ε ]
          extendBinaryNonexpanding (limit x) z
        step (ζ , ζ<ε , y∼zζ) =
          rounded-gap-step ε ζ ζ<ε λ δ δ+δ<ε ζ<ε-δδ →
            limit-limit-intro
              (binary-left-approx x y)
              (binary-left-approx x z)
              ε δ δ δ+δ<ε
              (close-mono ζ<ε-δδ (closeAt δ y∼zζ))


    extendBinaryNonexpanding-close :
      {x y z w : Completion} {η ε : ℚ⁺} →
      x ∼[ η ] y →
      z ∼[ ε ] w →
      extendBinaryNonexpanding x z ∼[ η +⁺ ε ] extendBinaryNonexpanding y w
    extendBinaryNonexpanding-close {y = y} {z = z} x∼y z∼w =
      close-triangle
        (extendBinaryNonexpanding-close-left x∼y z)
        (extendBinaryNonexpanding-close-right y z∼w)
