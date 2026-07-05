{-

Extension helpers for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Extension.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness.Properties
open import Constructive.CauchyReals.Continuity
open import Constructive.CauchyReals.Induction
open import Constructive.CauchyReals.Recursion public


close-limit-intro :
  (x : ℝᶜ) (y : CauchyApproximation) (ε δ : ℚ⁺) →
  (δ<ε : δ <⁺ ε) →
  x ∼[ ε ⊖ δ [ δ<ε ] ] approximate y δ →
  x ∼[ ε ] limit y
close-limit-intro x y ε δ δ<ε x∼yδ =
  computed→close x (limit y) ε
    (targetLimitIntro x y ε δ δ<ε (close→computed x∼yδ))


limit-close-intro :
  (x : CauchyApproximation) (y : ℝᶜ) (ε δ : ℚ⁺) →
  (δ<ε : δ <⁺ ε) →
  approximate x δ ∼[ ε ⊖ δ [ δ<ε ] ] y →
  limit x ∼[ ε ] y
limit-close-intro x y ε δ δ<ε xδ∼y =
  close-sym (close-limit-intro y x ε δ δ<ε (close-sym xδ∼y))


limit-limit-intro :
  (x y : CauchyApproximation) (ε δ η : ℚ⁺) →
  (δ+η<ε : δ +⁺ η <⁺ ε) →
  approximate x δ ∼[ ε ⊖ (δ +⁺ η) [ δ+η<ε ] ] approximate y η →
  limit x ∼[ ε ] limit y
limit-limit-intro =
  limit-limit-close


limit-approx-close :
  (x : CauchyApproximation) (ε : ℚ⁺) →
  limit x ∼[ ε ] approximate x (quarter⁺ ε)
limit-approx-close x ε =
  limit-close-intro x (approximate x δ) ε δ δ<ε
    (close-refl (approximate x δ) (ε ⊖ δ [ δ<ε ]))
  where
  δ : ℚ⁺
  δ = quarter⁺ ε

  δ<ε : δ <⁺ ε
  δ<ε = quarter< ε


IsRationalNonexpanding : (ℚ → ℝᶜ) → Type₀
IsRationalNonexpanding f =
  (q r : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  f q ∼[ ε ] f r


module _ (f : ℚ → ℝᶜ) (f-ne : IsRationalNonexpanding f) where
  private
    extensionKit : RecursionKit ℓ-zero ℓ-zero
    extensionKit .RecursionKit.A =
      ℝᶜ
    extensionKit .RecursionKit.B ε x y =
      x ∼[ ε ] y
    extensionKit .RecursionKit.isPropB ε x y =
      squash
    extensionKit .RecursionKit.separated =
      path
    extensionKit .RecursionKit.rational* =
      f
    extensionKit .RecursionKit.limit* x g gCauchy =
      limit (cauchy-approximation g gCauchy)
    extensionKit .RecursionKit.rational-rational* =
      f-ne
    extensionKit .RecursionKit.rational-limit* q ε δ δ<ε y g gCauchy q∼gδ =
      close-limit-intro
        (f q)
        (cauchy-approximation g gCauchy)
        ε δ δ<ε
        q∼gδ
    extensionKit .RecursionKit.limit-rational* x g gCauchy r ε δ δ<ε gδ∼r =
      limit-close-intro
        (cauchy-approximation g gCauchy)
        (f r)
        ε δ δ<ε
        gδ∼r
    extensionKit .RecursionKit.limit-limit* x y g h gCauchy hCauchy ε δ η δ+η<ε gδ∼hη =
      limit-limit-intro
        (cauchy-approximation g gCauchy)
        (cauchy-approximation h hCauchy)
        ε δ η δ+η<ε
        gδ∼hη

    module ExtensionRecursion = Recursion extensionKit

  extendNonexpanding : ℝᶜ → ℝᶜ
  extendNonexpanding =
    ExtensionRecursion.rec

  extendNonexpanding-rational :
    (q : ℚ) →
    extendNonexpanding (rational q) ≡ f q
  extendNonexpanding-rational q =
    refl

  extendNonexpanding-close :
    {x y : ℝᶜ} {ε : ℚ⁺} →
    x ∼[ ε ] y →
    extendNonexpanding x ∼[ ε ] extendNonexpanding y
  extendNonexpanding-close =
    ExtensionRecursion.rec-close

  extendNonexpanding-isNonexpanding :
    IsNonexpanding extendNonexpanding
  extendNonexpanding-isNonexpanding =
    extendNonexpanding-close

  extendNonexpanding-continuous :
    IsContinuous extendNonexpanding
  extendNonexpanding-continuous =
    nonexpanding→continuous extendNonexpanding-isNonexpanding


extensions-close :
  {f g : ℚ → ℝᶜ} →
  (f-ne : IsRationalNonexpanding f) →
  (g-ne : IsRationalNonexpanding g) →
  ((q : ℚ) (ε : ℚ⁺) → f q ∼[ ε ] g q) →
  (x : ℝᶜ) (ε : ℚ⁺) →
  extendNonexpanding f f-ne x ∼[ ε ] extendNonexpanding g g-ne x
extensions-close {f = f} {g = g} f-ne g-ne f∼g =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
  kit .PropInductionKit.A x =
    (ε : ℚ⁺) →
    extendNonexpanding f f-ne x ∼[ ε ] extendNonexpanding g g-ne x
  kit .PropInductionKit.isPropA x =
    isPropΠ λ ε →
      squash
  kit .PropInductionKit.rational* q =
    f∼g q
  kit .PropInductionKit.limit* x closeAt ε =
    limit-limit-intro
      (cauchy-approximation
        (λ δ → extendNonexpanding f f-ne (approximate x δ))
        (λ δ η → extendNonexpanding-close f f-ne (isRegular x δ η)))
      (cauchy-approximation
        (λ δ → extendNonexpanding g g-ne (approximate x δ))
        (λ δ η → extendNonexpanding-close g g-ne (isRegular x δ η)))
      ε δ δ δ+δ<ε
      (closeAt δ (ε ⊖ (δ +⁺ δ) [ δ+δ<ε ]))
    where
    δ : ℚ⁺
    δ = quarter⁺ ε

    δ+δ<ε : δ +⁺ δ <⁺ ε
    δ+δ<ε = quarter-sum< ε


extensions-equal :
  {f g : ℚ → ℝᶜ} →
  (f-ne : IsRationalNonexpanding f) →
  (g-ne : IsRationalNonexpanding g) →
  ((q : ℚ) → f q ≡ g q) →
  (x : ℝᶜ) →
  extendNonexpanding f f-ne x ≡ extendNonexpanding g g-ne x
extensions-equal {f = f} {g = g} f-ne g-ne f≡g x =
  path
    (extendNonexpanding f f-ne x)
    (extendNonexpanding g g-ne x)
    λ ε →
      extensions-close f-ne g-ne pointwise x ε
  where
  pointwise :
    (q : ℚ) (ε : ℚ⁺) →
    f q ∼[ ε ] g q
  pointwise q ε =
    subst
      (λ y → f q ∼[ ε ] y)
      (f≡g q)
      (close-refl (f q) ε)


nonexpanding-equal :
  (f g : ℝᶜ → ℝᶜ) →
  IsNonexpanding f →
  IsNonexpanding g →
  ((q : ℚ) → f (rational q) ≡ g (rational q)) →
  (x : ℝᶜ) →
  f x ≡ g x
nonexpanding-equal f g f-ne g-ne rational-path =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
  kit .PropInductionKit.A x =
    f x ≡ g x
  kit .PropInductionKit.isPropA x =
    isSetℝᶜ (f x) (g x)
  kit .PropInductionKit.rational* =
    rational-path
  kit .PropInductionKit.limit* x pointwise =
    path (f (limit x)) (g (limit x)) closeAt
    where
    closeAt : (ε : ℚ⁺) → f (limit x) ∼[ ε ] g (limit x)
    closeAt ε =
      close-mono {ε = (α +⁺ α) +⁺ α} {δ = ε}
        (three-quarter< ε)
        (close-triangle
          (close-triangle f-lim∼approx f-approx∼g-approx)
          g-approx∼lim)
      where
      α : ℚ⁺
      α = quarter⁺ ε

      δ : ℚ⁺
      δ = quarter⁺ α

      lim∼approx : limit x ∼[ α ] approximate x δ
      lim∼approx =
        limit-approx-close x α

      f-lim∼approx : f (limit x) ∼[ α ] f (approximate x δ)
      f-lim∼approx =
        f-ne lim∼approx

      f-approx∼g-approx : f (approximate x δ) ∼[ α ] g (approximate x δ)
      f-approx∼g-approx =
        subst
          (λ y → f (approximate x δ) ∼[ α ] y)
          (pointwise δ)
          (close-refl (f (approximate x δ)) α)

      g-approx∼lim : g (approximate x δ) ∼[ α ] g (limit x)
      g-approx∼lim =
        g-ne (close-sym lim∼approx)


continuous-equal :
  (f g : ℝᶜ → ℝᶜ) →
  IsContinuous f →
  IsContinuous g →
  ((q : ℚ) → f (rational q) ≡ g (rational q)) →
  (x : ℝᶜ) →
  f x ≡ g x
continuous-equal f g f-cont g-cont rational-path =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
  kit .PropInductionKit.A x =
    f x ≡ g x
  kit .PropInductionKit.isPropA x =
    isSetℝᶜ (f x) (g x)
  kit .PropInductionKit.rational* =
    rational-path
  kit .PropInductionKit.limit* x pointwise =
    path (f (limit x)) (g (limit x)) closeAt
    where
    closeAt : (ε : ℚ⁺) → f (limit x) ∼[ ε ] g (limit x)
    closeAt ε =
      close-mono {ε = (α +⁺ α) +⁺ α} {δ = ε}
        (three-quarter< ε)
        (close-triangle
          (close-triangle f-lim∼approx f-approx∼g-approx)
          g-approx∼lim)
      where
      α : ℚ⁺
      α = quarter⁺ ε

      μf μg : ℚ⁺
      μf = fst (f-cont α)
      μg = fst (g-cont α)

      μ : ℚ⁺
      μ = min⁺ μf μg

      β : ℚ⁺
      β = half⁺ μ

      δ : ℚ⁺
      δ = quarter⁺ β

      lim∼approx : limit x ∼[ β ] approximate x δ
      lim∼approx =
        limit-approx-close x β

      lim∼approx-f : limit x ∼[ μf ] approximate x δ
      lim∼approx-f =
        close-mono (half-min⁺<left μf μg) lim∼approx

      lim∼approx-g : limit x ∼[ μg ] approximate x δ
      lim∼approx-g =
        close-mono (half-min⁺<right μf μg) lim∼approx

      f-lim∼approx : f (limit x) ∼[ α ] f (approximate x δ)
      f-lim∼approx =
        snd (f-cont α) lim∼approx-f

      f-approx∼g-approx : f (approximate x δ) ∼[ α ] g (approximate x δ)
      f-approx∼g-approx =
        subst
          (λ y → f (approximate x δ) ∼[ α ] y)
          (pointwise δ)
          (close-refl (f (approximate x δ)) α)

      g-approx∼lim : g (approximate x δ) ∼[ α ] g (limit x)
      g-approx∼lim =
        snd (g-cont α) (close-sym lim∼approx-g)


continuous-constant-equal :
  (f : ℝᶜ → ℝᶜ) →
  (c : ℝᶜ) →
  IsContinuous f →
  ((q : ℚ) → f (rational q) ≡ c) →
  (x : ℝᶜ) →
  f x ≡ c
continuous-constant-equal f c f-cont rational-path =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
  kit .PropInductionKit.A x =
    f x ≡ c
  kit .PropInductionKit.isPropA x =
    isSetℝᶜ (f x) c
  kit .PropInductionKit.rational* =
    rational-path
  kit .PropInductionKit.limit* x pointwise =
    path (f (limit x)) c closeAt
    where
    closeAt : (ε : ℚ⁺) → f (limit x) ∼[ ε ] c
    closeAt ε =
      close-mono {ε = α +⁺ α} {δ = ε}
        (quarter-sum< ε)
        (close-triangle f-lim∼approx f-approx∼c)
      where
      α : ℚ⁺
      α = quarter⁺ ε

      μ : ℚ⁺
      μ = fst (f-cont α)

      f-close : {x y : ℝᶜ} → x ∼[ μ ] y → f x ∼[ α ] f y
      f-close = snd (f-cont α)

      δ : ℚ⁺
      δ = quarter⁺ μ

      lim∼approx : limit x ∼[ μ ] approximate x δ
      lim∼approx =
        limit-approx-close x μ

      f-lim∼approx : f (limit x) ∼[ α ] f (approximate x δ)
      f-lim∼approx =
        f-close lim∼approx

      f-approx∼c : f (approximate x δ) ∼[ α ] c
      f-approx∼c =
        subst
          (λ y → f (approximate x δ) ∼[ α ] y)
          (pointwise δ)
          (close-refl (f (approximate x δ)) α)


IsBinaryRationalNonexpandingLeft : (ℚ → ℚ → ℝᶜ) → Type₀
IsBinaryRationalNonexpandingLeft f =
  (q r s : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  f q s ∼[ ε ] f r s


IsBinaryRationalNonexpandingRight : (ℚ → ℚ → ℝᶜ) → Type₀
IsBinaryRationalNonexpandingRight f =
  (q : ℚ) → IsRationalNonexpanding (f q)


module _
  (f : ℚ → ℚ → ℝᶜ)
  (left-ne : IsBinaryRationalNonexpandingLeft f)
  (right-ne : IsBinaryRationalNonexpandingRight f)
  where

  private
    rightExtension : ℚ → ℝᶜ → ℝᶜ
    rightExtension q =
      extendNonexpanding (f q) (right-ne q)

    rightExtension-approx :
      ℚ →
      CauchyApproximation →
      CauchyApproximation
    rightExtension-approx q x =
      cauchy-approximation
        (λ δ → rightExtension q (approximate x δ))
        (λ δ η → extendNonexpanding-close (f q) (right-ne q) (isRegular x δ η))

    rounded-gap-step :
      {P : Type₀} →
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
      gap = ε ⊖ ζ [ ζ<ε ]

      δ : ℚ⁺
      δ = quarter⁺ gap

      δ+δ : ℚ⁺
      δ+δ = δ +⁺ δ

      δ+δ<gap : δ+δ <⁺ gap
      δ+δ<gap = quarter-sum< gap

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
      (q r : ℚ) (y : ℝᶜ) (ε : ℚ⁺) →
      Closeℚ q ε r →
      rightExtension q y ∼[ ε ] rightExtension r y
    rightExtension-left-close q r =
      PropInduction.ind kit
      where
      kit : PropInductionKit ℓ-zero
      kit .PropInductionKit.A y =
        (ε : ℚ⁺) →
        Closeℚ q ε r →
        rightExtension q y ∼[ ε ] rightExtension r y
      kit .PropInductionKit.isPropA y =
        isPropΠ2 λ ε _ →
          squash
      kit .PropInductionKit.rational* s ε q∼r =
        left-ne q r s ε q∼r
      kit .PropInductionKit.limit* x closeAt ε q∼r =
        Prop.rec squash step (rational-close-rounded q r ε q∼r)
        where
        step :
          Σ[ ζ ∈ ℚ⁺ ] (ζ <⁺ ε) × Closeℚ q ζ r →
          rightExtension q (limit x) ∼[ ε ] rightExtension r (limit x)
        step (ζ , ζ<ε , q∼rζ) =
          rounded-gap-step ε ζ ζ<ε λ δ δ+δ<ε ζ<ε-δδ →
            limit-limit-intro
              (rightExtension-approx q x)
              (rightExtension-approx r x)
              ε δ δ δ+δ<ε
              (close-mono ζ<ε-δδ (closeAt δ ζ q∼rζ))

  extendBinaryNonexpanding : ℝᶜ → ℝᶜ → ℝᶜ
  extendBinaryNonexpanding x y =
    extendNonexpanding
      (λ q → rightExtension q y)
      (λ q r ε q∼r → rightExtension-left-close q r y ε q∼r)
      x

  extendBinaryNonexpanding-rational-left :
    (q : ℚ) (y : ℝᶜ) →
    extendBinaryNonexpanding (rational q) y ≡
    extendNonexpanding (f q) (right-ne q) y
  extendBinaryNonexpanding-rational-left q y =
    refl

  extendBinaryNonexpanding-rational-rational :
    (q r : ℚ) →
    extendBinaryNonexpanding (rational q) (rational r) ≡ f q r
  extendBinaryNonexpanding-rational-rational q r =
    refl

  extendBinaryNonexpanding-rational-right :
    (x : ℝᶜ) (r : ℚ) →
    extendBinaryNonexpanding x (rational r) ≡
    extendNonexpanding
      (λ q → f q r)
      (λ q s ε q∼s → left-ne q s r ε q∼s)
      x
  extendBinaryNonexpanding-rational-right x r =
    extensions-equal
      (λ q s ε q∼s → rightExtension-left-close q s (rational r) ε q∼s)
      (λ q s ε q∼s → left-ne q s r ε q∼s)
      (λ q → refl)
      x

  extendBinaryNonexpanding-close-left :
    {x y : ℝᶜ} {ε : ℚ⁺} →
    x ∼[ ε ] y →
    (z : ℝᶜ) →
    extendBinaryNonexpanding x z ∼[ ε ] extendBinaryNonexpanding y z
  extendBinaryNonexpanding-close-left {ε = ε} x∼y z =
    extendNonexpanding-close
      (λ q → rightExtension q z)
      (λ q r ε q∼r → rightExtension-left-close q r z ε q∼r)
      x∼y

  private
    binary-left-approx :
      CauchyApproximation →
      ℝᶜ →
      CauchyApproximation
    binary-left-approx x y =
      cauchy-approximation
        (λ δ → extendBinaryNonexpanding (approximate x δ) y)
        (λ δ η → extendBinaryNonexpanding-close-left (isRegular x δ η) y)

  extendBinaryNonexpanding-close-right :
    (x : ℝᶜ) →
    {y z : ℝᶜ} {ε : ℚ⁺} →
    y ∼[ ε ] z →
    extendBinaryNonexpanding x y ∼[ ε ] extendBinaryNonexpanding x z
  extendBinaryNonexpanding-close-right =
    PropInduction.ind kit
    where
    kit : PropInductionKit ℓ-zero
    kit .PropInductionKit.A x =
      {y z : ℝᶜ} {ε : ℚ⁺} →
      y ∼[ ε ] z →
      extendBinaryNonexpanding x y ∼[ ε ] extendBinaryNonexpanding x z
    kit .PropInductionKit.isPropA x =
      isPropImplicitΠ3 λ y z ε →
        isPropΠ λ _ →
          squash
    kit .PropInductionKit.rational* q =
      extendNonexpanding-close (f q) (right-ne q)
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
    {x y z w : ℝᶜ} {η ε : ℚ⁺} →
    x ∼[ η ] y →
    z ∼[ ε ] w →
    extendBinaryNonexpanding x z ∼[ η +⁺ ε ] extendBinaryNonexpanding y w
  extendBinaryNonexpanding-close {y = y} {z = z} x∼y z∼w =
    close-triangle
      (extendBinaryNonexpanding-close-left x∼y z)
      (extendBinaryNonexpanding-close-right y z∼w)
