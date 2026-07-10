{-

Banach fixed-point theorem

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.FixedPoint.Banach where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; ΣPathP)

open import Constructive.Analysis.GeometricDecay.Rate
open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Cauchy
open import Constructive.Analysis.Modulus
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational
open import Constructive.Analysis.FixedPoint.Base
open import Constructive.Analysis.FixedPoint.Iteration

private
  variable
    ℓ ℓ' : Level


record BanachProblem (𝓜 : MetricSpace ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    complete :
      IsCauchyComplete 𝓜

    contraction :
      Contraction 𝓜

    seed :
      PicardSeed 𝓜 (Contraction.map contraction)


banachApproximation :
  (𝓜 : MetricSpace ℓ ℓ') →
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  IsContractionWith 𝓜 ρ f →
  (x₀ : MetricSpace.Carrier 𝓜) →
  (η : ℚ⁺) →
  MetricSpace.Close 𝓜 x₀ η (f x₀) →
  CauchyApproximation 𝓜
banachApproximation =
  picardCauchyApproximation


banachLimit :
  (𝓜 : MetricSpace ℓ ℓ') →
  IsCauchyComplete 𝓜 →
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  IsContractionWith 𝓜 ρ f →
  (x₀ : MetricSpace.Carrier 𝓜) →
  (η : ℚ⁺) →
  MetricSpace.Close 𝓜 x₀ η (f x₀) →
  MetricSpace.Carrier 𝓜
banachLimit 𝓜 complete ρ ρ<1 f-contr x₀ η x₀∼fx₀ =
  limitPoint (complete (banachApproximation 𝓜 ρ ρ<1 f-contr x₀ η x₀∼fx₀))


banachLimitConverges :
  (𝓜 : MetricSpace ℓ ℓ') →
  (complete : IsCauchyComplete 𝓜) →
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  (f-contr : IsContractionWith 𝓜 ρ f) →
  (x₀ : MetricSpace.Carrier 𝓜) →
  (η : ℚ⁺) →
  (x₀∼fx₀ : MetricSpace.Close 𝓜 x₀ η (f x₀)) →
  ConvergesTo
    (banachApproximation 𝓜 ρ ρ<1 f-contr x₀ η x₀∼fx₀)
    (banachLimit 𝓜 complete ρ ρ<1 f-contr x₀ η x₀∼fx₀)
banachLimitConverges 𝓜 complete ρ ρ<1 f-contr x₀ η x₀∼fx₀ =
  converges (complete (banachApproximation 𝓜 ρ ρ<1 f-contr x₀ η x₀∼fx₀))


private
  n≤sucn : (n : ℕ) → NatOrder._≤_ n (suc n)
  n≤sucn n =
    suc zero , refl

  n≤n : (n : ℕ) → NatOrder._≤_ n n
  n≤n n =
    zero , refl


banachLimitFixed :
  (𝓜 : MetricSpace ℓ ℓ') →
  (complete : IsCauchyComplete 𝓜) →
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  (f-contr : IsContractionWith 𝓜 ρ f) →
  (x₀ : MetricSpace.Carrier 𝓜) →
  (η : ℚ⁺) →
  (x₀∼fx₀ : MetricSpace.Close 𝓜 x₀ η (f x₀)) →
  let p = banachLimit 𝓜 complete ρ ρ<1 f-contr x₀ η x₀∼fx₀ in
  f p ≡ p
banachLimitFixed 𝓜 complete ρ ρ<1 {f = f} f-contr x₀ η x₀∼fx₀ =
  MetricSpace.close-separated 𝓜 (f p) p fixed-close
  where
  μ : NatModulus
  μ =
    scaledGeometricSegmentModulus ρ ρ<1 η

  approximation : CauchyApproximation 𝓜
  approximation =
    banachApproximation 𝓜 ρ ρ<1 f-contr x₀ η x₀∼fx₀

  p : MetricSpace.Carrier 𝓜
  p =
    banachLimit 𝓜 complete ρ ρ<1 f-contr x₀ η x₀∼fx₀

  p-converges : ConvergesTo approximation p
  p-converges =
    banachLimitConverges 𝓜 complete ρ ρ<1 f-contr x₀ η x₀∼fx₀

  fixed-close :
    (ε : ℚ⁺) →
    MetricSpace.Close 𝓜 (f p) ε p
  fixed-close ε =
    MetricSpace.close-mono
      𝓜
      (three-quarter< ε)
      (MetricSpace.close-triangle
        𝓜
        {x = f p}
        {y = iterate f x₀ n}
        {z = p}
        {ε = α +⁺ α}
        {δ = α}
        fp∼xn+1∼xn
        xn∼p)
    where
    α : ℚ⁺
    α =
      quarter⁺ ε

    β : ℚ⁺
    β =
      quarter⁺ α

    β<α : β <⁺ α
    β<α =
      quarter< α

    n : ℕ
    n =
      μ (half⁺ β)

    p∼xn :
      MetricSpace.Close 𝓜 p α (iterate f x₀ n)
    p∼xn =
      p-converges α β β<α

    fp∼xn+1 :
      MetricSpace.Close 𝓜 (f p) α (iterate f x₀ (suc n))
    fp∼xn+1 =
      MetricSpace.close-mono
        𝓜
        (contraction-precision< ρ ρ<1 α)
        (f-contr
          {x = p}
          {y = iterate f x₀ n}
          {ε = α}
          p∼xn)

    halfβ≤halfα :
      radius (half⁺ β) ℚOrder.≤ radius (half⁺ α)
    halfβ≤halfα =
      half-mono-≤
        {ε = β}
        {δ = α}
        (Rational.<→≤ {p = radius β} {q = radius α} β<α)

    μα≤n : NatOrder._≤_ (μ (half⁺ α)) n
    μα≤n =
      scaledGeometricSegmentModulus-antitone ρ ρ<1 η halfβ≤halfα

    μα≤sucn : NatOrder._≤_ (μ (half⁺ α)) (suc n)
    μα≤sucn =
      NatOrder.≤-trans μα≤n (n≤sucn n)

    xn+1∼xn :
      MetricSpace.Close 𝓜 (iterate f x₀ (suc n)) α (iterate f x₀ n)
    xn+1∼xn =
      picardCloseToCommonUpper
        𝓜
        ρ
        ρ<1
        f-contr
        x₀
        η
        α
        x₀∼fx₀
        (suc n)
        n
        (suc n)
        (n≤n (suc n))
        (n≤sucn n)
        μα≤sucn
        μα≤n

    fp∼xn+1∼xn :
      MetricSpace.Close 𝓜 (f p) (α +⁺ α) (iterate f x₀ n)
    fp∼xn+1∼xn =
      MetricSpace.close-triangle 𝓜 fp∼xn+1 xn+1∼xn

    xn∼p :
      MetricSpace.Close 𝓜 (iterate f x₀ n) α p
    xn∼p =
      MetricSpace.close-sym 𝓜 p∼xn


banachFrom :
  (𝓜 : MetricSpace ℓ ℓ') →
  IsCauchyComplete 𝓜 →
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  (f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜) →
  IsContractionWith 𝓜 ρ f →
  (x₀ : MetricSpace.Carrier 𝓜) →
  (η : ℚ⁺) →
  MetricSpace.Close 𝓜 x₀ η (f x₀) →
  FixedPoint {𝓜 = 𝓜} f
banachFrom 𝓜 complete ρ ρ<1 f f-contr x₀ η x₀∼fx₀ =
  p , banachLimitFixed 𝓜 complete ρ ρ<1 {f = f} f-contr x₀ η x₀∼fx₀
  where
  p : MetricSpace.Carrier 𝓜
  p =
    banachLimit 𝓜 complete ρ ρ<1 {f = f} f-contr x₀ η x₀∼fx₀


banachFixedPoint :
  (𝓜 : MetricSpace ℓ ℓ') →
  IsCauchyComplete 𝓜 →
  (c : Contraction 𝓜) →
  PicardSeed 𝓜 (Contraction.map c) →
  FixedPoint {𝓜 = 𝓜} (Contraction.map c)
banachFixedPoint 𝓜 complete c seed =
  banachFrom
    𝓜
    complete
    (Contraction.ratio c)
    (Contraction.ratio<1 c)
    (Contraction.map c)
    (Contraction.contracts c)
    (PicardSeed.start seed)
    (PicardSeed.stepBound seed)
    (PicardSeed.stepClose seed)


banachProblemFixedPoint :
  (𝓜 : MetricSpace ℓ ℓ') →
  (problem : BanachProblem 𝓜) →
  FixedPoint
    {𝓜 = 𝓜}
    (Contraction.map (BanachProblem.contraction problem))
banachProblemFixedPoint 𝓜 problem =
  banachFixedPoint
    𝓜
    (BanachProblem.complete problem)
    (BanachProblem.contraction problem)
    (BanachProblem.seed problem)


fixedPointsClosePower :
  (𝓜 : MetricSpace ℓ ℓ') →
  (ρ : ℚ⁺) →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  IsContractionWith 𝓜 ρ f →
  (p q : MetricSpace.Carrier 𝓜) →
  f p ≡ p →
  f q ≡ q →
  (ζ : ℚ⁺) →
  MetricSpace.Close 𝓜 p ζ q →
  (n : ℕ) →
  MetricSpace.Close 𝓜 p (positivePower ρ n *⁺ ζ) q
fixedPointsClosePower 𝓜 ρ {f = f} f-contr p q fp≡p fq≡q ζ p∼q zero =
  subst
    (λ ε → MetricSpace.Close 𝓜 p ε q)
    (sym (*⁺-identity-left ζ))
    p∼q
fixedPointsClosePower 𝓜 ρ {f = f} f-contr p q fp≡p fq≡q ζ p∼q (suc n) =
  subst2
    (λ x y → MetricSpace.Close 𝓜 x (positivePower ρ (suc n) *⁺ ζ) y)
    fp≡p
    fq≡q
    scaled
  where
  contracted :
    MetricSpace.Close 𝓜 (f p) (ρ *⁺ (positivePower ρ n *⁺ ζ)) (f q)
  contracted =
    f-contr
      {x = p}
      {y = q}
      {ε = positivePower ρ n *⁺ ζ}
      (fixedPointsClosePower 𝓜 ρ f-contr p q fp≡p fq≡q ζ p∼q n)

  scaled :
    MetricSpace.Close 𝓜 (f p) (positivePower ρ (suc n) *⁺ ζ) (f q)
  scaled =
    subst
      (λ ε → MetricSpace.Close 𝓜 (f p) ε (f q))
      (sym (*⁺-assoc ρ (positivePower ρ n) ζ))
      contracted


banachUniqueWithBound :
  (𝓜 : MetricSpace ℓ ℓ') →
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  IsContractionWith 𝓜 ρ f →
  (p q : MetricSpace.Carrier 𝓜) →
  f p ≡ p →
  f q ≡ q →
  CloseBound 𝓜 p q →
  p ≡ q
banachUniqueWithBound 𝓜 ρ ρ<1 {f = f} f-contr p q fp≡p fq≡q (ζ , p∼q) =
  MetricSpace.close-separated 𝓜 p q close-at
  where
  μ : NatModulus
  μ =
    scaledGeometricSegmentModulus ρ ρ<1 ζ

  close-at :
    (ε : ℚ⁺) →
    MetricSpace.Close 𝓜 p ε q
  close-at ε =
    close-mono-≤
      𝓜
      (scaledGeometricSegmentUpperBound⁺ ρ ρ<1 ζ ε n zero (n≤n n))
      (fixedPointsClosePower 𝓜 ρ f-contr p q fp≡p fq≡q ζ p∼q n)
    where
    n : ℕ
    n =
      μ ε


banachUnique :
  (𝓜 : MetricSpace ℓ ℓ') →
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  HasCloseBounds 𝓜 →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  IsContractionWith 𝓜 ρ f →
  (p q : MetricSpace.Carrier 𝓜) →
  f p ≡ p →
  f q ≡ q →
  p ≡ q
banachUnique 𝓜 ρ ρ<1 close-bounds f-contr p q fp≡p fq≡q =
  banachUniqueWithBound
    𝓜
    ρ
    ρ<1
    f-contr
    p
    q
    fp≡p
    fq≡q
    (close-bounds p q)


isPropFixedPoint :
  (𝓜 : MetricSpace ℓ ℓ') →
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  HasCloseBounds 𝓜 →
  {f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓜} →
  IsContractionWith 𝓜 ρ f →
  isProp (FixedPoint {𝓜 = 𝓜} f)
isPropFixedPoint 𝓜 ρ ρ<1 close-bounds {f = f} f-contr (p , fp≡p) (q , fq≡q) =
  ΣPathP
    ( p≡q
    , isProp→PathP
        (λ i → MetricSpace.isSetCarrier 𝓜 (f (p≡q i)) (p≡q i))
        fp≡p
        fq≡q)
  where
  p≡q : p ≡ q
  p≡q =
    banachUnique
      𝓜
      ρ
      ρ<1
      close-bounds
      {f = f}
      f-contr
      p
      q
      fp≡p
      fq≡q
