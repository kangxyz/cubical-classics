{-

Induction interfaces for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Induction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit using (Unit* ; tt* ; isPropUnit*)
open import Cubical.Data.Rationals using (ℚ)

open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Definitions public

private
  variable
    ℓ ℓ' : Level


record InductionKit (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality

  field
    A : ℝᶜ → Type ℓ
    B : DependentCloseness A ℓ'

    rational* : (q : ℚ) → A (rational q)
    limit* :
      (x : CauchyApproximation) →
      (a : (ε : ℚ⁺) → A (approximate x ε)) →
      IsDependentCauchyApproximation B x a →
      A (limit x)

    path* :
      (x y : ℝᶜ) →
      (x∼y : (ε : ℚ⁺) → x ∼[ ε ] y) →
      (a : A x) →
      (b : A y) →
      ((ε : ℚ⁺) → B ε (x∼y ε) a b) →
      PathP (λ i → A (path x y x∼y i)) a b

    rational-rational* :
      (q r : ℚ) (ε : ℚ⁺) →
      (q∼r : Closeℚ q ε r) →
      B ε (rational-rational-close q r ε q∼r) (rational* q) (rational* r)

    rational-limit* :
      (q : ℚ) (ε δ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      (y : CauchyApproximation) →
      (b : (η : ℚ⁺) → A (approximate y η)) →
      (bCauchy : IsDependentCauchyApproximation B y b) →
      (q∼yδ : rational q ∼[ ε ⊖ δ [ δ<ε ] ] approximate y δ) →
      B (ε ⊖ δ [ δ<ε ]) q∼yδ (rational* q) (b δ) →
      B ε
        (rational-limit-close q ε δ δ<ε y q∼yδ)
        (rational* q)
        (limit* y b bCauchy)

    limit-rational* :
      (x : CauchyApproximation) →
      (a : (η : ℚ⁺) → A (approximate x η)) →
      (aCauchy : IsDependentCauchyApproximation B x a) →
      (r : ℚ) (ε δ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      (xδ∼r : approximate x δ ∼[ ε ⊖ δ [ δ<ε ] ] rational r) →
      B (ε ⊖ δ [ δ<ε ]) xδ∼r (a δ) (rational* r) →
      B ε
        (limit-rational-close x r ε δ δ<ε xδ∼r)
        (limit* x a aCauchy)
        (rational* r)

    limit-limit* :
      (x y : CauchyApproximation) →
      (a : (θ : ℚ⁺) → A (approximate x θ)) →
      (b : (θ : ℚ⁺) → A (approximate y θ)) →
      (aCauchy : IsDependentCauchyApproximation B x a) →
      (bCauchy : IsDependentCauchyApproximation B y b) →
      (ε δ η : ℚ⁺) →
      (δ+η<ε : δ +⁺ η <⁺ ε) →
      (xδ∼yη :
        approximate x δ
          ∼[ ε ⊖ (δ +⁺ η) [ δ+η<ε ] ]
          approximate y η) →
      B (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) xδ∼yη (a δ) (b η) →
      B ε
        (limit-limit-close x y ε δ η δ+η<ε xδ∼yη)
        (limit* x a aCauchy)
        (limit* y b bCauchy)

    squash* :
      {x y : ℝᶜ} {ε : ℚ⁺} →
      (p : x ∼[ ε ] y) →
      (a : A x) →
      (b : A y) →
      isProp (B ε p a b)


module Induction (kit : InductionKit ℓ ℓ') where
  open InductionKit kit

  mutual
    ind : (x : ℝᶜ) → A x
    ind (rational q) = rational* q
    ind (limit x) =
      limit* x
        (λ ε → ind (approximate x ε))
        (λ ε δ → ind-close (isRegular x ε δ))
    ind (path x y x∼y i) =
      path* x y x∼y (ind x) (ind y) (λ ε → ind-close (x∼y ε)) i

    ind-close :
      {x y : ℝᶜ} {ε : ℚ⁺} →
      (x∼y : x ∼[ ε ] y) →
      B ε x∼y (ind x) (ind y)
    ind-close (rational-rational-close q r ε q∼r) =
      rational-rational* q r ε q∼r
    ind-close (rational-limit-close q ε δ δ<ε y q∼yδ) =
      rational-limit* q ε δ δ<ε y
        (λ η → ind (approximate y η))
        (λ η θ → ind-close (isRegular y η θ))
        q∼yδ
        (ind-close q∼yδ)
    ind-close (limit-rational-close x r ε δ δ<ε xδ∼r) =
      limit-rational* x
        (λ η → ind (approximate x η))
        (λ η θ → ind-close (isRegular x η θ))
        r ε δ δ<ε
        xδ∼r
        (ind-close xδ∼r)
    ind-close (limit-limit-close x y ε δ η δ+η<ε xδ∼yη) =
      limit-limit* x y
        (λ θ → ind (approximate x θ))
        (λ θ → ind (approximate y θ))
        (λ θ κ → ind-close (isRegular x θ κ))
        (λ θ κ → ind-close (isRegular y θ κ))
        ε δ η δ+η<ε
        xδ∼yη
        (ind-close xδ∼yη)
    ind-close (squash p q i) =
      isProp→PathP
        (λ i → squash* (squash p q i) _ _)
        (ind-close p)
        (ind-close q)
        i


record PropInductionKit (ℓ : Level) : Type (ℓ-suc ℓ) where
  no-eta-equality

  field
    A : ℝᶜ → Type ℓ
    isPropA : (x : ℝᶜ) → isProp (A x)

    rational* : (q : ℚ) → A (rational q)
    limit* :
      (x : CauchyApproximation) →
      ((ε : ℚ⁺) → A (approximate x ε)) →
      A (limit x)


module PropInduction (kit : PropInductionKit ℓ) where
  open PropInductionKit kit

  private
    propKit : InductionKit ℓ ℓ-zero
    propKit .InductionKit.A = A
    propKit .InductionKit.B ε x∼y a b = Unit*
    propKit .InductionKit.rational* = rational*
    propKit .InductionKit.limit* x a aCauchy = limit* x a
    propKit .InductionKit.path* x y x∼y a b close* =
      isProp→PathP
        (λ i → isPropA (path x y x∼y i))
        a
        b
    propKit .InductionKit.rational-rational* q r ε q∼r = tt*
    propKit .InductionKit.rational-limit* q ε δ δ<ε y b bCauchy q∼yδ q∼bδ = tt*
    propKit .InductionKit.limit-rational* x a aCauchy r ε δ δ<ε xδ∼r aδ∼r = tt*
    propKit .InductionKit.limit-limit* x y a b aCauchy bCauchy ε δ η δ+η<ε xδ∼yη aδ∼bη = tt*
    propKit .InductionKit.squash* p a b = isPropUnit*

    module Ind = Induction propKit

  ind : (x : ℝᶜ) → A x
  ind = Ind.ind
