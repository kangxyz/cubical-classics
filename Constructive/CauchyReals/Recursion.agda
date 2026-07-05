{-

Enhanced recursion for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Recursion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Rationals using (ℚ)

open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Definitions

private
  variable
    ℓ ℓ' : Level


record RecursionKit (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality

  field
    A : Type ℓ
    B : TargetCloseness A ℓ'

    isPropB : (ε : ℚ⁺) (a b : A) → isProp (B ε a b)
    separated : (a b : A) → ((ε : ℚ⁺) → B ε a b) → a ≡ b

    rational* : ℚ → A
    limit* :
      (x : CauchyApproximation) →
      (f : ℚ⁺ → A) →
      IsTargetCauchyApproximation B f →
      A

    rational-rational* :
      (q r : ℚ) (ε : ℚ⁺) →
      Closeℚ q ε r →
      B ε (rational* q) (rational* r)

    rational-limit* :
      (q : ℚ) (ε δ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      (y : CauchyApproximation) →
      (g : ℚ⁺ → A) →
      (gCauchy : IsTargetCauchyApproximation B g) →
      B (ε ⊖ δ [ δ<ε ]) (rational* q) (g δ) →
      B ε (rational* q) (limit* y g gCauchy)

    limit-rational* :
      (x : CauchyApproximation) →
      (f : ℚ⁺ → A) →
      (fCauchy : IsTargetCauchyApproximation B f) →
      (r : ℚ) (ε δ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      B (ε ⊖ δ [ δ<ε ]) (f δ) (rational* r) →
      B ε (limit* x f fCauchy) (rational* r)

    limit-limit* :
      (x y : CauchyApproximation) →
      (f g : ℚ⁺ → A) →
      (fCauchy : IsTargetCauchyApproximation B f) →
      (gCauchy : IsTargetCauchyApproximation B g) →
      (ε δ η : ℚ⁺) →
      (δ+η<ε : δ +⁺ η <⁺ ε) →
      B (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) (f δ) (g η) →
      B ε (limit* x f fCauchy) (limit* y g gCauchy)


module Recursion (kit : RecursionKit ℓ ℓ') where
  open RecursionKit kit

  mutual
    rec : ℝᴴ → A
    rec (rational q) = rational* q
    rec (limit x) =
      limit* x
        (λ ε → rec (approximate x ε))
        (λ ε δ → rec-close (isRegular x ε δ))
    rec (path x y x∼y i) =
      separated (rec x) (rec y) (λ ε → rec-close (x∼y ε)) i

    rec-close : {x y : ℝᴴ} {ε : ℚ⁺} → x ∼[ ε ] y → B ε (rec x) (rec y)
    rec-close (rational-rational-close q r ε q∼r) =
      rational-rational* q r ε q∼r
    rec-close (rational-limit-close q ε δ δ<ε y q∼yδ) =
      rational-limit* q ε δ δ<ε y
        (λ η → rec (approximate y η))
        (λ η θ → rec-close (isRegular y η θ))
        (rec-close q∼yδ)
    rec-close (limit-rational-close x r ε δ δ<ε xδ∼r) =
      limit-rational* x
        (λ η → rec (approximate x η))
        (λ η θ → rec-close (isRegular x η θ))
        r ε δ δ<ε
        (rec-close xδ∼r)
    rec-close (limit-limit-close x y ε δ η δ+η<ε xδ∼yη) =
      limit-limit* x y
        (λ θ → rec (approximate x θ))
        (λ θ → rec (approximate y θ))
        (λ θ κ → rec-close (isRegular x θ κ))
        (λ θ κ → rec-close (isRegular y θ κ))
        ε δ η δ+η<ε
        (rec-close xδ∼yη)
    rec-close (squash p q i) =
      isPropB _ _ _ (rec-close p) (rec-close q) i
