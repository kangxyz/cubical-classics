{-

Negation on HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Arithmetic.Negation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness.Properties
open import Constructive.CauchyReals.Continuity
open import Constructive.CauchyReals.Induction
open import Constructive.CauchyReals.Lipschitz.Base
open import Constructive.CauchyReals.Recursion


private
  negationKit : RecursionKit ℓ-zero ℓ-zero
  negationKit .RecursionKit.A = ℝᴴ
  negationKit .RecursionKit.B ε x y = x ∼[ ε ] y
  negationKit .RecursionKit.isPropB ε x y = squash
  negationKit .RecursionKit.separated x y = path x y
  negationKit .RecursionKit.rational* q = rational (ℚ.- q)
  negationKit .RecursionKit.limit* x f fCauchy =
    limit (cauchy-approximation f fCauchy)
  negationKit .RecursionKit.rational-rational* q r ε q∼r =
    rational-rational-close (ℚ.- q) (ℚ.- r) ε
      (rational-close-neg q r ε q∼r)
  negationKit .RecursionKit.rational-limit* q ε δ δ<ε y g gCauchy q∼gδ =
    rational-limit-close (ℚ.- q) ε δ δ<ε
      (cauchy-approximation g gCauchy)
      q∼gδ
  negationKit .RecursionKit.limit-rational* x f fCauchy r ε δ δ<ε fδ∼r =
    limit-rational-close
      (cauchy-approximation f fCauchy)
      (ℚ.- r) ε δ δ<ε
      fδ∼r
  negationKit .RecursionKit.limit-limit* x y f g fCauchy gCauchy ε δ η δ+η<ε fδ∼gη =
    limit-limit-close
      (cauchy-approximation f fCauchy)
      (cauchy-approximation g gCauchy)
      ε δ η δ+η<ε
      fδ∼gη

  module NegationRecursion = Recursion negationKit


-ᴴ_ : ℝᴴ → ℝᴴ
-ᴴ_ = NegationRecursion.rec


neg-rational : (q : ℚ) → -ᴴ rational q ≡ rational (ℚ.- q)
neg-rational q = refl


neg-close : {x y : ℝᴴ} {ε : ℚ⁺} → x ∼[ ε ] y → (-ᴴ x) ∼[ ε ] (-ᴴ y)
neg-close = NegationRecursion.rec-close


neg-nonexpanding : IsNonexpanding -ᴴ_
neg-nonexpanding = neg-close


neg-lipschitz : IsLipschitz -ᴴ_
neg-lipschitz =
  (λ ε → ε) , λ ε → neg-close


neg-continuous : IsContinuous -ᴴ_
neg-continuous =
  lipschitz→continuous neg-lipschitz


private
  negInvolutiveKit : PropInductionKit ℓ-zero
  negInvolutiveKit .PropInductionKit.A x = -ᴴ (-ᴴ x) ≡ x
  negInvolutiveKit .PropInductionKit.isPropA x =
    isSetℝᴴ (-ᴴ (-ᴴ x)) x
  negInvolutiveKit .PropInductionKit.rational* q =
    cong rational (ℚ.-Invol q)
  negInvolutiveKit .PropInductionKit.limit* x negneg≡id =
    path (limit (cauchy-approximation f fCauchy)) (limit x) closeAt
    where
    f : ℚ⁺ → ℝᴴ
    f ε = -ᴴ (-ᴴ approximate x ε)

    fCauchy : (ε δ : ℚ⁺) → f ε ∼[ ε +⁺ δ ] f δ
    fCauchy ε δ =
      neg-close (neg-close (isRegular x ε δ))

    closeAt :
      (ε : ℚ⁺) →
      limit (cauchy-approximation f fCauchy) ∼[ ε ] limit x
    closeAt ε =
      limit-limit-close
        (cauchy-approximation f fCauchy)
        x
        ε δ δ δ+δ<ε
        (subst
          (λ z → z ∼[ ε ⊖ (δ +⁺ δ) [ δ+δ<ε ] ] approximate x δ)
          (sym (negneg≡id δ))
          (close-refl (approximate x δ)
            (ε ⊖ (δ +⁺ δ) [ δ+δ<ε ])))
      where
      δ : ℚ⁺
      δ = quarter⁺ ε

      δ+δ<ε : δ +⁺ δ <⁺ ε
      δ+δ<ε = quarter-sum< ε

  module NegInvolutiveInduction = PropInduction negInvolutiveKit


neg-involutive : (x : ℝᴴ) → -ᴴ (-ᴴ x) ≡ x
neg-involutive =
  NegInvolutiveInduction.ind
