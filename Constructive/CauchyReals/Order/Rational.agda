{-# OPTIONS --safe #-}

module Constructive.CauchyReals.Order.Rational where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Relation.Nullary

open import Constructive.CauchyReals.Arithmetic.Base
open import Constructive.CauchyReals.Arithmetic.Lattice
open import Constructive.CauchyReals.Base
open import Constructive.Analysis.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace
open import Constructive.CauchyReals.Order.Base
open import Constructive.Data.PositiveRationals
open import Constructive.Data.Rationals.Closeness
import Constructive.Data.Rationals as Rational


private
  rational-close-from-path :
    (q r : ℚ) (ε : ℚ⁺) →
    rational q ≡ rational r →
    Closeℚ q ε r
  rational-close-from-path q r ε q≡r =
    close→computed
      (subst (λ y → rational q ∼[ ε ] y)
        q≡r
        (close-refl (rational q) ε))

  min-right-path :
    (q r : ℚ) →
    r ℚOrder.≤ q →
    ℚ.min q r ≡ r
  min-right-path q r r≤q =
    ℚ.minComm q r ∙
    ℚOrder.≤→min r q r≤q

  min-left→≤ :
    (q r : ℚ) →
    ℚ.min q r ≡ q →
    q ℚOrder.≤ r
  min-left→≤ q r min≡q with q ℚOrder.≟ r
  ... | ℚOrder.lt q<r =
    ℚOrder.<Weaken≤ q r q<r
  ... | ℚOrder.eq q≡r =
    ℚOrder.≡Weaken≤ q r q≡r
  ... | ℚOrder.gt r<q =
    Empty.rec
      (ℚOrder.isIrrefl< r
        (subst
          (r ℚOrder.<_)
          (sym r≡q)
          r<q))
    where
    r≡q : r ≡ q
    r≡q =
      sym (min-right-path q r (ℚOrder.<Weaken≤ r q r<q)) ∙
      min≡q


rational-injective :
  (q r : ℚ) →
  rational q ≡ rational r →
  q ≡ r
rational-injective q r q≡r with q ℚOrder.≟ r
... | ℚOrder.lt q<r =
  Empty.rec
    (ℚOrder.isAsym<
      (r ℚ.- q)
      (radius (half⁺ gap))
      (close .snd)
      (half< gap))
  where
  gap : ℚ⁺
  gap = r ℚ.- q , Rational.diff-positive {p = q} {q = r} q<r

  close : Closeℚ q (half⁺ gap) r
  close = rational-close-from-path q r (half⁺ gap) q≡r
... | ℚOrder.eq q≡r =
  q≡r
... | ℚOrder.gt r<q =
  Empty.rec
    (ℚOrder.isAsym<
      (q ℚ.- r)
      (radius (half⁺ gap))
      (close .fst)
      (half< gap))
  where
  gap : ℚ⁺
  gap = q ℚ.- r , Rational.diff-positive {p = r} {q = q} r<q

  close : Closeℚ q (half⁺ gap) r
  close = rational-close-from-path q r (half⁺ gap) q≡r


≤ℚ→rational≤ᶜ :
  {q r : ℚ} →
  q ℚOrder.≤ r →
  rational q ≤ᶜ rational r
≤ℚ→rational≤ᶜ {q = q} {r = r} q≤r =
  cong rational (ℚOrder.≤→min q r q≤r)


rational≤ᶜ→≤ℚ :
  {q r : ℚ} →
  rational q ≤ᶜ rational r →
  q ℚOrder.≤ r
rational≤ᶜ→≤ℚ {q = q} {r = r} q≤ᶜr =
  min-left→≤ q r
    (rational-injective (ℚ.min q r) q q≤ᶜr)


positive-rational-not≤0ᶜ :
  (ε : ℚ⁺) →
  ¬ (rational (radius ε) ≤ᶜ 0ᶜ)
positive-rational-not≤0ᶜ ε ε≤0 =
  ℚOrder.≤→≯ (radius ε) 0ℚ
    (rational≤ᶜ→≤ℚ ε≤0)
    (ε .snd)
