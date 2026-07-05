{-

Order and approximation lemmas for constructive Dedekind reals

The rational-cut API is the ℚ instance of the generic Dedekind completion.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals using (ℚ)
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

import Constructive.DedekindCompletion.Base as CompletionBase
import Constructive.DedekindCompletion.Order as CompletionOrder
import Constructive.DedekindCompletion.Arithmetic.Base as CompletionArithmetic
open import Constructive.DedekindCompletion.Instances.Rationals
open import Constructive.DedekindReals.Base public
import Constructive.Rationals as ℚExtra

private
  variable
    ℓ : Level

  ℚField = ℚArchimedeanLinearlyOrderedField .fst

private
  module RationalBase = CompletionBase.CompletionBase ℚField
  module GenericOrder = CompletionOrder.CompletionOrder ℚField
  module GenericArithmetic =
    CompletionArithmetic.ArithmeticBase ℚArchimedeanLinearlyOrderedField


ℚ→𝔻 : (ℓ : Level) → ℚ → DedekindReal ℓ
ℚ→𝔻 = RationalBase.K→𝔻


module Order {ℓ : Level} where
  private
    module RawOrder = CompletionOrder.CompletionOrder ℚField

  _≤_ = RawOrder._≤_ {ℓᴾ = ℓ}
  _<_ = RawOrder._<_ {ℓᴾ = ℓ}
  _#_ = RawOrder._#_ {ℓᴾ = ℓ}

  infix 4 _≤_ _<_ _#_

  isProp≤ = RawOrder.isProp≤ {ℓᴾ = ℓ}
  isProp< = RawOrder.isProp< {ℓᴾ = ℓ}
  ≡→≤ = RawOrder.≡→≤ {ℓᴾ = ℓ}
  ≤-refl = RawOrder.≤-refl {ℓᴾ = ℓ}
  ≤-trans = RawOrder.≤-trans {ℓᴾ = ℓ}
  lower<upper = RawOrder.lower<upper {ℓᴾ = ℓ}
  lower-closed-≤ = RawOrder.lower-closed-≤ {ℓᴾ = ℓ}
  upper-closed-≤ = RawOrder.upper-closed-≤ {ℓᴾ = ℓ}
  lower→ℚ< = RawOrder.lower→K< {ℓᴾ = ℓ}
  ℚ<→lower = RawOrder.K<→lower {ℓᴾ = ℓ}
  upper→<ℚ = RawOrder.upper→<K {ℓᴾ = ℓ}
  <ℚ→upper = RawOrder.<K→upper {ℓᴾ = ℓ}
  lower⇔ℚ< = RawOrder.lower⇔K< {ℓᴾ = ℓ}
  upper⇔<ℚ = RawOrder.upper⇔<K {ℓᴾ = ℓ}
  rational-between = RawOrder.basis-between {ℓᴾ = ℓ}
  rational-located = RawOrder.basis-located {ℓᴾ = ℓ}
  ℚ→<-pres = RawOrder.K→<-pres {ℓᴾ = ℓ}
  ℚ→<-reflect = RawOrder.K→<-reflect {ℓᴾ = ℓ}
  upper-inclusion-from-lower = RawOrder.upper-inclusion-from-lower {ℓᴾ = ℓ}
  ≤-antisym = RawOrder.≤-antisym {ℓᴾ = ℓ}
  <→≤ = RawOrder.<→≤ {ℓᴾ = ℓ}
  <-trans = RawOrder.<-trans {ℓᴾ = ℓ}
  ≤-<-trans = RawOrder.≤-<-trans {ℓᴾ = ℓ}
  <-≤-trans = RawOrder.<-≤-trans {ℓᴾ = ℓ}
  <≤-asym = RawOrder.<≤-asym {ℓᴾ = ℓ}
  <-irrefl = RawOrder.<-irrefl {ℓᴾ = ℓ}
  <-asym = RawOrder.<-asym {ℓᴾ = ℓ}
  isWeaklyLinear< = RawOrder.isWeaklyLinear< {ℓᴾ = ℓ}
  ≤→¬> = RawOrder.≤→¬> {ℓᴾ = ℓ}
  ¬>→≤ = RawOrder.¬>→≤ {ℓᴾ = ℓ}
  ≤⇔¬> = RawOrder.≤⇔¬> {ℓᴾ = ℓ}
  isStrictOrder< = RawOrder.isStrictOrder< {ℓᴾ = ℓ}
  isProp# = RawOrder.isProp# {ℓᴾ = ℓ}
  #-irrefl = RawOrder.#-irrefl {ℓᴾ = ℓ}
  #-sym = RawOrder.#-sym {ℓᴾ = ℓ}
  #-cotrans = RawOrder.#-cotrans {ℓᴾ = ℓ}
  #-tight = RawOrder.#-tight {ℓᴾ = ℓ}
  <→≠ = RawOrder.<→≠ {ℓᴾ = ℓ}
  #→≠ = RawOrder.#→≠ {ℓᴾ = ℓ}
  _⊓_ = RawOrder._⊓_ {ℓᴾ = ℓ}
  _⊔_ = RawOrder._⊔_ {ℓᴾ = ℓ}
  ⊓≤left = RawOrder.⊓≤left {ℓᴾ = ℓ}
  ⊓≤right = RawOrder.⊓≤right {ℓᴾ = ℓ}
  ≤⊓ = RawOrder.≤⊓ {ℓᴾ = ℓ}
  left≤⊔ = RawOrder.left≤⊔ {ℓᴾ = ℓ}
  right≤⊔ = RawOrder.right≤⊔ {ℓᴾ = ℓ}
  ⊔≤ = RawOrder.⊔≤ {ℓᴾ = ℓ}
  Dedekind≤Poset = RawOrder.DedekindCompletion≤Poset {ℓᴾ = ℓ}
  Dedekind≤Pseudolattice = RawOrder.DedekindCompletion≤Pseudolattice {ℓᴾ = ℓ}

  module DedekindPseudolatticeTheory =
    RawOrder.DedekindCompletionPseudolatticeTheory {ℓᴾ = ℓ}

  ⊓-comm = RawOrder.⊓-comm {ℓᴾ = ℓ}
  ⊓-idem = RawOrder.⊓-idem {ℓᴾ = ℓ}
  ⊓-assoc = RawOrder.⊓-assoc {ℓᴾ = ℓ}
  ⊔-comm = RawOrder.⊔-comm {ℓᴾ = ℓ}
  ⊔-idem = RawOrder.⊔-idem {ℓᴾ = ℓ}
  ⊔-assoc = RawOrder.⊔-assoc {ℓᴾ = ℓ}
  ⊓-absorb-⊔ = RawOrder.⊓-absorb-⊔ {ℓᴾ = ℓ}
  ⊔-absorb-⊓ = RawOrder.⊔-absorb-⊓ {ℓᴾ = ℓ}


module RationalEmbedding {ℓ : Level} where
  open Order {ℓ}

  ℚ→<-iff :
    (p q : ℚ) →
    (p ℚOrder.< q → ℚ→𝔻 ℓ p < ℚ→𝔻 ℓ q)
    ×
    (ℚ→𝔻 ℓ p < ℚ→𝔻 ℓ q → p ℚOrder.< q)
  ℚ→<-iff p q = ℚ→<-pres p q , ℚ→<-reflect p q

  ℚ→≤-pres :
    (p q : ℚ) → p ℚOrder.≤ q →
    ℚ→𝔻 ℓ p ≤ ℚ→𝔻 ℓ q
  ℚ→≤-pres p q p≤q r r<p =
    lift (ℚOrder.isTrans<≤ r p q (Lift.lower r<p) p≤q)

  ℚ→≤-reflect :
    (p q : ℚ) →
    ℚ→𝔻 ℓ p ≤ ℚ→𝔻 ℓ q →
    p ℚOrder.≤ q
  ℚ→≤-reflect p q p≤q =
    ℚOrder.≮→≥ q p λ q<p →
      Prop.rec Empty.isProp⊥
        (λ (r , q<r , r<p) →
          ℚOrder.isAsym< q r q<r (Lift.lower (p≤q r (lift r<p))))
        (ℚExtra.dense {p = q} {q = p} q<p)

  ℚ→≤-iff :
    (p q : ℚ) →
    (p ℚOrder.≤ q → ℚ→𝔻 ℓ p ≤ ℚ→𝔻 ℓ q)
    ×
    (ℚ→𝔻 ℓ p ≤ ℚ→𝔻 ℓ q → p ℚOrder.≤ q)
  ℚ→≤-iff p q = ℚ→≤-pres p q , ℚ→≤-reflect p q

  ℚ→-injective :
    (p q : ℚ) →
    ℚ→𝔻 ℓ p ≡ ℚ→𝔻 ℓ q →
    p ≡ q
  ℚ→-injective p q p*≡q* =
    ℚOrder.isAntisym≤ p q
      (ℚ→≤-reflect p q (≡→≤ p*≡q*))
      (ℚ→≤-reflect q p (≡→≤ (sym p*≡q*)))

  0𝔻<1𝔻 : ℚ→𝔻 ℓ ℚExtra.0ℚ < ℚ→𝔻 ℓ ℚExtra.1ℚ
  0𝔻<1𝔻 = ℚ→<-pres ℚExtra.0ℚ ℚExtra.1ℚ ℚExtra.0<1


module Archimedean {ℓ : Level} where
  open Order {ℓ}

  upper-rational-bound :
    (x : DedekindReal ℓ) →
    ∥ Σ[ n ∈ ℕ ] x < ℚ→𝔻 ℓ (ℚExtra.natMul n ℚExtra.1ℚ) ∥₁
  upper-rational-bound x =
    Prop.rec squash₁
      (λ (q , q∈Ux) →
        let (n , q<n) = ℚExtra.archimedes q ℚExtra.1ℚ ℚExtra.0<1 in
        ∣ n , ∣ q , q∈Ux , lift q<n ∣₁ ∣₁)
      (upper-inhabited x)

  lower-rational-bound :
    (x : DedekindReal ℓ) →
    ∥ Σ[ n ∈ ℕ ] ℚ→𝔻 ℓ (ℚ.- ℚExtra.natMul n ℚExtra.1ℚ) < x ∥₁
  lower-rational-bound x =
    Prop.rec squash₁
      (λ (q , q∈Lx) →
        let
          n , -q<n = ℚExtra.archimedes (ℚ.- q) ℚExtra.1ℚ ℚExtra.0<1
          -n<q =
            subst (λ r → (ℚ.- ℚExtra.natMul n ℚExtra.1ℚ) ℚOrder.< r)
              (ℚ.-Invol q)
              (ℚExtra.negReverse<
                {p = ℚ.- q}
                {q = ℚExtra.natMul n ℚExtra.1ℚ}
                -q<n)
        in
        ∣ n , ∣ q , lift -n<q , q∈Lx ∣₁ ∣₁)
      (lower-inhabited x)


module Approximation {ℓ : Level} where
  open GenericArithmetic.Approximation {ℓ} public
