{-

Eventual order data for Cauchy-real sequences

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Sequences.Order where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Sigma using (fst)
open import Cubical.Data.Sum as Sum using (inl ; inr)
open import Cubical.Relation.Nullary using (¬_)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Lattice
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Apartness
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.Sequences.Base
open import Constructive.Analysis.Reals.Sequences.Cauchy
open import Constructive.Analysis.Reals.Sequences.Convergence
open import Constructive.Data.PositiveRationals

open ClosenessOf RationalsMetricSpace


Eventually :
  ℕ →
  (ℕ → Type₀) →
  Type₀
Eventually N P =
  (n : ℕ) → NatOrder._≤_ N n → P n


EventuallyWith :
  NatModulus →
  (ℚ⁺ → ℕ → Type₀) →
  Type₀
EventuallyWith μ P =
  (ε : ℚ⁺) →
  Eventually (μ ε) (P ε)


Eventually≤ :
  ℕ →
  Sequence →
  Sequence →
  Type₀
Eventually≤ N u v =
  Eventually N (λ n → u n ≤ᶜ v n)


Eventually< :
  ℕ →
  Sequence →
  Sequence →
  Type₀
Eventually< N u v =
  Eventually N (λ n → u n <ᶜ v n)


EventuallyApart :
  ℕ →
  Sequence →
  Sequence →
  Type₀
EventuallyApart N u v =
  Eventually N (λ n → u n #ᶜ v n)


EventuallyUpperBound :
  ℕ →
  Sequence →
  ℝᶜ →
  Type₀
EventuallyUpperBound N u b =
  Eventually N (λ n → u n ≤ᶜ b)


EventuallyLowerBound :
  ℕ →
  ℝᶜ →
  Sequence →
  Type₀
EventuallyLowerBound N a u =
  Eventually N (λ n → a ≤ᶜ u n)


EventuallyEqual :
  ℕ →
  Sequence →
  Sequence →
  Type₀
EventuallyEqual N u v =
  Eventually N (λ n → u n ≡ v n)


eventually-weaken :
  {P : ℕ → Type₀} →
  {N M : ℕ} →
  NatOrder._≤_ N M →
  Eventually N P →
  Eventually M P
eventually-weaken N≤M eventuallyP n M≤n =
  eventuallyP n (NatOrder.≤-trans N≤M M≤n)


eventually≤-weaken :
  {u v : Sequence} →
  {N M : ℕ} →
  NatOrder._≤_ N M →
  Eventually≤ N u v →
  Eventually≤ M u v
eventually≤-weaken =
  eventually-weaken


eventuallyEqual-sym :
  {u v : Sequence} →
  {N : ℕ} →
  EventuallyEqual N u v →
  EventuallyEqual N v u
eventuallyEqual-sym u≡v n N≤n =
  sym (u≡v n N≤n)


eventuallyApart-sym :
  {u v : Sequence} →
  {N : ℕ} →
  EventuallyApart N u v →
  EventuallyApart N v u
eventuallyApart-sym u#v n N≤n with u#v n N≤n
... | inl u<v =
  inr u<v
... | inr v<u =
  inl v<u


eventually<→eventuallyApart :
  {u v : Sequence} →
  {N : ℕ} →
  Eventually< N u v →
  EventuallyApart N u v
eventually<→eventuallyApart u<v n N≤n =
  inl (u<v n N≤n)


eventually>→eventuallyApart :
  {u v : Sequence} →
  {N : ℕ} →
  Eventually< N v u →
  EventuallyApart N u v
eventually>→eventuallyApart v<u n N≤n =
  inr (v<u n N≤n)


eventuallyEqualPreservesConvergesWithModulus :
  {u v : Sequence} →
  {x : ℝᶜ} →
  {μ : NatModulus} →
  EventuallyWith μ (λ _ n → u n ≡ v n) →
  ConvergesWithModulus u x μ →
  ConvergesWithModulus v x μ
eventuallyEqualPreservesConvergesWithModulus {x = x} u≡v u→x ε n μ≤n =
  subst
    (λ z → z ∼[ ε ] x)
    (u≡v ε n μ≤n)
    (u→x ε n μ≤n)


eventuallyEqualPreservesConvergesTo :
  {u v : Sequence} →
  {x : ℝᶜ} →
  (u-conv : ConvergesTo u x) →
  EventuallyWith (fst u-conv) (λ _ n → u n ≡ v n) →
  ConvergesTo v x
eventuallyEqualPreservesConvergesTo (μ , u→x) u≡v =
  μ , eventuallyEqualPreservesConvergesWithModulus u≡v u→x


eventuallyEqualLimitsEqual :
  {u v : Sequence} →
  {x y : ℝᶜ} →
  (u-conv : ConvergesTo u x) →
  (v-conv : ConvergesTo v y) →
  EventuallyWith (fst u-conv) (λ _ n → u n ≡ v n) →
  x ≡ y
eventuallyEqualLimitsEqual u-conv v-conv u≡v =
  convergesToPath
    (eventuallyEqualPreservesConvergesTo u-conv u≡v)
    v-conv


eventuallyEqualLimitsNotApart :
  {u v : Sequence} →
  {x y : ℝᶜ} →
  (u-conv : ConvergesTo u x) →
  (v-conv : ConvergesTo v y) →
  EventuallyWith (fst u-conv) (λ _ n → u n ≡ v n) →
  ¬ (x #ᶜ y)
eventuallyEqualLimitsNotApart u-conv v-conv u≡v =
  ≡→¬#ᶜ (eventuallyEqualLimitsEqual u-conv v-conv u≡v)


eventuallyEqualPreservesCauchyWithModulus :
  {u v : Sequence} →
  {μ : NatModulus} →
  EventuallyWith μ (λ _ n → u n ≡ v n) →
  CauchyWithModulus u μ →
  CauchyWithModulus v μ
eventuallyEqualPreservesCauchyWithModulus u≡v u-cauchy ε m n μ≤m μ≤n =
  subst2
    (λ a b → a ∼[ ε ] b)
    (u≡v ε m μ≤m)
    (u≡v ε n μ≤n)
    (u-cauchy ε m n μ≤m μ≤n)


minSequence :
  Sequence →
  Sequence →
  Sequence
minSequence u v n =
  u n ⊓ᶜ v n


maxSequence :
  Sequence →
  Sequence →
  Sequence
maxSequence u v n =
  u n ⊔ᶜ v n


minConvergesWithModulus :
  {u v : Sequence} →
  {x y : ℝᶜ} →
  {μ ν : NatModulus} →
  ConvergesWithModulus u x μ →
  ConvergesWithModulus v y ν →
  ConvergesWithModulus
    (minSequence u v)
    (x ⊓ᶜ y)
    (λ ε → maxModulus μ ν (half⁺ ε))
minConvergesWithModulus {u = u} {v = v} {x = x} {y = y} {μ = μ} {ν = ν} u→x v→y ε n max≤n =
  subst
    (λ ρ → (u n ⊓ᶜ v n) ∼[ ρ ] (x ⊓ᶜ y))
    (half⁺+half⁺≡ ε)
    (min-close
      (u→x α n μ≤n)
      (v→y α n ν≤n))
  where
  α : ℚ⁺
  α =
    half⁺ ε

  μ≤n : NatOrder._≤_ (μ α) n
  μ≤n =
    NatOrder.≤-trans
      (maxModulus-left≤ μ ν α)
      max≤n

  ν≤n : NatOrder._≤_ (ν α) n
  ν≤n =
    NatOrder.≤-trans
      (maxModulus-right≤ μ ν α)
      max≤n


minConvergesTo :
  {u v : Sequence} →
  {x y : ℝᶜ} →
  ConvergesTo u x →
  ConvergesTo v y →
  ConvergesTo (minSequence u v) (x ⊓ᶜ y)
minConvergesTo (μ , u→x) (ν , v→y) =
  (λ ε → maxModulus μ ν (half⁺ ε)) ,
  minConvergesWithModulus u→x v→y


maxConvergesWithModulus :
  {u v : Sequence} →
  {x y : ℝᶜ} →
  {μ ν : NatModulus} →
  ConvergesWithModulus u x μ →
  ConvergesWithModulus v y ν →
  ConvergesWithModulus
    (maxSequence u v)
    (x ⊔ᶜ y)
    (λ ε → maxModulus μ ν (half⁺ ε))
maxConvergesWithModulus {u = u} {v = v} {x = x} {y = y} {μ = μ} {ν = ν} u→x v→y ε n max≤n =
  subst
    (λ ρ → (u n ⊔ᶜ v n) ∼[ ρ ] (x ⊔ᶜ y))
    (half⁺+half⁺≡ ε)
    (max-close
      (u→x α n μ≤n)
      (v→y α n ν≤n))
  where
  α : ℚ⁺
  α =
    half⁺ ε

  μ≤n : NatOrder._≤_ (μ α) n
  μ≤n =
    NatOrder.≤-trans
      (maxModulus-left≤ μ ν α)
      max≤n

  ν≤n : NatOrder._≤_ (ν α) n
  ν≤n =
    NatOrder.≤-trans
      (maxModulus-right≤ μ ν α)
      max≤n


maxConvergesTo :
  {u v : Sequence} →
  {x y : ℝᶜ} →
  ConvergesTo u x →
  ConvergesTo v y →
  ConvergesTo (maxSequence u v) (x ⊔ᶜ y)
maxConvergesTo (μ , u→x) (ν , v→y) =
  (λ ε → maxModulus μ ν (half⁺ ε)) ,
  maxConvergesWithModulus u→x v→y


eventually≤ClosedWithModuli :
  {u v : Sequence} →
  {x y : ℝᶜ} →
  {μ ν : NatModulus} →
  ConvergesWithModulus u x μ →
  ConvergesWithModulus v y ν →
  EventuallyWith
    (λ ε → maxModulus μ ν (half⁺ ε))
    (λ _ n → u n ≤ᶜ v n) →
  x ≤ᶜ y
eventually≤ClosedWithModuli {u = u} {v = v} {x = x} {y = y} {μ = μ} {ν = ν} u→x v→y u≤v =
  convergesToPath
    (ρ , u→x⊓y)
    (μ , u→x)
  where
  ρ : NatModulus
  ρ ε =
    maxModulus μ ν (half⁺ ε)

  min→x⊓y :
    ConvergesWithModulus (minSequence u v) (x ⊓ᶜ y) ρ
  min→x⊓y =
    minConvergesWithModulus u→x v→y

  u→x⊓y :
    ConvergesWithModulus u (x ⊓ᶜ y) ρ
  u→x⊓y =
    eventuallyEqualPreservesConvergesWithModulus
      {u = minSequence u v}
      {v = u}
      u≤v
      min→x⊓y


eventually≤Closed :
  {u v : Sequence} →
  {x y : ℝᶜ} →
  (u-conv : ConvergesTo u x) →
  (v-conv : ConvergesTo v y) →
  EventuallyWith
    (λ ε → maxModulus (fst u-conv) (fst v-conv) (half⁺ ε))
    (λ _ n → u n ≤ᶜ v n) →
  x ≤ᶜ y
eventually≤Closed (μ , u→x) (ν , v→y) =
  eventually≤ClosedWithModuli u→x v→y


eventuallyUpperBoundClosed :
  {u : Sequence} →
  {x b : ℝᶜ} →
  (u-conv : ConvergesTo u x) →
  EventuallyWith
    (λ ε → maxModulus (fst u-conv) (λ _ → zero) (half⁺ ε))
    (λ _ n → u n ≤ᶜ b) →
  x ≤ᶜ b
eventuallyUpperBoundClosed {b = b} u-conv =
  eventually≤Closed u-conv (constantConvergesTo b)


eventuallyLowerBoundClosed :
  {u : Sequence} →
  {a x : ℝᶜ} →
  (u-conv : ConvergesTo u x) →
  EventuallyWith
    (λ ε → maxModulus (λ _ → zero) (fst u-conv) (half⁺ ε))
    (λ _ n → a ≤ᶜ u n) →
  a ≤ᶜ x
eventuallyLowerBoundClosed {a = a} u-conv =
  eventually≤Closed (constantConvergesTo a) u-conv


squeezeLimitPathWithModuli :
  {u v w : Sequence} →
  {x y : ℝᶜ} →
  {μ ν ω : NatModulus} →
  ConvergesWithModulus u x μ →
  ConvergesWithModulus v y ν →
  ConvergesWithModulus w x ω →
  EventuallyWith
    (λ ε → maxModulus μ ν (half⁺ ε))
    (λ _ n → u n ≤ᶜ v n) →
  EventuallyWith
    (λ ε → maxModulus ν ω (half⁺ ε))
    (λ _ n → v n ≤ᶜ w n) →
  y ≡ x
squeezeLimitPathWithModuli u→x v→y w→x u≤v v≤w =
  ≤ᶜ-antisym
    (eventually≤ClosedWithModuli v→y w→x v≤w)
    (eventually≤ClosedWithModuli u→x v→y u≤v)


squeezeLimitPath :
  {u v w : Sequence} →
  {x y : ℝᶜ} →
  (u-conv : ConvergesTo u x) →
  (v-conv : ConvergesTo v y) →
  (w-conv : ConvergesTo w x) →
  EventuallyWith
    (λ ε → maxModulus (fst u-conv) (fst v-conv) (half⁺ ε))
    (λ _ n → u n ≤ᶜ v n) →
  EventuallyWith
    (λ ε → maxModulus (fst v-conv) (fst w-conv) (half⁺ ε))
    (λ _ n → v n ≤ᶜ w n) →
  y ≡ x
squeezeLimitPath (μ , u→x) (ν , v→y) (ω , w→x) =
  squeezeLimitPathWithModuli u→x v→y w→x
