{-

Finite-support power series

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (neg-zeroᶜ)
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using
    ( AnalyticAt
    ; HasPowerSeriesAt
    ; HasPowerSeriesAtOnBall
    ; HasPowerSeriesAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; inverseSucReal
    ; naturalReal
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct
  using (cauchyProductPowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( bounded-byᶜ-zero
    ; addPowerSeries
    ; constantPowerSeries
    ; negPowerSeries
    ; powerSeriesPartialSum-shift
    ; rationalScalePowerSeries
    ; shiftPowerSeries
    ; subPowerSeries
    ; tailSum-zero-sequence
    ; zeroPowerSeries
    )
open import Constructive.Data.PositiveRationals


PowerSeriesZeroAfter :
  PowerSeries →
  ℕ →
  Type₀
PowerSeriesZeroAfter a N =
  (n : ℕ) →
  NatOrder._≤_ N n →
  a n ≡ 0ᶜ


IsPolynomialPowerSeries :
  PowerSeries →
  Type₀
IsPolynomialPowerSeries a =
  Σ[ N ∈ ℕ ] PowerSeriesZeroAfter a N


powerSeriesZeroAfter-weaken :
  {a : PowerSeries} →
  {N M : ℕ} →
  NatOrder._≤_ N M →
  PowerSeriesZeroAfter a N →
  PowerSeriesZeroAfter a M
powerSeriesZeroAfter-weaken N≤M zeroAfter n M≤n =
  zeroAfter n (NatOrder.≤-trans N≤M M≤n)


powerSeriesTerm-zeroAfter :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  (h : ℝᶜ) →
  (n : ℕ) →
  NatOrder._≤_ N n →
  powerSeriesTerm a h n ≡ 0ᶜ
powerSeriesTerm-zeroAfter {a = a} N zeroAfter h n N≤n =
  cong
    (λ c → c ·ᶜ realPower h n)
    (zeroAfter n N≤n) ∙
  mulᶜ-zero-left (realPower h n)


drop-powerSeriesTerm-zeroAfter :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  (h : ℝᶜ) →
  (m n : ℕ) →
  NatOrder._≤_ N m →
  drop m (powerSeriesTerm a h) n ≡ 0ᶜ
drop-powerSeriesTerm-zeroAfter {a = a} N zeroAfter h m n N≤m =
  drop-index m (powerSeriesTerm a h) n ∙
  powerSeriesTerm-zeroAfter N zeroAfter h (m Nat.+ n) N≤m+n
  where
  N≤m+n : NatOrder._≤_ N (m Nat.+ n)
  N≤m+n =
    NatOrder.≤-trans
      N≤m
      (NatOrder.≤SumLeft {n = m} {k = n})


tailSum-powerSeriesTerm-zeroAfter :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  (h : ℝᶜ) →
  (m k : ℕ) →
  NatOrder._≤_ N m →
  tailSum (powerSeriesTerm a h) m k ≡ 0ᶜ
tailSum-powerSeriesTerm-zeroAfter N zeroAfter h m k N≤m =
  cong
    (λ u → partialSum u k)
    (funExt
      (λ n →
        drop-powerSeriesTerm-zeroAfter N zeroAfter h m n N≤m))
    ∙ tailSum-zero-sequence 0 k


finiteSupportPowerSeriesTailBound :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  (h : ℝᶜ) →
  PowerSeriesTailBound a h (λ _ → N)
finiteSupportPowerSeriesTailBound N zeroAfter h ε m k N≤m =
  subst
    (BoundedByᶜ ε)
    (sym (tailSum-powerSeriesTerm-zeroAfter N zeroAfter h m k N≤m))
    (bounded-byᶜ-zero ε)


finiteSupportPowerSeriesOnBallWith :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBallWith a ρ (λ _ → N)
finiteSupportPowerSeriesOnBallWith N zeroAfter =
  record
    { antitoneModulus = λ _ → NatOrder.≤-refl
    ; tailBound =
        λ h _ →
          finiteSupportPowerSeriesTailBound N zeroAfter h
    }


finiteSupportPowerSeriesOnBall :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall a ρ
finiteSupportPowerSeriesOnBall N zeroAfter =
  (λ _ → N) , finiteSupportPowerSeriesOnBallWith N zeroAfter


finiteSupportPowerSeriesInfiniteRadius :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  HasInfinitePowerSeriesRadius a
finiteSupportPowerSeriesInfiniteRadius N zeroAfter _ =
  finiteSupportPowerSeriesOnBall N zeroAfter


polynomialPowerSeriesOnBallWith :
  {a : PowerSeries} →
  (poly : IsPolynomialPowerSeries a) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBallWith a ρ (λ _ → fst poly)
polynomialPowerSeriesOnBallWith (N , zeroAfter) =
  finiteSupportPowerSeriesOnBallWith N zeroAfter


polynomialPowerSeriesOnBall :
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall a ρ
polynomialPowerSeriesOnBall (N , zeroAfter) =
  finiteSupportPowerSeriesOnBall N zeroAfter


polynomialPowerSeriesInfiniteRadius :
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  HasInfinitePowerSeriesRadius a
polynomialPowerSeriesInfiniteRadius (N , zeroAfter) =
  finiteSupportPowerSeriesInfiniteRadius N zeroAfter


finiteSupportPowerSeriesSumOnBall-partialSum :
  {a : PowerSeries} →
  (N : ℕ) →
  (zeroAfter : PowerSeriesZeroAfter a N) →
  {ρ : ℚ⁺} →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    a
    ρ
    (λ _ → N)
    (finiteSupportPowerSeriesOnBallWith N zeroAfter)
    h
    h-bound
  ≡ powerSeriesPartialSum a h N
finiteSupportPowerSeriesSumOnBall-partialSum N zeroAfter h h-bound =
  powerSeriesSumOnBall-constantModulusPartialSum
    N
    (finiteSupportPowerSeriesOnBallWith N zeroAfter)
    h
    h-bound


centeredFiniteSupportPowerSeriesSumOnBall-partialSum :
  {a : PowerSeries} →
  (N : ℕ) →
  (zeroAfter : PowerSeriesZeroAfter a N) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  centeredPowerSeriesSumOnBall
    a
    c
    ρ
    (λ _ → N)
    (finiteSupportPowerSeriesOnBallWith N zeroAfter)
    x
    inBall
  ≡ powerSeriesPartialSum a (centeredDisplacement c x) N
centeredFiniteSupportPowerSeriesSumOnBall-partialSum N zeroAfter c x inBall =
  centeredPowerSeriesSumOnBall-constantModulusPartialSum
    N
    (finiteSupportPowerSeriesOnBallWith N zeroAfter)
    x
    inBall


polynomialPowerSeriesSumOnBall-partialSum :
  {a : PowerSeries} →
  (poly : IsPolynomialPowerSeries a) →
  {ρ : ℚ⁺} →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    a
    ρ
    (λ _ → fst poly)
    (polynomialPowerSeriesOnBallWith poly)
    h
    h-bound
  ≡ powerSeriesPartialSum a h (fst poly)
polynomialPowerSeriesSumOnBall-partialSum (N , zeroAfter) =
  finiteSupportPowerSeriesSumOnBall-partialSum N zeroAfter


centeredPolynomialPowerSeriesSumOnBall-partialSum :
  {a : PowerSeries} →
  (poly : IsPolynomialPowerSeries a) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  centeredPowerSeriesSumOnBall
    a
    c
    ρ
    (λ _ → fst poly)
    (polynomialPowerSeriesOnBallWith poly)
    x
    inBall
  ≡ powerSeriesPartialSum a (centeredDisplacement c x) (fst poly)
centeredPolynomialPowerSeriesSumOnBall-partialSum (N , zeroAfter) =
  centeredFiniteSupportPowerSeriesSumOnBall-partialSum N zeroAfter


addPowerSeriesZeroAfter :
  {a b : PowerSeries} →
  (N M : ℕ) →
  PowerSeriesZeroAfter a N →
  PowerSeriesZeroAfter b M →
  PowerSeriesZeroAfter (addPowerSeries a b) (Nat.max N M)
addPowerSeriesZeroAfter {a = a} {b = b} N M a-zero b-zero n max≤n =
  cong₂
    _+ᶜ_
    (a-zero n (NatOrder.≤-trans N≤max max≤n))
    (b-zero n (NatOrder.≤-trans M≤max max≤n)) ∙
  add-zero-left 0ᶜ
  where
  N≤max : NatOrder._≤_ N (Nat.max N M)
  N≤max =
    NatOrder.left-≤-max {m = N} {n = M}

  M≤max : NatOrder._≤_ M (Nat.max N M)
  M≤max =
    NatOrder.right-≤-max {n = M} {m = N}


addPowerSeriesPolynomial :
  {a b : PowerSeries} →
  IsPolynomialPowerSeries a →
  IsPolynomialPowerSeries b →
  IsPolynomialPowerSeries (addPowerSeries a b)
addPowerSeriesPolynomial (N , a-zero) (M , b-zero) =
  Nat.max N M , addPowerSeriesZeroAfter N M a-zero b-zero


negPowerSeriesZeroAfter :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  PowerSeriesZeroAfter (negPowerSeries a) N
negPowerSeriesZeroAfter N zeroAfter n N≤n =
  cong -ᶜ_ (zeroAfter n N≤n) ∙
  neg-zeroᶜ


negPowerSeriesPolynomial :
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  IsPolynomialPowerSeries (negPowerSeries a)
negPowerSeriesPolynomial (N , zeroAfter) =
  N , negPowerSeriesZeroAfter N zeroAfter


subPowerSeriesPolynomial :
  {a b : PowerSeries} →
  IsPolynomialPowerSeries a →
  IsPolynomialPowerSeries b →
  IsPolynomialPowerSeries (subPowerSeries a b)
subPowerSeriesPolynomial left right =
  addPowerSeriesPolynomial left (negPowerSeriesPolynomial right)


shiftPowerSeriesZeroAfter :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a (suc N) →
  PowerSeriesZeroAfter (shiftPowerSeries a) N
shiftPowerSeriesZeroAfter N zeroAfter n N≤n =
  zeroAfter (suc n) (NatOrder.suc-≤-suc N≤n)


cauchyProductPowerSeriesZeroLeft :
  {a b : PowerSeries} →
  PowerSeriesZeroAfter a zero →
  PowerSeriesZeroAfter (cauchyProductPowerSeries a b) zero
cauchyProductPowerSeriesZeroLeft {a = a} {b = b} zeroAfter zero _ =
  cong
    (λ c → c ·ᶜ b zero)
    (zeroAfter zero NatOrder.zero-≤) ∙
  mulᶜ-zero-left (b zero)
cauchyProductPowerSeriesZeroLeft {a = a} {b = b} zeroAfter (suc n) _ =
  cong₂
    _+ᶜ_
    (cong
      (λ c → c ·ᶜ b (suc n))
      (zeroAfter zero NatOrder.zero-≤) ∙
    mulᶜ-zero-left (b (suc n)))
    (cauchyProductPowerSeriesZeroLeft
      (λ k _ → zeroAfter (suc k) NatOrder.zero-≤)
      n
      NatOrder.zero-≤) ∙
  add-zero-left 0ᶜ


cauchyProductPowerSeriesZeroAfter :
  {a b : PowerSeries} →
  (N M : ℕ) →
  PowerSeriesZeroAfter a N →
  PowerSeriesZeroAfter b M →
  PowerSeriesZeroAfter (cauchyProductPowerSeries a b) (N Nat.+ M)
cauchyProductPowerSeriesZeroAfter zero M a-zero b-zero =
  powerSeriesZeroAfter-weaken
    NatOrder.zero-≤
    (cauchyProductPowerSeriesZeroLeft a-zero)
cauchyProductPowerSeriesZeroAfter (suc N) M a-zero b-zero zero sucNM≤0 =
  Empty.rec (NatOrder.¬-<-zero sucNM≤0)
cauchyProductPowerSeriesZeroAfter
  {a = a}
  {b = b}
  (suc N)
  M
  a-zero
  b-zero
  (suc n)
  sucNM≤sucn =
  cong₂
    _+ᶜ_
    (cong
      (λ c → a zero ·ᶜ c)
      (b-zero (suc n) M≤sucn) ∙
    mulᶜ-zero-right (a zero))
    (cauchyProductPowerSeriesZeroAfter
      N
      M
      (shiftPowerSeriesZeroAfter N a-zero)
      b-zero
      n
      (NatOrder.pred-≤-pred sucNM≤sucn)) ∙
  add-zero-left 0ᶜ
  where
  M≤sucNM : NatOrder._≤_ M (suc N Nat.+ M)
  M≤sucNM =
    NatOrder.≤SumRight {n = M} {k = suc N}

  M≤sucn : NatOrder._≤_ M (suc n)
  M≤sucn =
    NatOrder.≤-trans M≤sucNM sucNM≤sucn


cauchyProductPowerSeriesPolynomial :
  {a b : PowerSeries} →
  IsPolynomialPowerSeries a →
  IsPolynomialPowerSeries b →
  IsPolynomialPowerSeries (cauchyProductPowerSeries a b)
cauchyProductPowerSeriesPolynomial (N , a-zero) (M , b-zero) =
  N Nat.+ M , cauchyProductPowerSeriesZeroAfter N M a-zero b-zero


zeroPowerSeriesZeroAfter :
  PowerSeriesZeroAfter zeroPowerSeries zero
zeroPowerSeriesZeroAfter n _ =
  refl


zeroPowerSeriesPolynomial :
  IsPolynomialPowerSeries zeroPowerSeries
zeroPowerSeriesPolynomial =
  zero , zeroPowerSeriesZeroAfter


constantPowerSeriesZeroAfter :
  (c : ℝᶜ) →
  PowerSeriesZeroAfter (constantPowerSeries c) (suc zero)
constantPowerSeriesZeroAfter c zero 1≤0 =
  Empty.rec (NatOrder.¬-<-zero 1≤0)
constantPowerSeriesZeroAfter c (suc n) _ =
  refl


constantPowerSeriesPolynomial :
  (c : ℝᶜ) →
  IsPolynomialPowerSeries (constantPowerSeries c)
constantPowerSeriesPolynomial c =
  suc zero , constantPowerSeriesZeroAfter c


finitePowerSeries :
  (N : ℕ) →
  (Fin N → ℝᶜ) →
  PowerSeries
finitePowerSeries zero coeff n =
  0ᶜ
finitePowerSeries (suc N) coeff zero =
  coeff Fin.zero
finitePowerSeries (suc N) coeff (suc n) =
  finitePowerSeries N (λ i → coeff (Fin.suc i)) n


finitePowerSeriesEval :
  (N : ℕ) →
  (Fin N → ℝᶜ) →
  ℝᶜ →
  ℝᶜ
finitePowerSeriesEval zero coeff h =
  0ᶜ
finitePowerSeriesEval (suc N) coeff h =
  coeff Fin.zero +ᶜ
  h ·ᶜ finitePowerSeriesEval N (λ i → coeff (Fin.suc i)) h


shiftFinitePowerSeries :
  (N : ℕ) →
  (coeff : Fin (suc N) → ℝᶜ) →
  (n : ℕ) →
  shiftPowerSeries (finitePowerSeries (suc N) coeff) n ≡
  finitePowerSeries N (λ i → coeff (Fin.suc i)) n
shiftFinitePowerSeries N coeff n =
  refl


finitePowerSeriesEval-partialSum :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (h : ℝᶜ) →
  powerSeriesPartialSum (finitePowerSeries N coeff) h N ≡
  finitePowerSeriesEval N coeff h
finitePowerSeriesEval-partialSum zero coeff h =
  refl
finitePowerSeriesEval-partialSum (suc N) coeff h =
  powerSeriesPartialSum-shift (finitePowerSeries (suc N) coeff) h N ∙
  cong
    (λ s → coeff Fin.zero +ᶜ h ·ᶜ s)
    (powerSeriesPartialSum-cong
      (shiftFinitePowerSeries N coeff)
      refl
      N ∙
    finitePowerSeriesEval-partialSum
      N
      (λ i → coeff (Fin.suc i))
      h)


finitePowerSeriesZeroAfter :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  PowerSeriesZeroAfter (finitePowerSeries N coeff) N
finitePowerSeriesZeroAfter zero coeff n _ =
  refl
finitePowerSeriesZeroAfter (suc N) coeff zero sucN≤0 =
  Empty.rec (NatOrder.¬-<-zero sucN≤0)
finitePowerSeriesZeroAfter (suc N) coeff (suc n) sucN≤sucn =
  finitePowerSeriesZeroAfter
    N
    (λ i → coeff (Fin.suc i))
    n
    (NatOrder.pred-≤-pred sucN≤sucn)


finitePowerSeriesOnBallWith :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBallWith (finitePowerSeries N coeff) ρ (λ _ → N)
finitePowerSeriesOnBallWith N coeff =
  finiteSupportPowerSeriesOnBallWith
    N
    (finitePowerSeriesZeroAfter N coeff)


finitePowerSeriesOnBall :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall (finitePowerSeries N coeff) ρ
finitePowerSeriesOnBall N coeff =
  finiteSupportPowerSeriesOnBall
    N
    (finitePowerSeriesZeroAfter N coeff)


finitePowerSeriesSumOnBall-eval :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  {ρ : ℚ⁺} →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (finitePowerSeries N coeff)
    ρ
    (λ _ → N)
    (finitePowerSeriesOnBallWith N coeff)
    h
    h-bound
  ≡ finitePowerSeriesEval N coeff h
finitePowerSeriesSumOnBall-eval N coeff h h-bound =
  powerSeriesSumOnBall-constantModulusPartialSum
    N
    (finitePowerSeriesOnBallWith N coeff)
    h
    h-bound ∙
  finitePowerSeriesEval-partialSum N coeff h


centeredFinitePowerSeriesSumOnBall-eval :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  centeredPowerSeriesSumOnBall
    (finitePowerSeries N coeff)
    c
    ρ
    (λ _ → N)
    (finitePowerSeriesOnBallWith N coeff)
    x
    inBall
  ≡ finitePowerSeriesEval N coeff (centeredDisplacement c x)
centeredFinitePowerSeriesSumOnBall-eval N coeff c x inBall =
  centeredPowerSeriesSumOnBall-constantModulusPartialSum
    N
    (finitePowerSeriesOnBallWith N coeff)
    x
    inBall ∙
  finitePowerSeriesEval-partialSum
    N
    coeff
    (centeredDisplacement c x)


finitePowerSeriesEvalHasPowerSeriesAtWith :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesAtWith
    (λ x → finitePowerSeriesEval N coeff (centeredDisplacement c x))
    c
    (finitePowerSeries N coeff)
    ρ
    (λ _ → N)
finitePowerSeriesEvalHasPowerSeriesAtWith N coeff c =
  finitePowerSeriesOnBallWith N coeff ,
  λ x inBall →
    sym (centeredFinitePowerSeriesSumOnBall-eval N coeff c x inBall)


finitePowerSeriesEvalHasPowerSeriesAtOnBall :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  HasPowerSeriesAtOnBall
    (λ x → finitePowerSeriesEval N coeff (centeredDisplacement c x))
    c
    (finitePowerSeries N coeff)
    ρ
finitePowerSeriesEvalHasPowerSeriesAtOnBall N coeff c ρ =
  (λ _ → N) ,
  finitePowerSeriesEvalHasPowerSeriesAtWith N coeff c


finitePowerSeriesEvalHasPowerSeriesAt :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  HasPowerSeriesAt
    (λ x → finitePowerSeriesEval N coeff (centeredDisplacement c x))
    c
    (finitePowerSeries N coeff)
finitePowerSeriesEvalHasPowerSeriesAt N coeff c =
  1⁺ ,
  finitePowerSeriesEvalHasPowerSeriesAtOnBall N coeff c 1⁺


finitePowerSeriesEvalAnalyticAt :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  AnalyticAt
    (λ x → finitePowerSeriesEval N coeff (centeredDisplacement c x))
    c
finitePowerSeriesEvalAnalyticAt N coeff c =
  finitePowerSeries N coeff ,
  finitePowerSeriesEvalHasPowerSeriesAt N coeff c


finitePowerSeriesPolynomial :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  IsPolynomialPowerSeries (finitePowerSeries N coeff)
finitePowerSeriesPolynomial N coeff =
  N , finitePowerSeriesZeroAfter N coeff


finitePowerSeriesInfiniteRadius :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  HasInfinitePowerSeriesRadius (finitePowerSeries N coeff)
finitePowerSeriesInfiniteRadius N coeff =
  polynomialPowerSeriesInfiniteRadius (finitePowerSeriesPolynomial N coeff)


monomialPowerSeries :
  ℕ →
  ℝᶜ →
  PowerSeries
monomialPowerSeries zero c zero =
  c
monomialPowerSeries zero c (suc _) =
  0ᶜ
monomialPowerSeries (suc d) c zero =
  0ᶜ
monomialPowerSeries (suc d) c (suc n) =
  monomialPowerSeries d c n


monomialPowerSeriesZeroAfter :
  (d : ℕ) →
  (c : ℝᶜ) →
  PowerSeriesZeroAfter (monomialPowerSeries d c) (suc d)
monomialPowerSeriesZeroAfter zero c zero 1≤0 =
  Empty.rec (NatOrder.¬-<-zero 1≤0)
monomialPowerSeriesZeroAfter zero c (suc n) _ =
  refl
monomialPowerSeriesZeroAfter (suc d) c zero sucsd≤0 =
  Empty.rec (NatOrder.¬-<-zero sucsd≤0)
monomialPowerSeriesZeroAfter (suc d) c (suc n) sucsd≤sucn =
  monomialPowerSeriesZeroAfter
    d
    c
    n
    (NatOrder.pred-≤-pred sucsd≤sucn)


monomialPowerSeriesOnBallWith :
  (d : ℕ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBallWith (monomialPowerSeries d c) ρ (λ _ → suc d)
monomialPowerSeriesOnBallWith d c =
  finiteSupportPowerSeriesOnBallWith
    (suc d)
    (monomialPowerSeriesZeroAfter d c)


monomialPowerSeriesOnBall :
  (d : ℕ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall (monomialPowerSeries d c) ρ
monomialPowerSeriesOnBall d c =
  finiteSupportPowerSeriesOnBall
    (suc d)
    (monomialPowerSeriesZeroAfter d c)


monomialPowerSeriesPolynomial :
  (d : ℕ) →
  (c : ℝᶜ) →
  IsPolynomialPowerSeries (monomialPowerSeries d c)
monomialPowerSeriesPolynomial d c =
  suc d , monomialPowerSeriesZeroAfter d c


monomialPowerSeriesInfiniteRadius :
  (d : ℕ) →
  (c : ℝᶜ) →
  HasInfinitePowerSeriesRadius (monomialPowerSeries d c)
monomialPowerSeriesInfiniteRadius d c =
  polynomialPowerSeriesInfiniteRadius (monomialPowerSeriesPolynomial d c)


derivativePowerSeriesZeroAfter :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a (suc N) →
  PowerSeriesZeroAfter (derivativePowerSeries a) N
derivativePowerSeriesZeroAfter N zeroAfter n N≤n =
  cong
    (λ c → naturalReal (suc n) ·ᶜ c)
    (zeroAfter (suc n) (NatOrder.suc-≤-suc N≤n)) ∙
  mulᶜ-zero-right (naturalReal (suc n))


derivativePowerSeriesZeroAfterZero :
  {a : PowerSeries} →
  PowerSeriesZeroAfter a zero →
  PowerSeriesZeroAfter (derivativePowerSeries a) zero
derivativePowerSeriesZeroAfterZero zeroAfter n _ =
  cong
    (λ c → naturalReal (suc n) ·ᶜ c)
    (zeroAfter (suc n) NatOrder.zero-≤) ∙
  mulᶜ-zero-right (naturalReal (suc n))


derivativePowerSeriesPolynomial :
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  IsPolynomialPowerSeries (derivativePowerSeries a)
derivativePowerSeriesPolynomial (zero , zeroAfter) =
  zero , derivativePowerSeriesZeroAfterZero zeroAfter
derivativePowerSeriesPolynomial (suc N , zeroAfter) =
  N , derivativePowerSeriesZeroAfter N zeroAfter


derivativeFinitePowerSeriesZeroAfterLength :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  PowerSeriesZeroAfter (derivativePowerSeries (finitePowerSeries N coeff)) N
derivativeFinitePowerSeriesZeroAfterLength zero coeff =
  derivativePowerSeriesZeroAfterZero
    (finitePowerSeriesZeroAfter zero coeff)
derivativeFinitePowerSeriesZeroAfterLength (suc N) coeff =
  powerSeriesZeroAfter-weaken
    (suc zero , refl)
    (derivativePowerSeriesZeroAfter
      N
      (finitePowerSeriesZeroAfter (suc N) coeff))


finitePowerSeriesFormalDerivativeEval :
  (N : ℕ) →
  (Fin N → ℝᶜ) →
  ℝᶜ →
  ℝᶜ
finitePowerSeriesFormalDerivativeEval N coeff h =
  powerSeriesPartialSum
    (derivativePowerSeries (finitePowerSeries N coeff))
    h
    N


finitePowerSeriesFormalDerivativeOnBallWith :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBallWith
    (derivativePowerSeries (finitePowerSeries N coeff))
    ρ
    (λ _ → N)
finitePowerSeriesFormalDerivativeOnBallWith N coeff =
  finiteSupportPowerSeriesOnBallWith
    N
    (derivativeFinitePowerSeriesZeroAfterLength N coeff)


finitePowerSeriesFormalDerivativeSumOnBall-eval :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  {ρ : ℚ⁺} →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (derivativePowerSeries (finitePowerSeries N coeff))
    ρ
    (λ _ → N)
    (finitePowerSeriesFormalDerivativeOnBallWith N coeff)
    h
    h-bound
  ≡ finitePowerSeriesFormalDerivativeEval N coeff h
finitePowerSeriesFormalDerivativeSumOnBall-eval N coeff h h-bound =
  powerSeriesSumOnBall-constantModulusPartialSum
    N
    (finitePowerSeriesFormalDerivativeOnBallWith N coeff)
    h
    h-bound


centeredFinitePowerSeriesFormalDerivativeSumOnBall-eval :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  centeredPowerSeriesSumOnBall
    (derivativePowerSeries (finitePowerSeries N coeff))
    c
    ρ
    (λ _ → N)
    (finitePowerSeriesFormalDerivativeOnBallWith N coeff)
    x
    inBall
  ≡ finitePowerSeriesFormalDerivativeEval N coeff (centeredDisplacement c x)
centeredFinitePowerSeriesFormalDerivativeSumOnBall-eval N coeff c x inBall =
  centeredPowerSeriesSumOnBall-constantModulusPartialSum
    N
    (finitePowerSeriesFormalDerivativeOnBallWith N coeff)
    x
    inBall


finitePowerSeriesFormalDerivativeHasPowerSeriesAtWith :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesAtWith
    (λ x →
      finitePowerSeriesFormalDerivativeEval
        N
        coeff
        (centeredDisplacement c x))
    c
    (derivativePowerSeries (finitePowerSeries N coeff))
    ρ
    (λ _ → N)
finitePowerSeriesFormalDerivativeHasPowerSeriesAtWith N coeff c =
  finitePowerSeriesFormalDerivativeOnBallWith N coeff ,
  λ x inBall →
    sym
      (centeredFinitePowerSeriesFormalDerivativeSumOnBall-eval
        N
        coeff
        c
        x
        inBall)


finitePowerSeriesFormalDerivativeHasPowerSeriesAtOnBall :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  HasPowerSeriesAtOnBall
    (λ x →
      finitePowerSeriesFormalDerivativeEval
        N
        coeff
        (centeredDisplacement c x))
    c
    (derivativePowerSeries (finitePowerSeries N coeff))
    ρ
finitePowerSeriesFormalDerivativeHasPowerSeriesAtOnBall N coeff c ρ =
  (λ _ → N) ,
  finitePowerSeriesFormalDerivativeHasPowerSeriesAtWith N coeff c


finitePowerSeriesFormalDerivativeHasPowerSeriesAt :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  HasPowerSeriesAt
    (λ x →
      finitePowerSeriesFormalDerivativeEval
        N
        coeff
        (centeredDisplacement c x))
    c
    (derivativePowerSeries (finitePowerSeries N coeff))
finitePowerSeriesFormalDerivativeHasPowerSeriesAt N coeff c =
  1⁺ ,
  finitePowerSeriesFormalDerivativeHasPowerSeriesAtOnBall N coeff c 1⁺


finitePowerSeriesFormalDerivativeAnalyticAt :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  AnalyticAt
    (λ x →
      finitePowerSeriesFormalDerivativeEval
        N
        coeff
        (centeredDisplacement c x))
    c
finitePowerSeriesFormalDerivativeAnalyticAt N coeff c =
  derivativePowerSeries (finitePowerSeries N coeff) ,
  finitePowerSeriesFormalDerivativeHasPowerSeriesAt N coeff c


derivativePowerSeriesPolynomialInfiniteRadius :
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  HasInfinitePowerSeriesRadius (derivativePowerSeries a)
derivativePowerSeriesPolynomialInfiniteRadius poly =
  polynomialPowerSeriesInfiniteRadius (derivativePowerSeriesPolynomial poly)


primitivePowerSeriesZeroAfter :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  PowerSeriesZeroAfter (primitivePowerSeries a) (suc N)
primitivePowerSeriesZeroAfter N zeroAfter zero sucN≤0 =
  Empty.rec (NatOrder.¬-<-zero sucN≤0)
primitivePowerSeriesZeroAfter N zeroAfter (suc n) sucN≤sucn =
  cong
    (λ c → inverseSucReal n ·ᶜ c)
    (zeroAfter n (NatOrder.pred-≤-pred sucN≤sucn)) ∙
  mulᶜ-zero-right (inverseSucReal n)


primitivePowerSeriesPolynomial :
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  IsPolynomialPowerSeries (primitivePowerSeries a)
primitivePowerSeriesPolynomial (N , zeroAfter) =
  suc N , primitivePowerSeriesZeroAfter N zeroAfter


finitePowerSeriesFormalPrimitiveEval :
  (N : ℕ) →
  (Fin N → ℝᶜ) →
  ℝᶜ →
  ℝᶜ
finitePowerSeriesFormalPrimitiveEval N coeff h =
  powerSeriesPartialSum
    (primitivePowerSeries (finitePowerSeries N coeff))
    h
    (suc N)


finitePowerSeriesFormalPrimitiveOnBallWith :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBallWith
    (primitivePowerSeries (finitePowerSeries N coeff))
    ρ
    (λ _ → suc N)
finitePowerSeriesFormalPrimitiveOnBallWith N coeff =
  finiteSupportPowerSeriesOnBallWith
    (suc N)
    (primitivePowerSeriesZeroAfter N (finitePowerSeriesZeroAfter N coeff))


finitePowerSeriesFormalPrimitiveSumOnBall-eval :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  {ρ : ℚ⁺} →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (primitivePowerSeries (finitePowerSeries N coeff))
    ρ
    (λ _ → suc N)
    (finitePowerSeriesFormalPrimitiveOnBallWith N coeff)
    h
    h-bound
  ≡ finitePowerSeriesFormalPrimitiveEval N coeff h
finitePowerSeriesFormalPrimitiveSumOnBall-eval N coeff h h-bound =
  powerSeriesSumOnBall-constantModulusPartialSum
    (suc N)
    (finitePowerSeriesFormalPrimitiveOnBallWith N coeff)
    h
    h-bound


centeredFinitePowerSeriesFormalPrimitiveSumOnBall-eval :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  centeredPowerSeriesSumOnBall
    (primitivePowerSeries (finitePowerSeries N coeff))
    c
    ρ
    (λ _ → suc N)
    (finitePowerSeriesFormalPrimitiveOnBallWith N coeff)
    x
    inBall
  ≡ finitePowerSeriesFormalPrimitiveEval N coeff (centeredDisplacement c x)
centeredFinitePowerSeriesFormalPrimitiveSumOnBall-eval N coeff c x inBall =
  centeredPowerSeriesSumOnBall-constantModulusPartialSum
    (suc N)
    (finitePowerSeriesFormalPrimitiveOnBallWith N coeff)
    x
    inBall


finitePowerSeriesFormalPrimitiveHasPowerSeriesAtWith :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesAtWith
    (λ x →
      finitePowerSeriesFormalPrimitiveEval
        N
        coeff
        (centeredDisplacement c x))
    c
    (primitivePowerSeries (finitePowerSeries N coeff))
    ρ
    (λ _ → suc N)
finitePowerSeriesFormalPrimitiveHasPowerSeriesAtWith N coeff c =
  finitePowerSeriesFormalPrimitiveOnBallWith N coeff ,
  λ x inBall →
    sym
      (centeredFinitePowerSeriesFormalPrimitiveSumOnBall-eval
        N
        coeff
        c
        x
        inBall)


finitePowerSeriesFormalPrimitiveHasPowerSeriesAtOnBall :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  HasPowerSeriesAtOnBall
    (λ x →
      finitePowerSeriesFormalPrimitiveEval
        N
        coeff
        (centeredDisplacement c x))
    c
    (primitivePowerSeries (finitePowerSeries N coeff))
    ρ
finitePowerSeriesFormalPrimitiveHasPowerSeriesAtOnBall N coeff c ρ =
  (λ _ → suc N) ,
  finitePowerSeriesFormalPrimitiveHasPowerSeriesAtWith N coeff c


finitePowerSeriesFormalPrimitiveHasPowerSeriesAt :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  HasPowerSeriesAt
    (λ x →
      finitePowerSeriesFormalPrimitiveEval
        N
        coeff
        (centeredDisplacement c x))
    c
    (primitivePowerSeries (finitePowerSeries N coeff))
finitePowerSeriesFormalPrimitiveHasPowerSeriesAt N coeff c =
  1⁺ ,
  finitePowerSeriesFormalPrimitiveHasPowerSeriesAtOnBall N coeff c 1⁺


finitePowerSeriesFormalPrimitiveAnalyticAt :
  (N : ℕ) →
  (coeff : Fin N → ℝᶜ) →
  (c : ℝᶜ) →
  AnalyticAt
    (λ x →
      finitePowerSeriesFormalPrimitiveEval
        N
        coeff
        (centeredDisplacement c x))
    c
finitePowerSeriesFormalPrimitiveAnalyticAt N coeff c =
  primitivePowerSeries (finitePowerSeries N coeff) ,
  finitePowerSeriesFormalPrimitiveHasPowerSeriesAt N coeff c


primitivePowerSeriesPolynomialInfiniteRadius :
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  HasInfinitePowerSeriesRadius (primitivePowerSeries a)
primitivePowerSeriesPolynomialInfiniteRadius poly =
  polynomialPowerSeriesInfiniteRadius (primitivePowerSeriesPolynomial poly)


rationalScalePowerSeriesZeroAfter :
  (q : ℚ) →
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  PowerSeriesZeroAfter (rationalScalePowerSeries q a) N
rationalScalePowerSeriesZeroAfter q N zeroAfter n N≤n =
  cong
    (λ c → rational q ·ᶜ c)
    (zeroAfter n N≤n) ∙
  mulᶜ-zero-right (rational q)


rationalScalePowerSeriesPolynomial :
  (q : ℚ) →
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  IsPolynomialPowerSeries (rationalScalePowerSeries q a)
rationalScalePowerSeriesPolynomial q (N , zeroAfter) =
  N , rationalScalePowerSeriesZeroAfter q N zeroAfter
