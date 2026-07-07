{-

Convergence transport for formal derivative coefficients

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.Internal where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
  using (0ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using
    ( _·ᶜ_
    ; mulᶜ-comm
    ; mulᶜ-zero-left
    ; mulᶜ-rational-left
    ; mulᶜ-rational-left-assoc
    ; mulᶜ-rational-rational
    ; mulᶜ-rational-right
    ; mulᶜ-rational-right-assoc
    ; mulᶜ-comm-rational-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_ ; neg-rational)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarOrder
  using (scalarMulᶜ-pres≤ᶜ-nonnegative)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using
    ( bounded-byᶜ-mul
    ; mulᶜ-pres≤ᶜ-right
    ; mulᶜ≤abs-product
    ; neg-mulᶜ≤abs-product
    ; scalarMulᶜ-nonnegative
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
  using
    ( scalarMulᶜ
    ; scalarMulᶜ-assoc
    ; scalarMulᶜ-neg-real
    ; scalarMulᶜ-one
    )
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-refl ; ≤ᶜ-trans)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using
    ( BoundedByᶜ
    ; rational-bound→boundedᶜ
    ; rational-closed-boundᶜ
    ; rational-closed-bound→boundedᶜ
    ; scalar-bound-rational-boundᶜ
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using
    ( absᶜ
    ; absᶜ-least
    ; absᶜ-nonnegative
    ; ≤ᶜabsᶜ-left
    ; ≤ᶜabsᶜ-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
  using (≤ℚ→rational≤ᶜ)
open import Constructive.Analysis.Reals.Series
  using
    ( AntitoneTailModulus
    ; SeriesMajorizedBy
    ; TailBound
    ; drop
    ; tailBound-drop
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Majorant
  using (bounded-byᶜ-abs)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using
    ( positiveGeometricGap
    ; positiveGeometricPower-linear-bound
    ; positivePower
    ; positivePower-radius
    ; positiveRationalPower-nonnegative
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Rational
  using (rationalPower)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using
    ( PowerSeriesMajorizedOnBall
    ; hasPowerSeriesOnBallFromBoundedTerms
    ; hasPowerSeriesOnBallFromTermBounds
    ; hasPowerSeriesOnBallWithFromBoundedTerms
    ; hasPowerSeriesOnBallWithFromTermBounds
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
  open CommRingStr (𝓡 .snd)

  ratio-power-step :
    (q qn s sn : 𝓡 .fst) →
    (q · qn) · (s · sn) ≡ (q · s) · (qn · sn)
  ratio-power-step _ _ _ _ = solve! 𝓡

  linear-gap-reassoc :
    (N q g : 𝓡 .fst) →
    (N · q) · g ≡ q · (N · g)
  linear-gap-reassoc _ _ _ = solve! 𝓡

  bound-gap-expand :
    (g i : 𝓡 .fst) →
    (1r + i) · g ≡ (i · g) + g
  bound-gap-expand _ _ = solve! 𝓡

  scale-sigma-cancel-form :
    (i b s sn : 𝓡 .fst) →
    (i · b) · (s · sn) ≡ (i · s) · (b · sn)
  scale-sigma-cancel-form _ _ _ _ = solve! 𝓡

  coefficient-sigma-cancel-form :
    (N i r s : 𝓡 .fst) →
    ((N · i) · r) · s ≡ N · ((i · s) · r)
  coefficient-sigma-cancel-form _ _ _ _ = solve! 𝓡

  scalar-product-form :
    (N i r : 𝓡 .fst) →
    N · (i · r) ≡ (N · i) · r
  scalar-product-form _ _ _ = solve! 𝓡

mulᶜ-nonnegative :
  (x y : ℝᶜ) →
  0ᶜ ≤ᶜ x →
  0ᶜ ≤ᶜ y →
  0ᶜ ≤ᶜ x ·ᶜ y
mulᶜ-nonnegative x y 0≤x 0≤y =
  subst
    (λ z → z ≤ᶜ x ·ᶜ y)
    (mulᶜ-zero-left y)
    (mulᶜ-pres≤ᶜ-right 0ᶜ x y 0≤y 0≤x)

absᶜ-mul≤product :
  (x y X Y : ℝᶜ) →
  0ᶜ ≤ᶜ X →
  0ᶜ ≤ᶜ Y →
  absᶜ x ≤ᶜ X →
  absᶜ y ≤ᶜ Y →
  absᶜ (x ·ᶜ y) ≤ᶜ X ·ᶜ Y
absᶜ-mul≤product x y X Y 0≤X 0≤Y absx≤X absy≤Y =
  absᶜ-least
    (x ·ᶜ y)
    (X ·ᶜ Y)
    (mulᶜ-nonnegative X Y 0≤X 0≤Y)
    (≤ᶜ-trans
      {x = x ·ᶜ y}
      {y = absᶜ x ·ᶜ absᶜ y}
      {z = X ·ᶜ Y}
      (mulᶜ≤abs-product x y)
      absProduct≤majorantProduct)
    (≤ᶜ-trans
      {x = -ᶜ (x ·ᶜ y)}
      {y = absᶜ x ·ᶜ absᶜ y}
      {z = X ·ᶜ Y}
      (neg-mulᶜ≤abs-product x y)
      absProduct≤majorantProduct)
  where
  absProduct≤majorantProduct :
    absᶜ x ·ᶜ absᶜ y ≤ᶜ X ·ᶜ Y
  absProduct≤majorantProduct =
    ≤ᶜ-trans
      {x = absᶜ x ·ᶜ absᶜ y}
      {y = X ·ᶜ absᶜ y}
      {z = X ·ᶜ Y}
      (mulᶜ-pres≤ᶜ-right
        (absᶜ x)
        X
        (absᶜ y)
        (absᶜ-nonnegative y)
        absx≤X)
      (subst2
        _≤ᶜ_
        (mulᶜ-comm (absᶜ y) X)
        (mulᶜ-comm Y X)
        (mulᶜ-pres≤ᶜ-right
          (absᶜ y)
          Y
          X
          0≤X
          absy≤Y))

absᶜ-scalarMul≤ :
  (q : ℚ) →
  Rational.0ℚ ℚOrder.≤ q →
  {x X : ℝᶜ} →
  0ᶜ ≤ᶜ X →
  absᶜ x ≤ᶜ X →
  absᶜ (scalarMulᶜ q x) ≤ᶜ scalarMulᶜ q X
absᶜ-scalarMul≤ q 0≤q {x = x} {X = X} 0≤X absx≤X =
  absᶜ-least
    (scalarMulᶜ q x)
    (scalarMulᶜ q X)
    (scalarMulᶜ-nonnegative q 0≤q {x = X} 0≤X)
    (scalarMulᶜ-pres≤ᶜ-nonnegative
      q
      0≤q
      {x = x}
      {y = X}
      (≤ᶜ-trans
        {x = x}
        {y = absᶜ x}
        {z = X}
        (≤ᶜabsᶜ-left x)
        absx≤X))
    (subst
      (λ y → y ≤ᶜ scalarMulᶜ q X)
      (scalarMulᶜ-neg-real q x)
      (scalarMulᶜ-pres≤ᶜ-nonnegative
        q
        0≤q
        {x = -ᶜ x}
        {y = X}
        (≤ᶜ-trans
          {x = -ᶜ x}
          {y = absᶜ x}
          {z = X}
          (≤ᶜabsᶜ-right x)
          absx≤X)))

absᶜ-rational-nonnegative :
  (q : ℚ) →
  Rational.0ℚ ℚOrder.≤ q →
  absᶜ (rational q) ≤ᶜ rational q
absᶜ-rational-nonnegative q 0≤q =
  absᶜ-least
    (rational q)
    (rational q)
    (≤ℚ→rational≤ᶜ {q = Rational.0ℚ} {r = q} 0≤q)
    (≤ᶜ-refl (rational q))
    (subst
      (λ x → x ≤ᶜ rational q)
      (sym (neg-rational q))
      (≤ℚ→rational≤ᶜ
        {q = ℚ.- q}
        {r = q}
        (Rational.≤-trans
          {p = ℚ.- q}
          {q = Rational.0ℚ}
          {r = q}
          (Rational.neg-nonpositive 0≤q)
          0≤q)))

rationalRatioPowerTimesPower :
  (r s : ℚ) →
  (0<s : Rational.0ℚ ℚOrder.< s) →
  (n : ℕ) →
  rationalPower (r ℚ.· Rational.posInv s 0<s) n ℚ.·
    rationalPower s n
  ≡
  rationalPower r n
rationalRatioPowerTimesPower r s 0<s zero =
  ℚ.·IdL Rational.1ℚ
rationalRatioPowerTimesPower r s 0<s (suc n) =
  SolverHelpers.ratio-power-step
    ℚCommRing
    q
    qⁿ
    s
    sⁿ ∙
  cong₂
    (λ x y → x ℚ.· y)
    q*s≡r
    (rationalRatioPowerTimesPower r s 0<s n)
  where
  q : ℚ
  q =
    r ℚ.· Rational.posInv s 0<s

  qⁿ : ℚ
  qⁿ =
    rationalPower q n

  sⁿ : ℚ
  sⁿ =
    rationalPower s n

  q*s≡r : q ℚ.· s ≡ r
  q*s≡r =
    sym (ℚ.·Assoc r (Rational.posInv s 0<s) s) ∙
    cong (r ℚ.·_) (Rational.posInv-left s 0<s) ∙
    ℚ.·IdR r

derivativeStrictSubballRatio :
  ℚ⁺ →
  ℚ⁺ →
  ℚ⁺
derivativeStrictSubballRatio ρ σ =
  ρ *⁺ posInv⁺ σ

derivativeStrictSubballRatio<1 :
  {ρ σ : ℚ⁺} →
  radius ρ ℚOrder.< radius σ →
  radius (derivativeStrictSubballRatio ρ σ) ℚOrder.< Rational.1ℚ
derivativeStrictSubballRatio<1 {ρ = ρ} {σ = σ} ρ<σ =
  Rational.div-positive-denom-<1
    {q = radius ρ}
    {a = radius σ}
    ρ<σ
    (σ .snd)

derivativeStrictSubballGap :
  (ρ σ : ℚ⁺) →
  radius ρ ℚOrder.< radius σ →
  ℚ⁺
derivativeStrictSubballGap ρ σ ρ<σ =
  1⁺ ⊖ derivativeStrictSubballRatio ρ σ
    [ derivativeStrictSubballRatio<1 {ρ = ρ} {σ = σ} ρ<σ ]

derivativeStrictSubballScale :
  (ρ σ : ℚ⁺) →
  radius ρ ℚOrder.< radius σ →
  ℚ⁺
derivativeStrictSubballScale ρ σ ρ<σ =
  posInv⁺ σ *⁺ (1⁺ +⁺ posInv⁺ (derivativeStrictSubballGap ρ σ ρ<σ))

derivativeStrictSubballModulus :
  {ρ σ : ℚ⁺} →
  radius ρ ℚOrder.< radius σ →
  (ℚ⁺ → ℕ) →
  ℚ⁺ →
  ℕ
derivativeStrictSubballModulus {ρ = ρ} {σ = σ} ρ<σ ν =
  rationalScaleModulus
    (radius (derivativeStrictSubballScale ρ σ ρ<σ))
    ν

positiveRationalSelfBounded :
  (ρ : ℚ⁺) →
  BoundedByᶜ ρ (rational (radius ρ))
positiveRationalSelfBounded ρ =
  rational-closed-bound→boundedᶜ
    ρ
    (radius ρ)
    (rational-closed-boundᶜ
      (Rational.≤-refl (radius ρ))
      negρ≤ρ)
  where
  0≤ρ : Rational.0ℚ ℚOrder.≤ radius ρ
  0≤ρ =
    Rational.<→≤
      {p = Rational.0ℚ}
      {q = radius ρ}
      (ρ .snd)

  negρ≤0 : ℚ.- radius ρ ℚOrder.≤ Rational.0ℚ
  negρ≤0 =
    Rational.neg-nonpositive 0≤ρ

  negρ≤ρ : ℚ.- radius ρ ℚOrder.≤ radius ρ
  negρ≤ρ =
    Rational.≤-trans
      {p = ℚ.- radius ρ}
      {q = Rational.0ℚ}
      {r = radius ρ}
      negρ≤0
      0≤ρ

realPower-rational-positive :
  (ρ : ℚ⁺) →
  (n : ℕ) →
  realPower (rational (radius ρ)) n ≡
  rational (radius (positivePower ρ n))
realPower-rational-positive ρ zero =
  refl
realPower-rational-positive ρ (suc n) =
  cong
    (λ p → rational (radius ρ) ·ᶜ p)
    (realPower-rational-positive ρ n) ∙
  mulᶜ-rational-rational (radius ρ) (radius (positivePower ρ n))

powerSeriesCoefficientFromRationalProbe :
  (ρ : ℚ⁺) →
  (a : PowerSeries) →
  (n : ℕ) →
  scalarMulᶜ
    (radius (posInv⁺ (positivePower ρ n)))
    (powerSeriesTerm a (rational (radius ρ)) n)
  ≡ a n
powerSeriesCoefficientFromRationalProbe ρ a n =
  cong
    (scalarMulᶜ invρⁿ)
    (cong (a n ·ᶜ_) (realPower-rational-positive ρ n) ∙
      mulᶜ-rational-right (a n) ρⁿ) ∙
  scalarMulᶜ-assoc invρⁿ ρⁿ (a n) ∙
  cong (λ q → scalarMulᶜ q (a n)) invρⁿ*ρⁿ≡1 ∙
  scalarMulᶜ-one (a n)
  where
  ρⁿ : ℚ
  ρⁿ =
    radius (positivePower ρ n)

  invρⁿ : ℚ
  invρⁿ =
    radius (posInv⁺ (positivePower ρ n))

  invρⁿ*ρⁿ≡1 : invρⁿ ℚ.· ρⁿ ≡ Rational.1ℚ
  invρⁿ*ρⁿ≡1 =
    cong radius (*⁺-posInv-left (positivePower ρ n))

naturalRealBound :
  (n : ℕ) →
  BoundedByᶜ
    (scalar-bound (Rational.natMul n Rational.1ℚ))
    (naturalReal n)
naturalRealBound n =
  rational-bound→boundedᶜ
    (scalar-bound natural)
    natural
    (scalar-bound-rational-boundᶜ natural)
  where
  natural : ℚ
  natural =
    Rational.natMul n Rational.1ℚ

ratioPowerTimesScalePower :
  (ρ σ : ℚ⁺) →
  (n : ℕ) →
  rationalPower (radius (derivativeStrictSubballRatio ρ σ)) n ℚ.·
    radius (positivePower σ n)
  ≡
  radius (positivePower ρ n)
ratioPowerTimesScalePower ρ σ n =
  cong
    (λ p →
      rationalPower (radius (derivativeStrictSubballRatio ρ σ)) n
        ℚ.· p)
    (positivePower-radius σ n) ∙
  rationalRatioPowerTimesPower
    (radius ρ)
    (radius σ)
    (σ .snd)
    n ∙
  sym (positivePower-radius ρ n)

geometricLinearCoefficient≤ :
  (q gap : ℚ⁺) →
  radius q ℚOrder.< Rational.1ℚ →
  radius gap ≡ positiveGeometricGap q →
  (n : ℕ) →
  Rational.natMul (suc n) Rational.1ℚ ℚ.·
    rationalPower (radius q) n
  ℚOrder.≤
  Rational.1ℚ ℚ.+ radius (posInv⁺ gap)
geometricLinearCoefficient≤ q gap q<1 gap-path n =
  Rational.mul-right-cancel-positive-≤
    {p = natural ℚ.· qpow}
    {q = bound}
    {c = gapR}
    (gap .snd)
    scaled≤
  where
  natural : ℚ
  natural =
    Rational.natMul (suc n) Rational.1ℚ

  qpow : ℚ
  qpow =
    rationalPower (radius q) n

  gapR : ℚ
  gapR =
    radius gap

  invgap : ℚ
  invgap =
    radius (posInv⁺ gap)

  bound : ℚ
  bound =
    Rational.1ℚ ℚ.+ invgap

  N : ℚ
  N =
    Rational.natMul n gapR

  qpow-nonnegative : Rational.0ℚ ℚOrder.≤ qpow
  qpow-nonnegative =
    positiveRationalPower-nonnegative q n

  gap≤1 : gapR ℚOrder.≤ Rational.1ℚ
  gap≤1 =
    subst
      (λ g → g ℚOrder.≤ Rational.1ℚ)
      (sym gap-path)
      (Rational.sub-nonnegative-right≤
        (Rational.<→≤ {p = Rational.0ℚ} {q = radius q} (q .snd)))

  natural-gap-path :
    natural ℚ.· gapR ≡ gapR ℚ.+ N
  natural-gap-path =
    ℚ.·Comm natural gapR ∙
    sym (Rational.natMul-mul-left (suc n) gapR Rational.1ℚ) ∙
    cong (Rational.natMul (suc n)) (ℚ.·IdR gapR) ∙
    Rational.natMul-suc n gapR ∙
    ℚ.+Comm N gapR

  natural-gap≤linear :
    natural ℚ.· gapR ℚOrder.≤ Rational.1ℚ ℚ.+ N
  natural-gap≤linear =
    subst
      (λ x → x ℚOrder.≤ Rational.1ℚ ℚ.+ N)
      (sym natural-gap-path)
      (Rational.+-rPres≤ {p = gapR} {q = Rational.1ℚ} {r = N} gap≤1)

  left≤linear :
    (natural ℚ.· qpow) ℚ.· gapR
      ℚOrder.≤
    qpow ℚ.· (Rational.1ℚ ℚ.+ N)
  left≤linear =
    subst
      (λ x → x ℚOrder.≤ qpow ℚ.· (Rational.1ℚ ℚ.+ N))
      (sym (SolverHelpers.linear-gap-reassoc ℚCommRing natural qpow gapR))
      (Rational.mul-left-nonnegative-≤
        qpow-nonnegative
        natural-gap≤linear)

  linear≤1 :
    qpow ℚ.· (Rational.1ℚ ℚ.+ N)
      ℚOrder.≤
    Rational.1ℚ
  linear≤1 =
    subst
      (λ g →
        qpow ℚ.· (Rational.1ℚ ℚ.+ Rational.natMul n g)
          ℚOrder.≤
        Rational.1ℚ)
      (sym gap-path)
      (positiveGeometricPower-linear-bound q q<1 n)

  left≤1 :
    (natural ℚ.· qpow) ℚ.· gapR ℚOrder.≤ Rational.1ℚ
  left≤1 =
    Rational.≤-trans left≤linear linear≤1

  bound-gap-path :
    bound ℚ.· gapR ≡ Rational.1ℚ ℚ.+ gapR
  bound-gap-path =
    SolverHelpers.bound-gap-expand ℚCommRing gapR invgap ∙
    cong (λ x → x ℚ.+ gapR) (Rational.posInv-left gapR (gap .snd))

  one≤bound-gap :
    Rational.1ℚ ℚOrder.≤ bound ℚ.· gapR
  one≤bound-gap =
    subst
      (λ x → Rational.1ℚ ℚOrder.≤ x)
      (sym bound-gap-path)
      (Rational.q≤q+nonnegative
        Rational.1ℚ
        gapR
        (Rational.<→≤ {p = Rational.0ℚ} {q = gapR} (gap .snd)))

  scaled≤ :
    (natural ℚ.· qpow) ℚ.· gapR
      ℚOrder.≤
    bound ℚ.· gapR
  scaled≤ =
    Rational.≤-trans left≤1 one≤bound-gap

derivativeStrictSubballCoefficient≤Scale :
  {ρ σ : ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  (n : ℕ) →
  ((Rational.natMul (suc n) Rational.1ℚ ℚ.·
    radius (posInv⁺ (positivePower σ (suc n)))) ℚ.·
    radius (positivePower ρ n))
  ℚOrder.≤
  radius (derivativeStrictSubballScale ρ σ ρ<σ)
derivativeStrictSubballCoefficient≤Scale {ρ = ρ} {σ = σ} ρ<σ n =
  Rational.mul-right-cancel-positive-≤
    {p = coeff}
    {q = scale}
    {c = σsuc}
    (positivePower σ (suc n) .snd)
    coeffσ≤scaleσ
  where
  natural : ℚ
  natural =
    Rational.natMul (suc n) Rational.1ℚ

  invσsuc : ℚ
  invσsuc =
    radius (posInv⁺ (positivePower σ (suc n)))

  ρpow : ℚ
  ρpow =
    radius (positivePower ρ n)

  σpow : ℚ
  σpow =
    radius (positivePower σ n)

  σsuc : ℚ
  σsuc =
    radius (positivePower σ (suc n))

  coeff : ℚ
  coeff =
    (natural ℚ.· invσsuc) ℚ.· ρpow

  ratio : ℚ⁺
  ratio =
    derivativeStrictSubballRatio ρ σ

  gap : ℚ⁺
  gap =
    derivativeStrictSubballGap ρ σ ρ<σ

  bound : ℚ
  bound =
    Rational.1ℚ ℚ.+ radius (posInv⁺ gap)

  scale : ℚ
  scale =
    radius (derivativeStrictSubballScale ρ σ ρ<σ)

  left-path :
    coeff ℚ.· σsuc ≡ natural ℚ.· ρpow
  left-path =
    SolverHelpers.coefficient-sigma-cancel-form
      ℚCommRing
      natural
      invσsuc
      ρpow
      σsuc ∙
    cong
      (λ x → natural ℚ.· (x ℚ.· ρpow))
      (Rational.posInv-left σsuc (positivePower σ (suc n) .snd)) ∙
    cong (natural ℚ.·_) (ℚ.·IdL ρpow)

  right-path :
    scale ℚ.· σsuc ≡ bound ℚ.· σpow
  right-path =
    SolverHelpers.scale-sigma-cancel-form
      ℚCommRing
      (radius (posInv⁺ σ))
      bound
      (radius σ)
      σpow ∙
    cong
      (λ x → x ℚ.· (bound ℚ.· σpow))
      (Rational.posInv-left (radius σ) (σ .snd)) ∙
    ℚ.·IdL (bound ℚ.· σpow)

  linear≤ :
    natural ℚ.· rationalPower (radius ratio) n
      ℚOrder.≤
    bound
  linear≤ =
    geometricLinearCoefficient≤
      ratio
      gap
      (derivativeStrictSubballRatio<1 {ρ = ρ} {σ = σ} ρ<σ)
      refl
      n

  scaled-ratio≤ :
    (natural ℚ.· rationalPower (radius ratio) n) ℚ.· σpow
      ℚOrder.≤
    bound ℚ.· σpow
  scaled-ratio≤ =
    ℚOrder.≤-·o
      (natural ℚ.· rationalPower (radius ratio) n)
      bound
      σpow
      (Rational.<→≤ {p = Rational.0ℚ} {q = σpow} (positivePower σ n .snd))
      linear≤

  ratio-path :
    (natural ℚ.· rationalPower (radius ratio) n) ℚ.· σpow
      ≡
    natural ℚ.· ρpow
  ratio-path =
    sym
      (ℚ.·Assoc
        natural
        (rationalPower (radius ratio) n)
        σpow) ∙
    cong (natural ℚ.·_) (ratioPowerTimesScalePower ρ σ n)

  scaled≤ :
    natural ℚ.· ρpow ℚOrder.≤ bound ℚ.· σpow
  scaled≤ =
    subst
      (λ x → x ℚOrder.≤ bound ℚ.· σpow)
      ratio-path
      scaled-ratio≤

  coeffσ≤scaleσ :
    coeff ℚ.· σsuc ℚOrder.≤ scale ℚ.· σsuc
  coeffσ≤scaleσ =
    subst2
      ℚOrder._≤_
      (sym left-path)
      (sym right-path)
      scaled≤

tripleScalarProductPath :
  (N i r : ℚ) →
  (x : ℝᶜ) →
  rational N ·ᶜ (scalarMulᶜ i x ·ᶜ rational r) ≡
  scalarMulᶜ ((N ℚ.· i) ℚ.· r) x
tripleScalarProductPath N i r x =
  cong
    (λ y → rational N ·ᶜ (y ·ᶜ rational r))
    (sym (mulᶜ-rational-left i x)) ∙
  cong
    (λ y → rational N ·ᶜ (y ·ᶜ rational r))
    (mulᶜ-comm (rational i) x) ∙
  cong
    (λ y → rational N ·ᶜ y)
    (mulᶜ-rational-right-assoc x i r) ∙
  cong
    (λ y → rational N ·ᶜ y)
    (mulᶜ-comm-rational-right x (i ℚ.· r)) ∙
  mulᶜ-rational-left-assoc N (i ℚ.· r) x ∙
  cong
    (λ q → rational q ·ᶜ x)
    (SolverHelpers.scalar-product-form ℚCommRing N i r) ∙
  mulᶜ-rational-left ((N ℚ.· i) ℚ.· r) x
