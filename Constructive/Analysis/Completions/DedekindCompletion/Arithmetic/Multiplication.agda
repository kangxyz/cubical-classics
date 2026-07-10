{-

Signed multiplication of constructive Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Multiplication where

open import Cubical.Foundations.Prelude

open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Analysis.Completions.DedekindCompletion.Base
open import Constructive.Analysis.Completions.DedekindCompletion.Order
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Base
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Negation
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.NonNegative

private
  variable
    ℓ ℓ' ℓᴾ : Level


module Multiplication (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  𝒦 : LinearlyOrderedField ℓ ℓ'
  𝒦 = 𝒜 .fst

  open CompletionBase 𝒦
  module OrdD = CompletionOrder 𝒦
  open OrdD
    using
      ( _≤_ ; _⊔_
      ; ≡→≤ ; ≤-trans
      ; left≤⊔ ; right≤⊔ ; ⊔≤ ; ⊔-idem
      )
  module Lat = OrdD.DedekindCompletionPseudolatticeTheory {ℓᴾ = ℓᴾ}

  open ArithmeticBase 𝒜
  open Addition {ℓᴾ}
  open Negation 𝒜 {ℓᴾ}
  open AdditiveGroup 𝒜 {ℓᴾ}
  open NonNegativeMultiplication 𝒜 {ℓᴾ}

  posPart : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ
  posPart x = x ⊔ 0𝔻

  negPart : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ
  negPart x = (-𝔻 x) ⊔ 0𝔻

  posPart≥0 :
    (x : DedekindCompletion ℓᴾ) →
    posPart x ≥0
  posPart≥0 x =
    right≤⊔ x 0𝔻

  negPart≥0 :
    (x : DedekindCompletion ℓᴾ) →
    negPart x ≥0
  negPart≥0 x =
    right≤⊔ (-𝔻 x) 0𝔻

  neg-0𝔻 : -𝔻 0𝔻 ≡ 0𝔻
  neg-0𝔻 =
    inverse-uniqueR 0𝔻 0𝔻 (+-idR 0𝔻)

  posPart-0𝔻 : posPart 0𝔻 ≡ 0𝔻
  posPart-0𝔻 = ⊔-idem 0𝔻

  negPart-0𝔻 : negPart 0𝔻 ≡ 0𝔻
  negPart-0𝔻 =
    cong (λ z → z ⊔ 0𝔻) neg-0𝔻 ∙
    ⊔-idem 0𝔻

  ≥0→posPart≡id :
    (x : DedekindCompletion ℓᴾ) →
    x ≥0 →
    posPart x ≡ x
  ≥0→posPart≡id x 0≤x =
    Lat.≥→∨≡Left {a = x} {b = 0𝔻} 0≤x

  ≥0→negPart≡0 :
    (x : DedekindCompletion ℓᴾ) →
    x ≥0 →
    negPart x ≡ 0𝔻
  ≥0→negPart≡0 x 0≤x =
    Lat.≤→∨≡Right {a = -𝔻 x} -x≤0
    where
    -x≤-0 : (-𝔻 x) ≤ (-𝔻 0𝔻)
    -x≤-0 =
      neg-≤-reverse 0𝔻 x 0≤x

    -0≤0 : (-𝔻 0𝔻) ≤ 0𝔻
    -0≤0 =
      ≡→≤ neg-0𝔻

    -x≤0 : (-𝔻 x) ≤ 0𝔻
    -x≤0 =
      ≤-trans (-𝔻 x) (-𝔻 0𝔻) 0𝔻 -x≤-0 -0≤0

  posPart-mono-≤ :
    (x y : DedekindCompletion ℓᴾ) →
    x ≤ y →
    posPart x ≤ posPart y
  posPart-mono-≤ x y x≤y =
    ⊔≤ x 0𝔻 (posPart y)
      (≤-trans x y (posPart y) x≤y (left≤⊔ y 0𝔻))
      (right≤⊔ y 0𝔻)

  negPart-antitone-≤ :
    (x y : DedekindCompletion ℓᴾ) →
    x ≤ y →
    negPart y ≤ negPart x
  negPart-antitone-≤ x y x≤y =
    ⊔≤ (-𝔻 y) 0𝔻 (negPart x)
      (≤-trans (-𝔻 y) (-𝔻 x) (negPart x)
        (neg-≤-reverse x y x≤y)
        (left≤⊔ (-𝔻 x) 0𝔻))
      (right≤⊔ (-𝔻 x) 0𝔻)

  posProducts : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ
  posProducts x y =
    nnMul (posPart x) (posPart y)
      (posPart≥0 x)
      (posPart≥0 y)
    +𝔻
    nnMul (negPart x) (negPart y)
      (negPart≥0 x)
      (negPart≥0 y)

  negProducts : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ
  negProducts x y =
    nnMul (posPart x) (negPart y)
      (posPart≥0 x)
      (negPart≥0 y)
    +𝔻
    nnMul (negPart x) (posPart y)
      (negPart≥0 x)
      (posPart≥0 y)

  _*𝔻_ : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ
  x *𝔻 y = posProducts x y +𝔻 (-𝔻 negProducts x y)

  infixl 7 _*𝔻_

  posProducts-comm :
    (x y : DedekindCompletion ℓᴾ) →
    posProducts x y ≡ posProducts y x
  posProducts-comm x y =
    cong₂ _+𝔻_
      (nnMul-comm
        (posPart x) (posPart y)
        (posPart≥0 x)
        (posPart≥0 y))
      (nnMul-comm
        (negPart x) (negPart y)
        (negPart≥0 x)
        (negPart≥0 y))

  negProducts-comm :
    (x y : DedekindCompletion ℓᴾ) →
    negProducts x y ≡ negProducts y x
  negProducts-comm x y =
    cong₂ _+𝔻_
      (nnMul-comm
        (posPart x) (negPart y)
        (posPart≥0 x)
        (negPart≥0 y))
      (nnMul-comm
        (negPart x) (posPart y)
        (negPart≥0 x)
        (posPart≥0 y))
    ∙
    +-comm
      (nnMul (negPart y) (posPart x)
        (negPart≥0 y)
        (posPart≥0 x))
      (nnMul (posPart y) (negPart x)
        (posPart≥0 y)
        (negPart≥0 x))

  *𝔻-comm :
    (x y : DedekindCompletion ℓᴾ) →
    x *𝔻 y ≡ y *𝔻 x
  *𝔻-comm x y =
    cong₂ _+𝔻_
      (posProducts-comm x y)
      (cong -𝔻_ (negProducts-comm x y))

  posProducts≥0 :
    (x y : DedekindCompletion ℓᴾ) →
    posProducts x y ≥0
  posProducts≥0 x y =
    +-Pres≥0
      (nnMul (posPart x) (posPart y)
        (posPart≥0 x)
        (posPart≥0 y))
      (nnMul (negPart x) (negPart y)
        (negPart≥0 x)
        (negPart≥0 y))
      (nnMul-Pres≥0
        (posPart x)
        (posPart y)
        (posPart≥0 x)
        (posPart≥0 y))
      (nnMul-Pres≥0
        (negPart x)
        (negPart y)
        (negPart≥0 x)
        (negPart≥0 y))

  negProducts≥0 :
    (x y : DedekindCompletion ℓᴾ) →
    negProducts x y ≥0
  negProducts≥0 x y =
    +-Pres≥0
      (nnMul (posPart x) (negPart y)
        (posPart≥0 x)
        (negPart≥0 y))
      (nnMul (negPart x) (posPart y)
        (negPart≥0 x)
        (posPart≥0 y))
      (nnMul-Pres≥0
        (posPart x)
        (negPart y)
        (posPart≥0 x)
        (negPart≥0 y))
      (nnMul-Pres≥0
        (negPart x)
        (posPart y)
        (negPart≥0 x)
        (posPart≥0 y))

  posProducts≡nnMul :
    (x y : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    posProducts x y ≡ nnMul x y 0≤x 0≤y
  posProducts≡nnMul x y 0≤x 0≤y =
    cong₂ _+𝔻_ main-product zero-product ∙
    +-idR (nnMul x y 0≤x 0≤y)
    where
    main-product :
      nnMul (posPart x) (posPart y)
        (posPart≥0 x)
        (posPart≥0 y)
      ≡ nnMul x y 0≤x 0≤y
    main-product =
      nnMul-cong₂
        (posPart x)
        x
        (posPart y)
        y
        (≥0→posPart≡id x 0≤x)
        (≥0→posPart≡id y 0≤y)
        (posPart≥0 x)
        0≤x
        (posPart≥0 y)
        0≤y

    zero-product :
      nnMul (negPart x) (negPart y)
        (negPart≥0 x)
        (negPart≥0 y)
      ≡ 0𝔻
    zero-product =
      nnMul-cong₂
        (negPart x)
        0𝔻
        (negPart y)
        0𝔻
        (≥0→negPart≡0 x 0≤x)
        (≥0→negPart≡0 y 0≤y)
        (negPart≥0 x)
        0𝔻≥0
        (negPart≥0 y)
        0𝔻≥0
      ∙ nnMul-zeroR 0𝔻 0𝔻≥0

  negProducts≡0 :
    (x y : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    negProducts x y ≡ 0𝔻
  negProducts≡0 x y 0≤x 0≤y =
    cong₂ _+𝔻_ left-zero right-zero ∙
    +-idR 0𝔻
    where
    left-zero :
      nnMul (posPart x) (negPart y)
        (posPart≥0 x)
        (negPart≥0 y)
      ≡ 0𝔻
    left-zero =
      nnMul-cong₂
        (posPart x)
        x
        (negPart y)
        0𝔻
        (≥0→posPart≡id x 0≤x)
        (≥0→negPart≡0 y 0≤y)
        (posPart≥0 x)
        0≤x
        (negPart≥0 y)
        0𝔻≥0
      ∙ nnMul-zeroR x 0≤x

    right-zero :
      nnMul (negPart x) (posPart y)
        (negPart≥0 x)
        (posPart≥0 y)
      ≡ 0𝔻
    right-zero =
      nnMul-cong₂
        (negPart x)
        0𝔻
        (posPart y)
        y
        (≥0→negPart≡0 x 0≤x)
        (≥0→posPart≡id y 0≤y)
        (negPart≥0 x)
        0𝔻≥0
        (posPart≥0 y)
        0≤y
      ∙ nnMul-zeroL y 0≤y

  *𝔻-of-≥0 :
    (x y : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    x *𝔻 y ≡ nnMul x y 0≤x 0≤y
  *𝔻-of-≥0 x y 0≤x 0≤y =
    cong₂ _+𝔻_
      (posProducts≡nnMul x y 0≤x 0≤y)
      (cong -𝔻_ (negProducts≡0 x y 0≤x 0≤y) ∙ neg-0𝔻)
    ∙
    +-idR (nnMul x y 0≤x 0≤y)

  *𝔻-Pres≥0 :
    (x y : DedekindCompletion ℓᴾ) →
    (0≤x : x ≥0) →
    (0≤y : y ≥0) →
    (x *𝔻 y) ≥0
  *𝔻-Pres≥0 x y 0≤x 0≤y =
    ≤-trans
      0𝔻
      (nnMul x y 0≤x 0≤y)
      (x *𝔻 y)
      (nnMul-Pres≥0 x y 0≤x 0≤y)
      (≡→≤ (sym (*𝔻-of-≥0 x y 0≤x 0≤y)))

  rMul≥0 :
    (x z : DedekindCompletion ℓᴾ) →
    z ≥0 →
    DedekindCompletion ℓᴾ
  rMul≥0 x z 0≤z =
    nnMul (posPart x) z
      (posPart≥0 x)
      0≤z
    +𝔻
    (-𝔻 nnMul (negPart x) z
      (negPart≥0 x)
      0≤z)

  posProducts-r≥0 :
    (x z : DedekindCompletion ℓᴾ) →
    (0≤z : z ≥0) →
    posProducts x z ≡
      nnMul (posPart x) z (posPart≥0 x) 0≤z
  posProducts-r≥0 x z 0≤z =
    cong₂ _+𝔻_ first-product second-zero ∙
    +-idR (nnMul (posPart x) z (posPart≥0 x) 0≤z)
    where
    first-product :
      nnMul (posPart x) (posPart z)
        (posPart≥0 x)
        (posPart≥0 z)
      ≡ nnMul (posPart x) z (posPart≥0 x) 0≤z
    first-product =
      nnMul-congR
        (posPart x)
        (posPart z)
        z
        (≥0→posPart≡id z 0≤z)
        (posPart≥0 x)
        (posPart≥0 x)
        (posPart≥0 z)
        0≤z

    second-zero :
      nnMul (negPart x) (negPart z)
        (negPart≥0 x)
        (negPart≥0 z)
      ≡ 0𝔻
    second-zero =
      nnMul-congR
        (negPart x)
        (negPart z)
        0𝔻
        (≥0→negPart≡0 z 0≤z)
        (negPart≥0 x)
        (negPart≥0 x)
        (negPart≥0 z)
        0𝔻≥0
      ∙ nnMul-zeroR (negPart x) (negPart≥0 x)

  negProducts-r≥0 :
    (x z : DedekindCompletion ℓᴾ) →
    (0≤z : z ≥0) →
    negProducts x z ≡
      nnMul (negPart x) z (negPart≥0 x) 0≤z
  negProducts-r≥0 x z 0≤z =
    cong₂ _+𝔻_ first-zero second-product ∙
    +-idL (nnMul (negPart x) z (negPart≥0 x) 0≤z)
    where
    first-zero :
      nnMul (posPart x) (negPart z)
        (posPart≥0 x)
        (negPart≥0 z)
      ≡ 0𝔻
    first-zero =
      nnMul-congR
        (posPart x)
        (negPart z)
        0𝔻
        (≥0→negPart≡0 z 0≤z)
        (posPart≥0 x)
        (posPart≥0 x)
        (negPart≥0 z)
        0𝔻≥0
      ∙ nnMul-zeroR (posPart x) (posPart≥0 x)

    second-product :
      nnMul (negPart x) (posPart z)
        (negPart≥0 x)
        (posPart≥0 z)
      ≡ nnMul (negPart x) z (negPart≥0 x) 0≤z
    second-product =
      nnMul-congR
        (negPart x)
        (posPart z)
        z
        (≥0→posPart≡id z 0≤z)
        (negPart≥0 x)
        (negPart≥0 x)
        (posPart≥0 z)
        0≤z

  *𝔻-r≥0-form :
    (x z : DedekindCompletion ℓᴾ) →
    (0≤z : z ≥0) →
    x *𝔻 z ≡ rMul≥0 x z 0≤z
  *𝔻-r≥0-form x z 0≤z =
    cong₂ _+𝔻_
      (posProducts-r≥0 x z 0≤z)
      (cong -𝔻_ (negProducts-r≥0 x z 0≤z))

  *𝔻-rPosPres≤ :
    (x y z : DedekindCompletion ℓᴾ) →
    x ≤ y →
    (0≤z : z ≥0) →
    x *𝔻 z ≤ y *𝔻 z
  *𝔻-rPosPres≤ x y z x≤y 0≤z =
    ≤-trans (x *𝔻 z) xz-form (y *𝔻 z)
      (≡→≤ (*𝔻-r≥0-form x z 0≤z))
      (≤-trans xz-form yz-form (y *𝔻 z)
        form≤
        (≡→≤ (sym (*𝔻-r≥0-form y z 0≤z))))
    where
    xz-form : DedekindCompletion ℓᴾ
    xz-form = rMul≥0 x z 0≤z

    yz-form : DedekindCompletion ℓᴾ
    yz-form = rMul≥0 y z 0≤z

    pos≤ :
      nnMul (posPart x) z
        (posPart≥0 x)
        0≤z
      ≤
      nnMul (posPart y) z
        (posPart≥0 y)
        0≤z
    pos≤ =
      nnMul-monoL-≤
        (posPart x)
        (posPart y)
        z
        (posPart≥0 x)
        (posPart≥0 y)
        0≤z
        (posPart-mono-≤ x y x≤y)

    neg-prod≤ :
      nnMul (negPart y) z
        (negPart≥0 y)
        0≤z
      ≤
      nnMul (negPart x) z
        (negPart≥0 x)
        0≤z
    neg-prod≤ =
      nnMul-monoL-≤
        (negPart y)
        (negPart x)
        z
        (negPart≥0 y)
        (negPart≥0 x)
        0≤z
        (negPart-antitone-≤ x y x≤y)

    neg≤ :
      (-𝔻 nnMul (negPart x) z
        (negPart≥0 x)
        0≤z)
      ≤
      (-𝔻 nnMul (negPart y) z
        (negPart≥0 y)
        0≤z)
    neg≤ =
      neg-≤-reverse
        (nnMul (negPart y) z
          (negPart≥0 y)
          0≤z)
        (nnMul (negPart x) z
          (negPart≥0 x)
          0≤z)
        neg-prod≤

    form≤ : xz-form ≤ yz-form
    form≤ =
      +-mono-≤
        (nnMul (posPart x) z
          (posPart≥0 x)
          0≤z)
        (nnMul (posPart y) z
          (posPart≥0 y)
          0≤z)
        (-𝔻 nnMul (negPart x) z
          (negPart≥0 x)
          0≤z)
        (-𝔻 nnMul (negPart y) z
          (negPart≥0 y)
          0≤z)
        pos≤
        neg≤

  *𝔻-lPosPres≤ :
    (x y z : DedekindCompletion ℓᴾ) →
    x ≤ y →
    (0≤z : z ≥0) →
    z *𝔻 x ≤ z *𝔻 y
  *𝔻-lPosPres≤ x y z x≤y 0≤z =
    ≤-trans (z *𝔻 x) (x *𝔻 z) (z *𝔻 y)
      (≡→≤ (*𝔻-comm z x))
      (≤-trans (x *𝔻 z) (y *𝔻 z) (z *𝔻 y)
        (*𝔻-rPosPres≤ x y z x≤y 0≤z)
        (≡→≤ (sym (*𝔻-comm z y))))

  posProducts-zeroR :
    (x : DedekindCompletion ℓᴾ) →
    posProducts x 0𝔻 ≡ 0𝔻
  posProducts-zeroR x =
    cong₂ _+𝔻_ first-zero second-zero ∙
    +-idR 0𝔻
    where
    first-zero :
      nnMul (posPart x) (posPart 0𝔻)
        (posPart≥0 x)
        (posPart≥0 0𝔻)
      ≡ 0𝔻
    first-zero =
      nnMul-congR
        (posPart x)
        (posPart 0𝔻)
        0𝔻
        posPart-0𝔻
        (posPart≥0 x)
        (posPart≥0 x)
        (posPart≥0 0𝔻)
        0𝔻≥0
      ∙ nnMul-zeroR (posPart x) (posPart≥0 x)

    second-zero :
      nnMul (negPart x) (negPart 0𝔻)
        (negPart≥0 x)
        (negPart≥0 0𝔻)
      ≡ 0𝔻
    second-zero =
      nnMul-congR
        (negPart x)
        (negPart 0𝔻)
        0𝔻
        negPart-0𝔻
        (negPart≥0 x)
        (negPart≥0 x)
        (negPart≥0 0𝔻)
        0𝔻≥0
      ∙ nnMul-zeroR (negPart x) (negPart≥0 x)

  negProducts-zeroR :
    (x : DedekindCompletion ℓᴾ) →
    negProducts x 0𝔻 ≡ 0𝔻
  negProducts-zeroR x =
    cong₂ _+𝔻_ first-zero second-zero ∙
    +-idR 0𝔻
    where
    first-zero :
      nnMul (posPart x) (negPart 0𝔻)
        (posPart≥0 x)
        (negPart≥0 0𝔻)
      ≡ 0𝔻
    first-zero =
      nnMul-congR
        (posPart x)
        (negPart 0𝔻)
        0𝔻
        negPart-0𝔻
        (posPart≥0 x)
        (posPart≥0 x)
        (negPart≥0 0𝔻)
        0𝔻≥0
      ∙ nnMul-zeroR (posPart x) (posPart≥0 x)

    second-zero :
      nnMul (negPart x) (posPart 0𝔻)
        (negPart≥0 x)
        (posPart≥0 0𝔻)
      ≡ 0𝔻
    second-zero =
      nnMul-congR
        (negPart x)
        (posPart 0𝔻)
        0𝔻
        posPart-0𝔻
        (negPart≥0 x)
        (negPart≥0 x)
        (posPart≥0 0𝔻)
        0𝔻≥0
      ∙ nnMul-zeroR (negPart x) (negPart≥0 x)

  *𝔻-zeroR :
    (x : DedekindCompletion ℓᴾ) →
    x *𝔻 0𝔻 ≡ 0𝔻
  *𝔻-zeroR x =
    cong₂ _+𝔻_
      (posProducts-zeroR x)
      (cong -𝔻_ (negProducts-zeroR x) ∙ neg-0𝔻)
    ∙
    +-idR 0𝔻

  *𝔻-zeroL :
    (x : DedekindCompletion ℓᴾ) →
    0𝔻 *𝔻 x ≡ 0𝔻
  *𝔻-zeroL x =
    *𝔻-comm 0𝔻 x ∙
    *𝔻-zeroR x


module MultiplicationNegation
  (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  baseField : LinearlyOrderedField ℓ ℓ'
  baseField = 𝒜 .fst

  open CompletionBase baseField
  module CutOrder = CompletionOrder baseField
  open CutOrder using (_⊔_)

  open ArithmeticBase 𝒜
  open Addition {ℓᴾ}
  open Negation 𝒜 {ℓᴾ}
  open AdditiveGroup 𝒜 {ℓᴾ}
  open NonNegativeMultiplication 𝒜 {ℓᴾ}
  open Multiplication 𝒜 {ℓᴾ}

  posPart-neg :
    (x : DedekindCompletion ℓᴾ) →
    posPart (-𝔻 x) ≡ negPart x
  posPart-neg x = refl

  negPart-neg :
    (x : DedekindCompletion ℓᴾ) →
    negPart (-𝔻 x) ≡ posPart x
  negPart-neg x =
    cong (λ z → z ⊔ 0𝔻) (neg-involutive x)

  posProducts-negL :
    (x y : DedekindCompletion ℓᴾ) →
    posProducts (-𝔻 x) y ≡ negProducts x y
  posProducts-negL x y =
    cong₂ _+𝔻_ first second ∙
    +-comm
      (nnMul (negPart x) (posPart y)
        (negPart≥0 x)
        (posPart≥0 y))
      (nnMul (posPart x) (negPart y)
        (posPart≥0 x)
        (negPart≥0 y))
    where
    first :
      nnMul (posPart (-𝔻 x)) (posPart y)
        (posPart≥0 (-𝔻 x))
        (posPart≥0 y)
      ≡
      nnMul (negPart x) (posPart y)
        (negPart≥0 x)
        (posPart≥0 y)
    first =
      nnMul-congL
        (posPart (-𝔻 x))
        (negPart x)
        (posPart y)
        (posPart-neg x)
        (posPart≥0 (-𝔻 x))
        (negPart≥0 x)
        (posPart≥0 y)
        (posPart≥0 y)

    second :
      nnMul (negPart (-𝔻 x)) (negPart y)
        (negPart≥0 (-𝔻 x))
        (negPart≥0 y)
      ≡
      nnMul (posPart x) (negPart y)
        (posPart≥0 x)
        (negPart≥0 y)
    second =
      nnMul-congL
        (negPart (-𝔻 x))
        (posPart x)
        (negPart y)
        (negPart-neg x)
        (negPart≥0 (-𝔻 x))
        (posPart≥0 x)
        (negPart≥0 y)
        (negPart≥0 y)

  negProducts-negL :
    (x y : DedekindCompletion ℓᴾ) →
    negProducts (-𝔻 x) y ≡ posProducts x y
  negProducts-negL x y =
    cong₂ _+𝔻_ first second ∙
    +-comm
      (nnMul (negPart x) (negPart y)
        (negPart≥0 x)
        (negPart≥0 y))
      (nnMul (posPart x) (posPart y)
        (posPart≥0 x)
        (posPart≥0 y))
    where
    first :
      nnMul (posPart (-𝔻 x)) (negPart y)
        (posPart≥0 (-𝔻 x))
        (negPart≥0 y)
      ≡
      nnMul (negPart x) (negPart y)
        (negPart≥0 x)
        (negPart≥0 y)
    first =
      nnMul-congL
        (posPart (-𝔻 x))
        (negPart x)
        (negPart y)
        (posPart-neg x)
        (posPart≥0 (-𝔻 x))
        (negPart≥0 x)
        (negPart≥0 y)
        (negPart≥0 y)

    second :
      nnMul (negPart (-𝔻 x)) (posPart y)
        (negPart≥0 (-𝔻 x))
        (posPart≥0 y)
      ≡
      nnMul (posPart x) (posPart y)
        (posPart≥0 x)
        (posPart≥0 y)
    second =
      nnMul-congL
        (negPart (-𝔻 x))
        (posPart x)
        (posPart y)
        (negPart-neg x)
        (negPart≥0 (-𝔻 x))
        (posPart≥0 x)
        (posPart≥0 y)
        (posPart≥0 y)

  *𝔻-negL :
    (x y : DedekindCompletion ℓᴾ) →
    (-𝔻 x) *𝔻 y ≡ -𝔻 (x *𝔻 y)
  *𝔻-negL x y =
    cong₂ _+𝔻_
      (posProducts-negL x y)
      (cong -𝔻_ (negProducts-negL x y)) ∙
    sym (neg-difference-swap (posProducts x y) (negProducts x y))

  *𝔻-negR :
    (x y : DedekindCompletion ℓᴾ) →
    x *𝔻 (-𝔻 y) ≡ -𝔻 (x *𝔻 y)
  *𝔻-negR x y =
    *𝔻-comm x (-𝔻 y) ∙
    *𝔻-negL y x ∙
    cong -𝔻_ (*𝔻-comm y x)

  *𝔻-negL-negR :
    (x y : DedekindCompletion ℓᴾ) →
    (-𝔻 x) *𝔻 (-𝔻 y) ≡ x *𝔻 y
  *𝔻-negL-negR x y =
    *𝔻-negL x (-𝔻 y) ∙
    cong -𝔻_ (*𝔻-negR x y) ∙
    neg-involutive (x *𝔻 y)
