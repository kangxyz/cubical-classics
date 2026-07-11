{-

Algebraic and ordered-field structures for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.CauchyReals.Arithmetic.Structures where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Relation.Binary.Order.Pseudolattice

open import Constructive.Algebra.OrderedHeytingField.Base
  using (IsHeytingFieldOnOrderedCommRing; OrderedHeytingField)
import Constructive.Algebra.OrderedCommRing.Properties as OrderedProperties

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.MultiplicationOrder
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Inverse
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Lattice
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Properties
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.CauchyReals.Order.Tightness
open import Constructive.Analysis.Reals.CauchyReals.Order.WeakLinear
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace


CauchyRealsCommRing : CommRing ℓ-zero
CauchyRealsCommRing =
  makeCommRing 0ᶜ 1ᶜ _+ᶜ_ _·ᶜ_ -ᶜ_
    isSetCompletion
    add-assoc
    add-zero-right
    add-inverse-right
    add-comm
    mulᶜ-assoc
    mulᶜ-one-right
    mulᶜ-distrib-right
    mulᶜ-comm


module CauchyRealsCommRingTheory =
  CommRingTheory CauchyRealsCommRing


CauchyRealsIsOrderedCommRing :
  IsOrderedCommRing 0ᶜ 1ᶜ _+ᶜ_ _·ᶜ_ -ᶜ_ _<ᶜ_ _≤ᶜ_
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.isCommRing =
  CauchyRealsCommRing .snd .CommRingStr.isCommRing
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.isPseudolattice =
  CauchyReals≤Pseudolattice .snd .PseudolatticeStr.is-pseudolattice
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.isStrictOrder =
  CauchyReals<StrictOrder
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.<-≤-weaken =
  λ x y → <ᶜ→≤ᶜ {x = x} {y = y}
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.≤≃¬> =
  ≤ᶜ≃¬>ᶜ
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.+MonoR≤ =
  λ x y z → addᶜ-pres≤ᶜ-right {x = x} {y = y} z
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.+MonoR< =
  λ x y z → addᶜ-pres<ᶜ-right {x = x} {y = y} z
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.posSum→pos∨pos =
  positive-sum-splitᶜ
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.<-≤-trans =
  <ᶜ-≤ᶜ-trans
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.≤-<-trans =
  ≤ᶜ-<ᶜ-trans
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.·MonoR≤ =
  mulᶜ-pres≤ᶜ-right
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.·MonoR< =
  mulᶜ-pres<ᶜ-right
CauchyRealsIsOrderedCommRing .IsOrderedCommRing.0<1 =
  0ᶜ<1ᶜ


CauchyRealsOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
CauchyRealsOrderedCommRing .fst =
  ℝᶜ
CauchyRealsOrderedCommRing .snd =
  orderedcommringstr
    0ᶜ
    1ᶜ
    _+ᶜ_
    _·ᶜ_
    -ᶜ_
    _<ᶜ_
    _≤ᶜ_
    CauchyRealsIsOrderedCommRing


module CauchyRealsOrdered =
  OrderedProperties.OrderedCommRingTheory CauchyRealsOrderedCommRing


CauchyRealsIsHeytingFieldOnOrderedCommRing-from-positive :
  PositiveRightInverseProviderᶜ →
  IsHeytingFieldOnOrderedCommRing CauchyRealsOrderedCommRing
CauchyRealsIsHeytingFieldOnOrderedCommRing-from-positive inv₊
  .IsHeytingFieldOnOrderedCommRing.inv# =
    inv#ᶜ-from-positive inv₊


CauchyRealsOrderedHeytingField-from-positive :
  PositiveRightInverseProviderᶜ →
  OrderedHeytingField ℓ-zero ℓ-zero
CauchyRealsOrderedHeytingField-from-positive inv₊ =
  CauchyRealsOrderedCommRing ,
  CauchyRealsIsHeytingFieldOnOrderedCommRing-from-positive inv₊


CauchyRealsIsHeytingFieldOnOrderedCommRing :
  IsHeytingFieldOnOrderedCommRing CauchyRealsOrderedCommRing
CauchyRealsIsHeytingFieldOnOrderedCommRing =
  CauchyRealsIsHeytingFieldOnOrderedCommRing-from-positive
    positive-right-inverseᶜ


CauchyRealsOrderedHeytingField :
  OrderedHeytingField ℓ-zero ℓ-zero
CauchyRealsOrderedHeytingField =
  CauchyRealsOrderedHeytingField-from-positive positive-right-inverseᶜ
