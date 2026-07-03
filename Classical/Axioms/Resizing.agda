{-

Voevodsky's Axiom of Propositional Resizing

Notice that Resizing is a corollary of Excluded Middle,
of which proof can be found in `Classical.Axiom.ExcludedMiddle`.

-}
{-# OPTIONS --safe #-}
module Classical.Axioms.Resizing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence

private
  variable
    ℓ ℓ' : Level


-- Construct dependent path of isProp

pathIsProp :
  (p : I → Type ℓ)(p0 : isProp (p i0))(p1 : isProp (p i1)) → PathP (λ i → isProp (p i)) p0 p1
pathIsProp p p0 p1 = isProp→PathP (λ i → isPropIsProp {A = p i}) p0 p1


-- Formulation of Propositional Resizing

-- Lifting h-propositions to higher universe level
liftProp : (ℓ' : Level) → hProp ℓ → hProp (ℓ-max ℓ ℓ')
liftProp ℓ' P .fst = Lift ℓ' (P .fst)
liftProp ℓ' P .snd = isOfHLevelLift 1 (P .snd)

Resizing : Typeω
Resizing = {ℓ ℓ' : Level} → isEquiv (liftProp {ℓ = ℓ} ℓ')


-- A simplified version that only lifting from level zero is required

Resizing₀ : Typeω
Resizing₀ = {ℓ : Level} → isEquiv (liftProp {ℓ = ℓ-zero} ℓ)

Resizing→Resizing₀ : Resizing → Resizing₀
Resizing→Resizing₀ resizing = resizing

-- The simplified implies the full version.
Resizing₀→Resizing : Resizing₀ → Resizing
Resizing₀→Resizing resizing₀ {ℓ = ℓ} {ℓ' = ℓ'} =
  isEquiv[f∘equivFunA≃B]→isEquiv[f] _ (_ , resizing₀) (subst isEquiv (sym liftComp) resizing₀)
  where
  liftCompPath : (P : hProp ℓ-zero) → liftProp ℓ' (liftProp ℓ P) .fst ≡ liftProp (ℓ-max ℓ ℓ') P .fst
  liftCompPath P = ua (compEquiv (invEquiv (compEquiv LiftEquiv LiftEquiv)) LiftEquiv)

  liftComp : liftProp ℓ' ∘ liftProp ℓ ≡ liftProp (ℓ-max ℓ ℓ')
  liftComp i P .fst = liftCompPath P i
  liftComp i P .snd =
    pathIsProp (λ i → liftComp i P .fst)
    (liftProp ℓ' (liftProp ℓ P) .snd) (liftProp (ℓ-max ℓ ℓ') P .snd) i


-- Another formulation of Resizing by providing explicit inverse of universe lifting

record DropProp (P : hProp ℓ) : Type (ℓ-suc ℓ) where
  field
    lower : hProp ℓ-zero
    dropEquiv : P .fst ≃ lower .fst

open DropProp

Drop : Typeω
Drop = {ℓ : Level} → (P : hProp ℓ) → DropProp P


-- The equivalence between Resizing and Drop

Resizing→Drop : Resizing → Drop
Resizing→Drop resizing P .lower = invIsEq resizing P
Resizing→Drop resizing P .dropEquiv =
  compEquiv (pathToEquiv (λ i → secIsEq resizing P (~ i) .fst)) (invEquiv LiftEquiv)

module _
  {drop : Drop}{ℓ : Level} where

  liftp : hProp ℓ-zero → hProp ℓ
  liftp = liftProp {ℓ = ℓ-zero} ℓ

  resize : hProp ℓ → hProp ℓ-zero
  resize P = drop P .lower

  liftp-resize : (P : hProp _) → liftp (resize P) ≡ P
  liftp-resize P i .fst = ua (compEquiv (invEquiv LiftEquiv) (invEquiv (drop P .dropEquiv))) i
  liftp-resize P i .snd = pathIsProp (λ i → liftp-resize P i .fst) (liftp (resize P) .snd) (P .snd) i

  resize-liftp : (P : hProp _) → resize (liftp P) ≡ P
  resize-liftp P i .fst = ua (compEquiv (invEquiv (drop (liftp P) .dropEquiv)) (invEquiv LiftEquiv)) i
  resize-liftp P i .snd = pathIsProp (λ i → resize-liftp P i .fst) (resize (liftp P) .snd) (P .snd) i

  isEquiv-resize : isEquiv liftp
  isEquiv-resize = isoToEquiv (iso liftp resize liftp-resize resize-liftp) .snd

Drop→Resizing₀ : Drop → Resizing₀
Drop→Resizing₀ drop = isEquiv-resize {drop = drop}

Drop→Resizing : Drop → Resizing
Drop→Resizing drop = Resizing₀→Resizing (Drop→Resizing₀ drop)


{-

  Subobject Classifier

-}

-- A (pre-)formulation of subobject classifier

-- Warning: This is not a complete formulation.
-- The object Ω should be a `Heyting algebra` and all equivalences should respect this.
-- (hProp automatically admit that by considering usual logical operations on propositions)
-- Moreover, the equivalences should commute with universe level lifting.

isSubobjectClassifier : Type ℓ → Typeω
isSubobjectClassifier Ω = {ℓ : Level}{X : Type ℓ} → (X → Ω) ≃ (X → hProp ℓ)

getSubobjectClassifier :
  {ℓ : Level}{Prop : Type ℓ} → ({ℓ : Level} → Prop ≃ hProp ℓ) → isSubobjectClassifier Prop
getSubobjectClassifier Prop≃hProp = equiv→ (idEquiv _) Prop≃hProp


-- Propositional Resizing implies the Existence of Subobject Classifier
-- In particular, it is the type hProp of base level.

Resizing→∃SubobjectClassifier : Resizing → isSubobjectClassifier (hProp ℓ-zero)
Resizing→∃SubobjectClassifier resizing = getSubobjectClassifier (_ , resizing)
