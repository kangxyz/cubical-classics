# HoTT Cauchy Reals Ordered Heyting Field Plan

This plan tracks the work needed to prove that the HoTT-style Cauchy reals form
an ordered Heyting field in this repository's interfaces.

The target theorem is:

```agda
CauchyRealsOrderedHeytingField :
  OrderedHeytingField ℓ-zero ℓ-zero
```

Equivalently, we first build an `OrderedCommRing` structure on the HoTT Cauchy
reals, then prove that every element apart from zero in the order-induced
apartness relation has a multiplicative inverse.

## Ground Rules

- Follow the HoTT Book construction of the Cauchy reals as a higher
  inductive-inductive type with a rational-indexed closeness relation.
- Do not use a quotient of rational Cauchy approximations as the main real
  type.
- Prefer extension and uniqueness principles over direct induction on reals
  for algebraic laws.
- Keep the implementation compatible with the local
  `OrderedCommRing` and `OrderedHeytingField` interfaces.
- Type-check each module as it is introduced, and type-check the aggregate
  `Constructive.CauchyReals` module after each phase.

## Phase 0: Definition Layer

Goal: make the base HIIT definition stable and aligned with the HoTT Book.

Modules:

```text
Constructive/CauchyReals/Base.agda
Constructive/CauchyReals/PositiveRationals.agda
Constructive/CauchyReals/RationalCloseness.agda
```

Tasks:

- Factor positive rational precision infrastructure out of `Base`.
- Define `Q+`, precision addition, precision subtraction, and positivity
  transport lemmas.
- Keep the real constructors aligned with the HoTT Book:
  `rational`, `limit`, and `path`.
- Keep closeness constructors aligned by shape:
  rational-rational, rational-limit, limit-rational, and limit-limit.
- Do not add set-truncation as a constructor for the real type. Prove
  `isSet` later from separatedness and reflexive closeness.

Exit criteria:

```sh
agda Constructive/CauchyReals/Base.agda
agda Constructive/CauchyReals.agda
git diff --check
```

## Phase 1: Induction And Recursion

Goal: expose usable eliminators so later modules do not depend directly on the
raw HIIT eliminator.

Modules:

```text
Constructive/CauchyReals/Definitions.agda
Constructive/CauchyReals/Induction.agda
Constructive/CauchyReals/Recursion.agda
```

Tasks:

- Define Cauchy approximation predicates and dependent Cauchy approximation
  predicates.
- Package the general induction principle for the real type and closeness
  relation.
- Provide specializations:
  `R`-induction, closeness-induction, proposition-valued induction, and binary
  proposition-valued induction.
- Define the enhanced recursion principle with a target closeness-like
  relation.

Exit criteria:

- Basic functions out of the reals can be defined through the packaged
  recursion principle.
- Proposition-valued proofs avoid manual path-constructor obligations where
  the target is a proposition.

## Phase 2: Closeness Theory

Goal: establish the metric-like behavior of the indexed closeness relation.

Modules:

```text
Constructive/CauchyReals/Closeness/ReflexiveSymmetric.agda
Constructive/CauchyReals/Closeness/Rounded.agda
Constructive/CauchyReals/Closeness/Properties.agda
```

Tasks:

- Prove reflexivity of closeness.
- Prove symmetry of closeness.
- Prove that the real type is a set.
- Prove roundedness of the inductive closeness relation.
- Build the computed closeness relation used to analyze closeness hypotheses.
- Prove equivalence between inductive closeness and computed closeness.
- Derive roundedness, monotonicity, and triangle inequality.
- Add reusable limit/closeness interaction helpers.

Exit criteria:

- Available lemmas include:
  `close-refl`, `close-sym`, `close-rounded`, `close-mono`,
  `close-triangle`, and `isSetR`.
- Later extension proofs can use closeness hypotheses without directly
  recursing through closeness constructors.

## Phase 3: Extension Principles

Goal: make continuous construction on reals reusable.

Modules:

```text
Constructive/CauchyReals/Lipschitz/Base.agda
Constructive/CauchyReals/Lipschitz/Closed.agda
Constructive/CauchyReals/Nonexpanding.agda
Constructive/CauchyReals/Continuity.agda
Constructive/CauchyReals/Extension/Properties.agda
```

Tasks:

- Define Lipschitz, non-expanding, and continuous maps in terms of closeness.
- Prove unary Lipschitz extension from rationals to reals.
- Prove binary non-expanding extension.
- Optionally prove closed-interval Lipschitz extension if needed for later
  reciprocal work.
- Prove uniqueness of continuous extensions.
- Provide unary, binary, and ternary extension-law helpers.

Exit criteria:

- Negation, addition, min, max, and scalar multiplication can be defined by
  extension rather than raw HIIT recursion.
- Algebraic identities can be transferred from rationals using extension
  uniqueness.

## Phase 4: Additive And Lattice Structure

Goal: define the low-risk operations and their laws first.

Modules:

```text
Constructive/CauchyReals/Arithmetic/Negation.agda
Constructive/CauchyReals/Arithmetic/Addition.agda
Constructive/CauchyReals/Arithmetic/Lattice.agda
Constructive/CauchyReals/Arithmetic/AdditiveGroup.agda
```

Tasks:

- Define `0R` as `rational 0`.
- Define negation by Lipschitz extension of rational negation.
- Define addition by binary non-expanding extension of rational addition.
- Define `min` and `max` by non-expanding extension.
- Prove rational computation rules for each operation.
- Transfer additive group laws from rationals.
- Transfer lattice laws for `min` and `max`.

Exit criteria:

- There is an abelian group structure on the HoTT Cauchy reals.
- `min` and `max` are available for non-strict order.

## Phase 5: Order

Goal: build the order structure required by `OrderedCommRing`.

Modules:

```text
Constructive/CauchyReals/Order/Base.agda
Constructive/CauchyReals/Order/Magnitude.agda
Constructive/CauchyReals/Order/Distance.agda
Constructive/CauchyReals/Order/Properties.agda
```

Tasks:

- Define non-strict order, preferably through the lattice structure.
- Define strict order following the HoTT Book and Gilbert-style
  rational-separation presentation.
- Prove proposition-valuedness of `<` and `<=`.
- Prove poset laws and pseudolattice laws.
- Prove `<` is a strict order.
- Prove weak linearity for `<`.
- Prove addition preserves and reflects both `<` and `<=`.
- Establish Gilbert's alternative characterization of strict order.
- Define absolute value and distance, and prove their basic order properties.

Exit criteria:

- The real type has the order data needed by the local `OrderedCommRing`
  interface except multiplication compatibility.
- Apartness `x # y = (x < y) ⊎ (y < x)` is usable.

## Phase 6: Multiplication And Commutative Ring

Goal: define global multiplication and prove commutative ring laws.

Modules:

```text
Constructive/CauchyReals/Arithmetic/ScalarMultiplication.agda
Constructive/CauchyReals/Arithmetic/BoundedMultiplication.agda
Constructive/CauchyReals/Arithmetic/Multiplication.agda
Constructive/CauchyReals/Arithmetic/CommRing.agda
```

Tasks:

- Define rational scalar multiplication by Lipschitz extension.
- Prove fixed rational multiplication is Lipschitz.
- Define bounded multiplication for reals with a rational bound.
- Prove every real merely has a rational bound.
- Prove bounded multiplication is independent of the chosen bound.
- Use elimination from propositional truncation into a set to define global
  multiplication.
- Prove rational computation rules for multiplication.
- Transfer associativity, commutativity, unit laws, distributivity, and zero
  laws from rationals using extension uniqueness.

Exit criteria:

```agda
CauchyRealsCommRing : CommRing ℓ-zero
```

or the local equivalent needed to build:

```agda
CauchyRealsOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
```

## Phase 7: Ordered Commutative Ring

Goal: finish the ordered-ring compatibility proofs.

Modules:

```text
Constructive/CauchyReals/Arithmetic/OrderedCommRing.agda
```

Tasks:

- Prove `0 < 1`.
- Prove `<` weakens to `<=`.
- Prove `<=` corresponds to negated reverse strict order if required by the
  local interface.
- Prove positive-sum reflection:
  if `0 < x + y`, then merely `0 < x` or `0 < y`.
- Prove multiplication by a nonnegative real preserves `<=`.
- Prove multiplication by a positive real preserves `<`.
- Package the local `IsOrderedCommRing`.

Exit criteria:

```agda
CauchyRealsOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
```

## Phase 8: Reciprocal And Ordered Heyting Field

Goal: construct inverses from order-induced apartness.

Modules:

```text
Constructive/CauchyReals/Arithmetic/BoundedReciprocal.agda
Constructive/CauchyReals/Arithmetic/Inverse.agda
Constructive/CauchyReals/Arithmetic/OrderedHeytingField.agda
```

Tasks:

- Define reciprocal on positive reals bounded away from zero.
- Prove the local reciprocal is continuous or Lipschitz on suitable bounded
  domains.
- Prove local reciprocal laws.
- Show the construction is independent of chosen local bounds.
- Define reciprocal for `0 < x`.
- Define reciprocal for `x < 0` using negation and the positive case.
- Case split on `x # 0` to define:

```agda
inv# : (x : R) -> x # 0R -> Sigma R (lambda y -> x * y == 1R)
```

- Package:

```agda
CauchyRealsIsHeytingFieldOnOrderedCommRing :
  IsHeytingFieldOnOrderedCommRing CauchyRealsOrderedCommRing

CauchyRealsOrderedHeytingField :
  OrderedHeytingField ℓ-zero ℓ-zero
```

Exit criteria:

- The final ordered Heyting field instance type-checks.
- The inverse proof uses apartness from strict order, not inequality from
  decidable equality.

## Phase 9: Aggregates And README

Goal: expose the completed development coherently.

Modules:

```text
Constructive/CauchyReals.agda
Constructive/CauchyReals/Arithmetic.agda
Constructive/CauchyReals/Order.agda
```

Tasks:

- Add aggregate modules for public imports.
- Re-export the final `OrderedHeytingField` instance.
- Update `README.md` to describe the completed structure.
- Keep public names stable and aligned with the local Dedekind-real naming
  style where possible.

## Verification Checklist

Run narrow checks after every edited module:

```sh
agda Constructive/CauchyReals/<module>.agda
```

Run aggregate checks after every phase:

```sh
agda Constructive/CauchyReals.agda
```

Run whitespace checks before reporting completion:

```sh
git diff --check
```

For interface-level changes, also check the nearest dependents:

```sh
agda Constructive/Algebra/OrderedHeytingField.agda
agda Constructive/Algebra/OrderedCommRing.agda
```

## Risk Register

- The alternative closeness proof is likely the largest foundational proof.
- Multiplication is not globally Lipschitz, so bounded/local construction is
  required.
- Reciprocal needs careful management of away-from-zero evidence and local
  bounds.
- Propositional truncation can only be eliminated into sets; `isSetR` must be
  available before local-to-global multiplication and reciprocal.
- The final packaging may differ from Brough's ordered-field interface and
  must be adapted to this repository's `OrderedHeytingField`.

## Suggested Milestones

1. Definition layer and aggregate type-check.
2. Induction and recursion APIs.
3. Closeness reflexivity, symmetry, roundedness, triangle inequality, and
   `isSetR`.
4. Lipschitz and non-expanding extension principles.
5. Additive group and lattice structure.
6. Order structure up to addition compatibility.
7. Multiplication and commutative ring.
8. Ordered commutative ring.
9. Reciprocal and ordered Heyting field.
