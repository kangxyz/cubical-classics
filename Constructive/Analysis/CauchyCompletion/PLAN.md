# Cauchy Completion Migration Plan

This plan moves Cauchy completion ownership from
`Constructive.CauchyReals` into `Constructive.Analysis.CauchyCompletion`.
Preserving the old Cauchy-real API is not a goal.  The old modules may be
rewritten to use the new names directly once the generic completion stack is
ready.

## Target Shape

- `Constructive.Analysis.CauchyCompletion.Base`
  defines the generic completion HIIT for a `MetricSpace`.
- `Constructive.Analysis.CauchyCompletion.Closeness`
  proves the generic closeness laws for the completion.
- `Constructive.Analysis.CauchyCompletion.Recursion`
  exposes the generic recursion principle into separated metric targets.
- `Constructive.Analysis.CauchyCompletion.Extension`
  aggregates the extension submodules.  The core universal properties live in
  `Extension.Core`, and binary nonexpanding completion extensions live in
  `Extension.BinaryNonexpanding`.
- `Constructive.Analysis.CauchyCompletion.Complete`
  packages the completion as a `MetricSpace` and proves it complete.
- `Constructive.Analysis.CauchyCompletion`
  is the public aggregate for the completion API.
- `Constructive.Analysis.Metric.Cauchy`
  owns generic Cauchy approximations, convergence, and completeness, so the
  completion modules do not depend on Cauchy-real specializations.
- `Constructive.Analysis.Metric.Map`
  owns continuity interfaces, including regular precision moduli and the
  completion precision-modulus split structure used to extend uniformly
  continuous maps.
- `Constructive.CauchyReals.Base`
  becomes a thin specialization of the generic completion at
  `RationalsMetricSpace`, without compatibility aliases unless they are needed
  locally during migration.

## Invariants

- The metric interface remains precision-indexed by `ℚ⁺`; no real-valued
  distance function is introduced.
- The generic completion depends only on `MetricSpace` structure, not on
  rational arithmetic except through the precision algebra.
- Rational-specific arithmetic and order stay in `Constructive.CauchyReals`
  or later rational-real modules; only completion machinery moves under
  `Analysis`.
- New generic proofs should be parameterized before adding Cauchy-real
  special cases.
- If an old Cauchy-real proof only uses completion structure, migrate it to
  `Analysis.CauchyCompletion`; if it uses ordered-field structure of `ℚ`, keep
  it outside the generic completion layer.

## Phase 1: Move The Generic Base

1. Move the current generic HIIT from
   `Constructive.Analysis.Metric.Completion` to
   `Constructive.Analysis.CauchyCompletion.Base`.
2. Export `CauchyCompletion`, `point`, `limit`, `path`,
   `CauchyApproximation`, and `_∼[_]_` from the new aggregate.
3. Update `Constructive.CauchyReals.Base` to specialize the new module at
   `RationalsMetricSpace`.
4. Remove `Constructive.Analysis.Metric.Completion` once all imports are
   migrated.

Acceptance checks:
- `agda Constructive/Analysis/CauchyCompletion/Base.agda`
- `agda Constructive/CauchyReals/Base.agda`

## Phase 2: Generic Closeness Laws

1. Port the structure of `CauchyReals.Closeness.ReflexiveSymmetric` to the
   generic completion.
2. Port roundedness from `CauchyReals.Closeness.Rounded`.
3. Port the internal computed/prelength proof machinery only as far as needed
   for:
   - `close-refl`
   - `close-sym`
   - `close-mono`
   - `close-triangle`
   - `close-rounded`
   - `close-separated`
   - `isSet` for the completion
4. Package these proofs in
   `Constructive.Analysis.CauchyCompletion.Closeness`.

Acceptance checks:
- `agda Constructive/Analysis/CauchyCompletion/Closeness.agda`
- `agda Constructive/CauchyReals/Closeness.agda` after specialization updates

## Phase 3: Metric-Space Instance And Completeness

1. Define
   `CauchyCompletionMetricSpace : MetricSpace _ _`
   for any input `MetricSpace`.
2. Prove `point` is nonexpanding.
3. Prove the stronger embedding statement needed by downstream code:
   point-level closeness in the completion is equivalent to base closeness,
   or at least the direction required by existing arithmetic/order proofs.
4. Prove `IsComplete CauchyCompletionMetricSpace`.
5. Replace `CauchyRealsIsComplete` with the rational instance of the generic
   completeness theorem.

Acceptance checks:
- `agda Constructive/Analysis/CauchyCompletion/Complete.agda`
- `agda Constructive/Analysis/Metric/Complete.agda`

## Phase 4: Recursion And Extension

1. Generalize `CauchyReals.Recursion` to recursion from a completion into a
   separated metric target.
2. Generalize the extension kit from `CauchyReals.Extension`.
3. Prove nonexpanding extension into complete metric spaces first.
4. Add a regular precision-modulus interface and the induced action on Cauchy
   approximations.  This supplies the first split law needed by uniformly
   continuous extension proofs.
5. Keep scaled-Lipschitz extension as the concrete algebraic universal property
   for linear precision changes, sharing the generic recursion infrastructure
   with the nonexpanding and split-modulus uniformly continuous extensions.
6. State and prove the full universal property for uniformly continuous maps
   whose modulus includes the remaining point-limit and limit-limit precision
   splits.

Acceptance checks:
- `agda Constructive/Analysis/CauchyCompletion/Recursion.agda`
- `agda Constructive/Analysis/CauchyCompletion/Extension.agda`

## Phase 5: Cauchy Reals Specialization

1. Rewrite `Constructive.CauchyReals.Base` to use the new generic names
   directly.
2. Update Cauchy-real modules to import generic completion facts rather than
   local copies.
3. Keep rational arithmetic and order proofs specialized, but rebuild their
   extension arguments through the generic universal property.
4. Delete duplicated Cauchy-real-specific completion proofs after their generic
   replacements type-check.

Acceptance checks:
- `agda Constructive/CauchyReals.agda`
- `agda Constructive/Analysis/CauchyCompletion.agda`

## Phase 6: Cleanup

1. Remove temporary shims and compatibility aliases.
2. Update `README.md` and aggregate modules to make
   `Constructive.Analysis.CauchyCompletion` the canonical completion API.
3. Run whitespace and diff checks.
4. Run broader Agda checks for all touched aggregates.

Acceptance checks:
- `git diff --check`
- trailing-whitespace search over touched files
- aggregate module checks for `Constructive.Analysis.*` and
  `Constructive.CauchyReals`
