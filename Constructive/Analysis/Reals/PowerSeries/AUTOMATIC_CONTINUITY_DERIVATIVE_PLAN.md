# Power Series Automatic Continuity And Derivative Plan

This plan is independent of `Constructive/Analysis/Reals/PowerSeries/PLAN.md`.
It targets the remaining theorem work needed to derive continuity, uniform
continuity on closed subballs, and termwise derivative conclusions
automatically from existing power-series data.

Here, "automatic" means that downstream proofs should provide expansion data,
subball or margin data, and coefficient identities when the derivative series is
known by a named instance. They should no longer manually assemble partial-sum
uniform-continuity witnesses, derivative-radius witnesses, iterated derivative
bounds, or `PowerSeriesPartialSumsDerivativeModulusLarge` records.

## Literature And Implementation Basis

- Mathlib's analytic API separates formal series from the statement that a
  function has that series on a ball. Its public consequences include automatic
  continuity from `HasFPowerSeriesOnBall`, `HasFPowerSeriesAt`, and
  `AnalyticAt`:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/Basic.html
- Mathlib's composition API is a useful warning about scope. The mature API
  supports `HasFPowerSeriesAt.comp` and `AnalyticAt.comp`, but the implementation
  cost is mostly coefficient reindexing and summability bookkeeping:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/Composition.html
- Russell O'Connor's exact real work in Coq shows the constructive pattern:
  elementary functions should be built from complete metric spaces and explicit
  correctness data rather than from classical convergence shortcuts:
  https://arxiv.org/abs/0805.2438
- Krebbers and Spitters confirm that constructive exact-real power-series work
  scales when moduli, approximants, and approximate division are first-class:
  https://arxiv.org/abs/1105.2751
- CoRN is the mature constructive real-analysis reference. Its library includes
  continuity, differentiability, Taylor's theorem, exact computation, and
  elementary functions:
  https://github.com/rocq-community/corn
- Arb is not a proof-assistant library, but it is a mature implementation
  reference for later performance work: Taylor series, argument reduction,
  rectangular splitting, and rigorous error bounds:
  https://arxiv.org/abs/1410.7176

The design lesson is stable across these references: keep theorem-level
conclusions public, keep moduli and error estimates explicit internally, and do
not mix correctness automation with optimized evaluation algorithms.

## External Model Mapping

Use the external references as design constraints, not as code to copy.

- Mathlib exposes consequences at the `HasFPowerSeriesOnBall`,
  `HasFPowerSeriesAt`, and `AnalyticAt` layers. The local analogue should expose
  consequences from `HasPowerSeriesOnBallWith`, `HasPowerSeriesAtWith`, and the
  analytic existential wrappers only after the lower-level theorem has checked.
- Mathlib includes `HasFPowerSeriesOnBall.continuousOn`,
  `HasFPowerSeriesAt.continuousAt`, and locally uniform convergence of partial
  sums. The constructive local analogue is not topological openness; it is a
  closed-subball theorem with explicit positive-rational moduli.
- Mathlib composition is a mature API, but it is intentionally out of scope
  here. Composition requires coefficient reindexing and summability
  bookkeeping that should not block continuity and derivative automation.
- O'Connor, Krebbers-Spitters, and CoRN all support the same constructive
  engineering rule: make moduli, approximants, and convergence witnesses
  first-class rather than hiding them behind classical existence.
- Arb is only a later performance reference. Its Taylor and ball-arithmetic
  algorithms should not determine the public proof API until the correctness
  theorems are stable.

## Current Implementation Progress

Implemented theorem-level bridges:

- `hasPowerSeriesAtWith→uniformlyContinuousOnBallFromPartialSumsWith`
- `hasPowerSeriesAtWith→uniformlyContinuousOnBallFromPartialSums`
- `hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromPartialSumsWith`
- `hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromPartialSums`
- `hasPowerSeriesAtWith→continuousAtFromPartialSumsWith`
- `hasPowerSeriesAtWith→continuousAtFromPartialSums`
- `hasPowerSeriesWithinAtWith→continuousAtFromPartialSumsWith`
- `hasPowerSeriesWithinAtWith→continuousAtFromPartialSums`
- `powerSeriesPartialSumsUniformlyContinuousOnBallFromPartialSumModuliWith`
- `powerSeriesPartialSumsUniformlyContinuousOnBallFromPartialSumModuli`
- `centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith`
- `centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith`

These remove two pieces of repeated downstream proof plumbing: manually
threading centered sum continuity through analytic expansions, and manually
deriving derivative-radius data from a coefficient path plus target radius data.
The formal derivative bridge also specializes the termwise derivative theorem
to `derivativePowerSeries a` without passing a reflexive coefficient path or
duplicate target radius data.

The partial-sum modulus bridge is intentionally modest. It converts a family of
finite partial-sum moduli into the existing sum-level continuity criterion. It
does not yet prove the finite polynomial moduli themselves.

Updated downstream users:

- `expᶜHasDerivativeAtWithFromIteratedBoundsOnSubball`
- `sinᶜHasDerivativeAtWithFromIteratedBoundsOnSubball`
- `cosᶜHasDerivativeAtWithFromIteratedBoundsOnSubball`

Remaining hard gaps:

- automatically constructing partial-sum uniform-continuity witnesses;
- proving generic derivative-series convergence on strict subballs;
- constructing canonical iterated derivative bounds and derivative-modulus
  largeness data from convergence or majorant data;
- replacing elementary instance derivative proofs with the new high-level
  theorem stack.

## Current Local Basis

The following local modules are already the foundation for this work:

- `Constructive.Analysis.Reals.PowerSeries.Base` defines power-series terms,
  partial sums, closed-ball convergence data, and sums.
- `Constructive.Analysis.Reals.PowerSeries.Radius` packages local radius data
  by closed subballs rather than by a classical exact radius.
- `Constructive.Analysis.Reals.PowerSeries.Continuity` already proves
  continuity and uniform continuity criteria from partial-sum continuity.
- `Constructive.Analysis.Reals.PowerSeries.Analytic.Continuity` defines
  function-level continuity and uniform-continuity conclusions for
  `HasPowerSeriesAt`.
- `Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences` bridges
  expansion data and centered sum continuity to function-level conclusions.
- `Constructive.Analysis.Reals.PowerSeries.Differentiation` defines the formal
  derivative series.
- `Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence` currently
  transports derivative convergence through coefficient paths. It does not yet
  prove generic convergence of the formal derivative from radius data of the
  original series.
- `Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Theorem` contains
  the hard termwise derivative criterion, but callers still need to provide too
  much proof plumbing.
- `Constructive.Analysis.Reals.PowerSeries.Majorant` and
  `Constructive.Analysis.Reals.PowerSeries.Instances.Geometric` provide the
  majorant and geometric-tail infrastructure needed for generic automation.

## Target Theorems

The public target is a small theorem-first API:

- `hasPowerSeriesOnBallWith→uniformlyContinuousOnSubball`
- `centeredHasPowerSeriesOnBallWith→uniformlyContinuousOnSubball`
- `hasPowerSeriesAtWith→uniformlyContinuousOnSubball`
- `hasPowerSeriesAtWith→continuousAtOnSubball`
- `derivativePowerSeriesOnStrictSubballWith`
- `derivativePowerSeriesRadius`
- `derivativePowerSeriesInfiniteRadius`
- `hasPowerSeriesOnBallWith→hasDerivativeAtWithOnSubball`
- `hasPowerSeriesAtWith→hasDerivativeAtWith`

Names can be adjusted to match local module style, but every exported theorem
must remove a real proof obligation from downstream users. Do not publish thin
aliases that only rename existing records.

## Status By Target

| Target | Status | Remaining blocker |
| --- | --- | --- |
| Continuity from explicit partial-sum witnesses | Implemented as bridges | Needs automatic construction of the witnesses |
| Uniform continuity on a closed subball | Partially implemented | Finite polynomial modulus theorem |
| `HasPowerSeriesAtWith` continuity | Partially implemented | Same partial-sum automation gap |
| Derivative radius by coefficient path | Implemented as a bridge | Still depends on named derivative-series radius data |
| Derivative radius for `derivativePowerSeries a` | Not implemented generically | Strict-subball derivative convergence |
| Termwise derivative to `HasDerivativeAtWith` | Partially implemented | Iterated bounds and modulus-largeness are still manual |
| Elementary `exp`, `sin`, `cos` derivative instances | Partially simplified | They still pass derivative bounds and modulus-largeness data |
| `log` derivative through the generic theorem | Not implemented | Needs strict radius-one geometric derivative convergence |

## Theorem Dependency Graph

The automation target should be built in this order:

```text
finite polynomial moduli
  -> partial-sum uniform continuity
  -> sum uniform continuity on closed subballs
  -> function-level continuity from HasPowerSeriesAtWith

strict-subball derivative convergence
  -> canonical derivative radius for derivativePowerSeries
  -> formal partial derivative bounds
  -> PowerSeriesPartialSumsDerivativeModulusLarge
  -> HasDerivativeAtWith for centered sums
  -> HasDerivativeAtWith for HasPowerSeriesAtWith functions
```

The first chain is mostly proof-engineering around finite sums and continuity
criteria. The second chain is the hard mathematical content. In particular,
`PowerSeriesPartialSumsDerivativeModulusLarge` cannot be hidden until there is a
canonical way to make the input perturbation small enough for the chosen
partial derivative modulus.

## Near-Term Execution Order

Use this order before attempting the full final theorem.

1. In `Continuity.agda`, prove finite partial-sum uniform continuity from
   reusable polynomial estimates on closed balls. Keep the single-partial-sum
   helper public only if another module uses it directly.
2. In `Analytic.Consequences.agda`, replace the remaining continuity callers
   with a theorem that consumes only expansion data plus the Phase 1 automatic
   partial-sum theorem.
3. In `DerivativeConvergence.agda`, add the majorant-based strict-subball
   derivative convergence theorem before the fully generic radius theorem if
   the generic proof is too large.
4. In `TermwiseDerivative.IteratedBounds` and
   `TermwiseDerivative.PartialSums`, derive canonical iterated partial
   derivative bounds and modulus-largeness witnesses from the convergence data
   produced in step 3.
5. In `TermwiseDerivative.Theorem`, expose the final high-level derivative
   theorem only after steps 3 and 4 remove the current manual arguments.
6. Update instance modules only after the generic theorem checks. Instance
   changes are the acceptance test, not the proof strategy.

## Non-Goals

- No multivariable analytic API in this plan.
- No optimized evaluation algorithms in this plan.
- No classical radius of convergence, supremum radius, or hidden choice.
- No public wrappers that merely repackage existing definitions.
- No composition theorem unless the derivative and continuity automation is
  already complete.

## Design Choices

Use three layers, following the mature analytic-library pattern:

- Raw closed-ball power-series sums.
- Function-level "has this power series on this ball" records.
- Analytic existential wrappers only after theorem-level consequences are
  stable.

Keep the constructive boundary explicit:

- Work on closed subballs inside a positive radius.
- Carry rational margins through the public API.
- Use explicit precision and tail moduli internally.
- Prefer majorant and geometric-tail proofs over extracting arbitrary
  coefficient bounds from truncated existence data.

## Phase 1: Partial-Sum Uniform Continuity

Goal: remove manual partial-sum uniform-continuity witnesses from all callers.

Prove finite polynomial Lipschitz estimates on a closed ball. The key estimate
is the constructive version of

```text
|h ^ n - k ^ n| <= n * rho ^ (n - 1) * |h - k|
```

for `BoundedByᶜ rho h` and `BoundedByᶜ rho k`.

Implementation targets:

- `powerSeriesPartialSumLipschitzOnBallWith`
- `powerSeriesPartialSumsUniformlyContinuousOnBallFromCoefficientBounds`
- `powerSeriesPartialSumsUniformlyContinuousOnBallCanonical`

If coefficient bounds for arbitrary `ℝᶜ` coefficients are available only under
truncation, do not force a choice principle into the public API. Use one of
these routes instead:

- derive the required finite bounds from existing majorant data;
- require an explicit finite coefficient-bound stream at the internal theorem;
- expose only the higher-level theorem that consumes convergence or majorant
  data already available in the power-series record.

Acceptance criteria:

- Downstream users no longer pass
  `PowerSeriesPartialSumsUniformlyContinuousOnBallWith` by hand.
- The old criterion remains available as a low-level theorem, but ordinary
  power-series continuity proofs do not mention it.

## Phase 2: Continuity Automation

Use Phase 1 with the existing theorems in
`Constructive.Analysis.Reals.PowerSeries.Continuity`.

Implementation targets:

- `hasPowerSeriesOnBallWith→uniformlyContinuousOnSubball`
- `centeredPowerSeriesSumUniformlyContinuousOnSubball`
- `hasPowerSeriesAtWith→uniformlyContinuousOnSubball`
- `hasPowerSeriesAtWith→continuousAtOnSubball`
- within-domain variants only if a current instance needs them.

The public API should take an expansion, a smaller closed ball, and the required
strict-containment evidence. It should construct all partial-sum continuity and
sum continuity data internally.

Acceptance criteria:

- `Analytic.Consequences` can expose direct continuity consequences from
  `HasPowerSeriesAtWith`.
- Instance modules for `exp`, `sin`, `cos`, and `log` do not build continuity
  data manually when a power-series expansion is already present.

## Phase 3: Derivative-Series Convergence

Goal: prove that the formal derivative series converges on every strict
subball where the original series has positive radius.

This is the main hard theorem. Given convergence of

```text
sum a n * h ^ n
```

on a ball of radius `sigma`, and a strict smaller radius `rho < sigma`, prove
closed-ball convergence of

```text
sum (n + 1) * a (n + 1) * h ^ n
```

on the `rho` ball.

Proof route:

- Choose an intermediate rational radius when the public data gives only
  `rho < R`.
- Use tail control of `a n * sigma ^ n`.
- Convert the derivative tail to a geometric-weighted tail using the ratio
  `rho / sigma < 1`.
- Keep the ratio represented by rational slack or an existing positive-rational
  comparison, avoiding unnecessary division on `ℝᶜ`.
- Reuse `PowerSeriesMajorizedOnBall` and geometric-tail infrastructure before
  adding any local derivative-specific majorant API.

Implementation targets:

- `derivativePowerSeriesOnStrictSubballWith`
- `derivativePowerSeriesOnStrictSubball`
- `derivativePowerSeriesRadius`
- `derivativePowerSeriesInfiniteRadius`

Acceptance criteria:

- `DerivativeConvergence.agda` no longer only transports derivative convergence
  through coefficient paths for generic series.
- Existing coefficient-path theorems remain useful for named functions whose
  derivative series is definitionally or propositionally a known instance.

## Phase 4: Termwise Derivative Automation

Package the existing theorem in
`Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Theorem`.

The wrapper should internally derive:

- derivative-series convergence from Phase 3;
- target derivative-radius data by coefficient path when the derivative series
  is a named instance;
- iterated formal partial derivative bounds from generic coefficient or
  majorant bounds;
- canonical `PowerSeriesPartialSumsDerivativeModulusLarge` data;
- the derivative value as the sum of the formal derivative series.

Implementation targets:

- `centeredPowerSeriesSumFormalDerivativeAtWith`
- `centeredPowerSeriesSumEverywhereFormalDerivativeAtWith`
- `hasPowerSeriesOnBallWith→hasDerivativeAtWithOnSubball`
- `hasPowerSeriesAtWith→hasDerivativeAtWith`

Acceptance criteria:

- A caller with a power-series expansion, a point inside a strict subball, and a
  margin can obtain `HasDerivativeAtWith`.
- Downstream instance modules do not manually pass derivative radius, iterated
  bounds, or partial-sum derivative modulus records.

## Phase 5: Derivative Is Analytic

This phase is optional for the immediate derivative conclusion, but it is the
right endpoint for an analytic API.

Target conclusion:

- if `f` has a power series at `c`, then the derivative function has a power
  series locally at every point in a strict subball.

Likely hard step: re-center the derivative expansion. The coefficient formula
is the constructive analogue of

```text
b n = sum over m >= n of binomial(m, n) * a m * (x - c) ^ (m - n)
```

Do not start this phase until the direct derivative-at theorem is complete.

## Phase 6: Instances

After the generic theorems type-check, simplify the elementary instances.

Targets:

- `Instances.Exponential.Derivative`
- `Instances.Trigonometric.Derivative`
- `Instances.Logarithm`
- polynomial derivative modules where the generic theorem is cleaner than local
  proof plumbing.

Acceptance criteria:

- `exp`, `sin`, and `cos` derivative proofs use the high-level theorem plus
  coefficient identities.
- `log` uses the high-level theorem on a strict radius-one subball when the
  required geometric derivative-series convergence is available.

## Phase 7: Public API And Curation

Only theorem-level names should be re-exported by aggregate modules. Keep
internal modulus plumbing private unless it is reused across at least two hard
proofs.

Public aggregates to update only after children type-check:

- `Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative`
- `Constructive.Analysis.Reals.PowerSeries.Analytic`
- `Constructive.Analysis.Reals.PowerSeries`
- `Constructive.Analysis.Reals.PowerSeries.Instances`

Update `README.md` in the same change if public module paths or exported
interfaces change.

## Verification

For this plan file:

```text
git diff --check
```

For implementation phases, type-check the touched module and nearest aggregate
when practical:

```text
agda Constructive/Analysis/Reals/PowerSeries/Continuity.agda
agda Constructive/Analysis/Reals/PowerSeries/DerivativeConvergence.agda
agda Constructive/Analysis/Reals/PowerSeries/TermwiseDerivative.agda
agda Constructive/Analysis/Reals/PowerSeries/Analytic.agda
agda Constructive/Analysis/Reals/PowerSeries.agda
```

When public interfaces change, also check the nearest parent aggregate:

```text
agda Constructive/Analysis/Reals.agda
```

Before reporting implementation completion, run:

```text
rg "postulate|\\?|TODO|FIXME" Constructive/Analysis/Reals/PowerSeries
git diff --check
```

If Agda checking is anomalously slow, follow `docs/PERFORMANCE.md`. If a
file-level check remains too slow, add `--lossy-unification` to that module's
safe options and record the local pattern as required by repository policy.

## Risks

- Arbitrary coefficient bounds may be trapped behind truncation. Prefer proofs
  from convergence or majorant data instead of adding choice-like assumptions.
- Phase 3 is the main mathematical risk. If the fully generic radius theorem is
  too large, first prove a majorant-based derivative convergence theorem, then
  wrap it with radius data.
- Re-centering the derivative expansion is a separate hard theorem. Do not let
  it block the direct `HasDerivativeAtWith` result.
- Avoid large public plumbing modules. The public surface should be theorems
  that replace current manual proof obligations.

## Completion Criteria

The plan is complete when:

- generic continuity and uniform-continuity consequences are available from
  power-series expansion data;
- generic derivative-series convergence is available on strict subballs;
- generic termwise derivative theorems produce `HasDerivativeAtWith`;
- elementary derivative instances use the generic theorem instead of manual
  termwise-derivative plumbing;
- the PowerSeries aggregate modules type-check.
