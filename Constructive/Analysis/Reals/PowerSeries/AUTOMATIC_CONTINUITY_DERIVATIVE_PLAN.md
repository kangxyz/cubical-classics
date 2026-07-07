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
- Mathlib's derivative API is the closest mature implementation template for
  the final target. It exposes consequences such as
  `HasFPowerSeriesAt.hasDerivAt`, `HasFPowerSeriesOnBall.hasFDerivAt`,
  `HasFPowerSeriesOnBall.fderiv`, and `AnalyticAt.fderiv`:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Analytic.html
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
- Mathlib's derivative split is important locally: derivative at the expansion
  center is easier than differentiability at every point in a ball; derivative
  of the function as an analytic function requires convergence of the derivative
  series after moving the origin. The local constructive version should keep
  direct `HasDerivativeAtWith` and derivative-is-analytic as separate phases.
- O'Connor, Krebbers-Spitters, and CoRN all support the same constructive
  engineering rule: make moduli, approximants, and convergence witnesses
  first-class rather than hiding them behind classical existence.
- Arb is only a later performance reference. Its Taylor and ball-arithmetic
  algorithms should not determine the public proof API until the correctness
  theorems are stable.

## Mature Pattern To Local Proof Shape

| External pattern | Local proof shape | Local non-goal |
| --- | --- | --- |
| Mathlib `HasFPowerSeriesOnBall.continuousOn` | closed-subball uniform continuity from `HasPowerSeriesAtWith` plus explicit margin data | classical open-ball topological API |
| Mathlib `HasFPowerSeriesAt.hasDerivAt` style consequences | derivative theorem whose public input is an expansion and strict-subball point data | caller-built derivative-radius and partial-sum modulus records |
| Mathlib `HasFPowerSeriesOnBall.fderiv` and `AnalyticAt.fderiv` | later theorem that the derivative function has a local power-series expansion | making re-centering block the direct derivative-at theorem |
| Mathlib composition API | later proof family after derivative automation is stable | coefficient reindexing before continuity and derivative results |
| O'Connor exact real elementary functions | moduli and approximation indices stay explicit in internal records | hidden classical convergence arguments |
| Krebbers-Spitters exact reals | majorants and approximate operations drive constructive estimates | extracting arbitrary coefficient bounds by choice |
| CoRN real analysis | reusable continuity, differentiability, and Taylor interfaces | duplicating low-level proof plumbing in each instance |
| Arb implementation practice | future performance route for Taylor evaluation and error bounds | using optimized evaluation as the correctness theorem API |

This plan follows the same split used by mature libraries: public theorems
state mathematical consequences, while constructive precision data is built by
the theorem implementation or carried by small internal records.

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
- `mulᶜ-close-right-with-bound`
- `mulᶜ-close-left-with-bound`
- `PowerSeriesCoefficientBoundsWith`
- `PowerSeriesCoefficientBounds`
- `powerSeriesPartialSumBoundedOnBallFromCoefficientBoundsWith`
- `powerSeriesPartialSumBoundedOnBallFromCoefficientBounds`
- `powerSeriesPartialSumUniformlyContinuousOnBallFromCoefficientBoundsWith`
- `powerSeriesPartialSumUniformlyContinuousOnBallFromCoefficientBounds`
- `powerSeriesPartialSumsModulusFromCoefficientBounds`
- `powerSeriesPartialSumsUniformlyContinuousOnBallFromCoefficientBoundsWith`
- `powerSeriesPartialSumsUniformlyContinuousOnBallFromCoefficientBounds`
- `powerSeriesCoefficientBoundsFromRationalProbeTermBoundsWith`
- `powerSeriesCoefficientBoundsFromBallTermBoundsWith`
- `powerSeriesCoefficientBoundsFromBallTermBounds`
- `powerSeriesPartialSumsUniformlyContinuousOnBallFromBallTermBoundsWith`
- `powerSeriesPartialSumsUniformlyContinuousOnBallFromBallTermBounds`
- `powerSeriesSumUniformlyContinuousFromCoefficientBoundsWith`
- `powerSeriesSumUniformlyContinuousFromCoefficientBounds`
- `powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonicalWith`
- `powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical`
- `powerSeriesSumUniformlyContinuousFromBallTermBoundsWith`
- `powerSeriesSumUniformlyContinuousFromBallTermBounds`
- `powerSeriesSumUniformlyContinuousFromBallTermBoundsCanonicalWith`
- `powerSeriesSumUniformlyContinuousFromBallTermBoundsCanonical`
- `powerSeriesSumContinuousAtFromCoefficientBoundsWith`
- `powerSeriesSumContinuousAtFromCoefficientBounds`
- `powerSeriesSumContinuousAtFromCoefficientBoundsCanonicalWith`
- `powerSeriesSumContinuousAtFromCoefficientBoundsCanonical`
- `powerSeriesSumContinuousAtFromBallTermBoundsWith`
- `powerSeriesSumContinuousAtFromBallTermBounds`
- `powerSeriesSumContinuousAtFromBallTermBoundsCanonicalWith`
- `powerSeriesSumContinuousAtFromBallTermBoundsCanonical`
- `powerSeriesSumUniformlyContinuousFromBoundedTermsAndMajorantCanonicalWith`
- `powerSeriesSumUniformlyContinuousFromBoundedTermsAndMajorantCanonical`
- `powerSeriesSumContinuousAtFromBoundedTermsAndMajorantCanonicalWith`
- `powerSeriesSumContinuousAtFromBoundedTermsAndMajorantCanonical`
- `centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsWith`
- `centeredPowerSeriesSumUniformlyContinuousFromCoefficientBounds`
- `centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonicalWith`
- `centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical`
- `centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsWith`
- `centeredPowerSeriesSumUniformlyContinuousFromBallTermBounds`
- `centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsCanonicalWith`
- `centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsCanonical`
- `hasPowerSeriesAtWith→uniformlyContinuousOnBallFromCoefficientBoundsWith`
- `hasPowerSeriesAtWith→uniformlyContinuousOnBallFromCoefficientBounds`
- `hasPowerSeriesAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonicalWith`
- `hasPowerSeriesAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonical`
- `hasPowerSeriesAtWith→uniformlyContinuousOnBallFromBallTermBoundsWith`
- `hasPowerSeriesAtWith→uniformlyContinuousOnBallFromBallTermBounds`
- `hasPowerSeriesAtWith→uniformlyContinuousOnBallFromBallTermBoundsCanonicalWith`
- `hasPowerSeriesAtWith→uniformlyContinuousOnBallFromBallTermBoundsCanonical`
- `hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromCoefficientBoundsWith`
- `hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromCoefficientBounds`
- `hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonicalWith`
- `hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonical`
- `hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromBallTermBoundsWith`
- `hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromBallTermBounds`
- `hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromBallTermBoundsCanonicalWith`
- `hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromBallTermBoundsCanonical`
- `hasPowerSeriesAtWith→continuousAtFromCoefficientBoundsWith`
- `hasPowerSeriesAtWith→continuousAtFromCoefficientBounds`
- `hasPowerSeriesAtWith→continuousAtFromCoefficientBoundsCanonicalWith`
- `hasPowerSeriesAtWith→continuousAtFromCoefficientBoundsCanonical`
- `hasPowerSeriesAtWith→continuousAtFromBallTermBoundsWith`
- `hasPowerSeriesAtWith→continuousAtFromBallTermBounds`
- `hasPowerSeriesAtWith→continuousAtFromBallTermBoundsCanonicalWith`
- `hasPowerSeriesAtWith→continuousAtFromBallTermBoundsCanonical`
- `hasPowerSeriesWithinAtWith→continuousAtFromCoefficientBoundsWith`
- `hasPowerSeriesWithinAtWith→continuousAtFromCoefficientBounds`
- `hasPowerSeriesWithinAtWith→continuousAtFromCoefficientBoundsCanonicalWith`
- `hasPowerSeriesWithinAtWith→continuousAtFromCoefficientBoundsCanonical`
- `hasPowerSeriesWithinAtWith→continuousAtFromBallTermBoundsWith`
- `hasPowerSeriesWithinAtWith→continuousAtFromBallTermBounds`
- `hasPowerSeriesWithinAtWith→continuousAtFromBallTermBoundsCanonicalWith`
- `hasPowerSeriesWithinAtWith→continuousAtFromBallTermBoundsCanonical`
- `powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds`
- `centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndTargetRadiusAndCoefficientBoundsOnSubballCanonicalIndex→hasDerivativeAtWith`
- `centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith`
- `centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith`
- `centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientBoundsOnSubballCanonicalIndex→hasDerivativeAtWith`
- `PowerSeriesPartialSumsDerivativeUniformModulus`
- `powerSeriesPartialSumsDerivativeModulusLargeFromUniformModulus`
- `powerSeriesPartialSumsDerivativeModulusLargeFromUniformSubmodulus`
- `hasDerivativeAtWith-local-cong`
- `hasPowerSeriesAtWith→hasDerivativeAtWithFromLocalModel`
- `hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel`
- `hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex`
- `hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndCoefficientBoundsOnSubballCanonicalIndex`
- `hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientBoundsOnSubballCanonicalIndex`

These remove three pieces of repeated downstream proof plumbing: manually
threading centered sum continuity through analytic expansions, manually
building partial-sum continuity witnesses when explicit coefficient bounds are
available, and manually deriving derivative-radius data from a coefficient path
plus target radius data. The formal derivative bridge also specializes the
termwise derivative theorem to `derivativePowerSeries a` without passing a
reflexive coefficient path or duplicate target radius data.
The coefficient-bound derivative bridge additionally constructs the canonical
formal partial derivative bounds from coefficient bounds, so instance proofs no
longer need to pass `PowerSeriesIteratedFormalPartialDerivativeBounds` when
those coefficient bounds are already available.
The formal-derivative coefficient-bound bridge gives the same benefit when the
public derivative value is the sum of `derivativePowerSeries a`, without
requiring a coefficient path to a named target series.
The function-level derivative bridges transport a derivative from a total
centered-sum model through the local expansion path. This removes manual
rewriting of `linearRemainder` once the centered model derivative is available,
including the common everywhere-radius model produced by
`centeredPowerSeriesSumEverywhere`.
The function-level coefficient-bound derivative wrappers now combine this
transport with the centered-sum termwise derivative theorem, so callers with
`HasPowerSeriesAtWith` no longer need to build a separate derivative for the
centered model before transporting it to the expanded function.
The matching function-level iterated-bound wrapper gives the same transport
when a caller already has explicit iterated derivative bounds.
The partial-sums derivative modulus layer now has a checked strengthened
condition, `PowerSeriesPartialSumsDerivativeUniformModulus`, plus constructors
to obtain `PowerSeriesPartialSumsDerivativeModulusLarge` directly or after
shrinking another perturbation modulus by `min⁺`. This proves the planned
record-strengthening route for the derivative-modulus blocker; the remaining
work is to construct the uniform datum from convergence, majorants, or
canonical partial-sum derivative moduli.
The canonical coefficient-bound continuity bridges choose
`powerSeriesLimitApproximationIndex μ` internally and discharge the index
comparison by reflexivity, so callers no longer pass `χ` or `index-large` when
explicit coefficient bounds are available.
The closed-ball term-bound bridges derive coefficient bounds by probing the
term bound at the positive rational radius and rescaling by the inverse power of
that radius. The same data now feeds partial sums, raw sums, centered sums, and
`HasPowerSeriesAtWith` / `HasPowerSeriesWithinAtWith` continuity consequences,
including canonical variants that choose `powerSeriesLimitApproximationIndex μ`
internally.
The bounded-term/majorant bridges now also construct the convergence witness
from the majorant tail and use the same bounded-term data to construct
canonical sum-level uniform-continuity and point-continuity witnesses. This
removes the repeated pattern of separately calling
`hasPowerSeriesOnBallWithFromBoundedTerms` and then rebuilding continuity from
the original term bounds.
The real-majorant/rational-bound continuity bridges convert
`SeriesMajorizedBy (powerSeriesTerm a h) v` plus rational bounds for the
majorant terms `v n` into the ball-term bounds required by the finite
partial-sum continuity machinery. This route supports partial sums, raw sums,
centered sums, and ordinary/within-domain `HasPowerSeriesAtWith` consequences
without choosing arbitrary coefficient bounds from truncation.

The partial-sum modulus bridge is intentionally modest. It converts either a
family of finite partial-sum moduli, explicit coefficient bounds, or closed-ball
term bounds into the existing sum-level continuity criterion. It also consumes
bounded-term majorant data when rational term bounds are part of that data. It
does not yet construct rational term bounds automatically from arbitrary
convergence, majorant, or radius data.

Updated downstream users:

- `expᶜHasDerivativeAtWithFromIteratedBoundsOnSubball`
- `expᶜHasDerivativeAtWithFromCoefficientBoundsOnSubball`
- `exp` derivative entries now use the function-level `HasPowerSeriesAtWith`
  wrappers rather than the centered-sum theorem directly
- `expᶜUniformlyContinuousOnBallFromCoefficientBounds`
- `expᶜContinuousAtFromCoefficientBounds`
- `sinᶜHasDerivativeAtWithFromIteratedBoundsOnSubball`
- `sinᶜHasDerivativeAtWithFromCoefficientBoundsOnSubball`
- `sin` derivative entries now use the function-level `HasPowerSeriesAtWith`
  wrappers rather than the centered-sum theorem directly
- `sinᶜUniformlyContinuousOnBallFromCoefficientBounds`
- `sinᶜContinuousAtFromCoefficientBounds`
- `cosᶜHasDerivativeAtWithFromIteratedBoundsOnSubball`
- `cosᶜHasDerivativeAtWithFromCoefficientBoundsOnSubball`
- `cos` derivative entries now use the function-level `HasPowerSeriesAtWith`
  wrappers before rewriting the named `- sin` target
- `cosᶜUniformlyContinuousOnBallFromCoefficientBounds`
- `cosᶜContinuousAtFromCoefficientBounds`
- `logOnePlusᶜWithinSubunitBallUniformlyContinuousFromCoefficientBounds`
- `logOnePlusᶜWithinSubunitBallContinuousAtFromCoefficientBounds`

Remaining hard gaps:

- automatically constructing closed-ball rational term bounds or partial-sum
  uniform-continuity witnesses from arbitrary convergence, majorant, or radius
  data;
- proving generic derivative-series convergence on strict subballs;
- constructing derivative-modulus largeness data from convergence or majorant
  data, and constructing canonical iterated derivative bounds when explicit
  coefficient bounds are not available;
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

## Target Proof Contracts

| Theorem family | Caller supplies | The theorem constructs internally | Primary module |
| --- | --- | --- | --- |
| subball uniform continuity | expansion, closed subball, strict radius evidence | partial-sum moduli, approximation index, sum-level uniform continuity | `PowerSeries.Continuity` and `Analytic.Consequences` |
| point continuity from a local series | `HasPowerSeriesAtWith` and radius/margin data | centered-sum continuity and function equality transport | `Analytic.Consequences` |
| derivative series on strict subballs | original convergence/radius or majorant data | convergence of `derivativePowerSeries a` on smaller balls | `DerivativeConvergence` |
| termwise derivative for centered sums | expansion point, subball point, derivative coefficient identity when needed | derivative-radius data, iterated derivative bounds, modulus-largeness data, derivative value | `TermwiseDerivative.Theorem` |
| function-level derivative | `HasPowerSeriesAtWith` and point-in-subball data | centered derivative theorem plus equality transport to the function | `Analytic.Consequences` |
| elementary instances | named coefficient identities and existing expansion proofs | all generic continuity and derivative plumbing | `Instances.*` |

Each contract is complete only when an ordinary caller can use the public theorem
without mentioning `PowerSeriesPartialSumsUniformlyContinuousOnBallWith`,
`PowerSeriesIteratedFormalPartialDerivativeBounds`, or
`PowerSeriesPartialSumsDerivativeModulusLarge`.

## Status By Target

| Target | Status | Remaining blocker |
| --- | --- | --- |
| Continuity from explicit partial-sum witnesses | Implemented as bridges | Needs automatic construction from expansion data |
| Uniform continuity on a closed subball | Partially implemented | Coefficient, closed-ball term, bounded-term majorant, or real-majorant/rational-bound data can now drive canonical moduli; arbitrary radius/convergence data still cannot |
| `HasPowerSeriesAtWith` continuity | Partially implemented | Direct coefficient-bound, closed-ball term-bound, and real-majorant/rational-bound variants exist; need bridge from expansion/radius data to usable bounds |
| Derivative radius by coefficient path | Implemented as a bridge | Still depends on named derivative-series radius data |
| Derivative radius for `derivativePowerSeries a` | Not implemented generically | Strict-subball derivative convergence |
| Termwise derivative to `HasDerivativeAtWith` | Partially implemented | Coefficient-bound variants build iterated bounds for named targets and formal derivative targets; modulus-largeness is still manual |
| Function-level derivative transport | Implemented as local, everywhere-model, and coefficient-bound termwise bridges | Modulus-largeness is still manual |
| Elementary `exp`, `sin`, `cos` derivative instances | Partially simplified | Coefficient-bound entries avoid passing derivative bounds; modulus-largeness is still manual |
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
  -> local derivative congruence for equal functions near the base point
  -> HasDerivativeAtWith for HasPowerSeriesAtWith functions
```

The first chain is mostly proof-engineering around finite sums and continuity
criteria. The second chain is the hard mathematical content. In particular,
`PowerSeriesPartialSumsDerivativeModulusLarge` cannot be hidden until there is a
canonical way to make the input perturbation small enough for the chosen
partial derivative modulus.

## Near-Term Execution Order

Use this order before attempting the full final theorem.

1. In `Continuity.agda`, extend finite partial-sum uniform continuity from
   explicit coefficient bounds to the majorant/radius data already carried by
   power-series convergence records. Keep the single-partial-sum helper public
   only if another module uses it directly.
2. In `Analytic.Consequences.agda`, use the coefficient-bound bridges as the
   temporary high-level continuity API, then replace them with a theorem that
   consumes only expansion data plus the Phase 1 automatic partial-sum theorem.
3. In `DerivativeConvergence.agda`, add the majorant-based strict-subball
   derivative convergence theorem before the fully generic radius theorem if
   the generic proof is too large.
4. In `Constructive.Analysis.Reals.Calculus.Derivative`, add a local
   derivative congruence theorem. It should transport `HasDerivativeAtWith`
   from a model function `g` to a function `f` using equality at the base point
   and equality on the small perturbations allowed by the chosen modulus.
5. In `Analytic.Consequences.agda`, add a bridge from
   `HasPowerSeriesAtWith` to function-level derivative conclusions whenever a
   total centered-sum model already has the derivative.
6. In `TermwiseDerivative.IteratedBounds` and
   `TermwiseDerivative.PartialSums`, derive canonical iterated partial
   derivative bounds and modulus-largeness witnesses from the convergence data
   produced in step 3.
7. In `TermwiseDerivative.Theorem`, expose the final high-level derivative
   theorem only after steps 3 through 6 remove the current manual arguments.
8. Update instance modules only after the generic theorem checks. Instance
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

Implemented first:

- `powerSeriesPartialSumsUniformlyContinuousOnBallFromCoefficientBounds`
- `powerSeriesSumUniformlyContinuousFromCoefficientBounds`
- `powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical`
- `powerSeriesSumContinuousAtFromCoefficientBoundsCanonical`
- `centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical`
- `hasPowerSeriesAtWith→uniformlyContinuousOnBallFromCoefficientBounds`
- `hasPowerSeriesAtWith→continuousAtFromCoefficientBounds`
- `hasPowerSeriesAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonical`
- `hasPowerSeriesAtWith→continuousAtFromCoefficientBoundsCanonical`

Remaining implementation targets:

- `powerSeriesPartialSumLipschitzOnBallWith`
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

Implemented intermediate bridges:

- canonical coefficient-bound variants hide `χ` and `index-large` by using
  `powerSeriesLimitApproximationIndex` and reflexive index comparison;
- ordinary and within-domain variants are available for uniform continuity and
  continuous-at conclusions in `Analytic.Consequences`.
- `Instances.Exponential.Convergence` and `Instances.Trigonometric.Convergence`
  now expose coefficient-bound continuity consequences for `exp`, `sin`, and
  `cos`.
- `Instances.Logarithm` now uses the within-domain canonical coefficient-bound
  consequences for uniform continuity and point continuity on the subunit ball.
- real-majorant/rational-bound variants now derive ball-term bounds from
  `SeriesMajorizedBy` data and expose ordinary and within-domain
  `HasPowerSeriesAtWith` consequences.

Implementation targets:

- `hasPowerSeriesOnBallWith→uniformlyContinuousOnSubball`
- `centeredPowerSeriesSumUniformlyContinuousOnSubball`
- `hasPowerSeriesAtWith→uniformlyContinuousOnSubball`
- `hasPowerSeriesAtWith→continuousAtOnSubball`

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

Implemented transport bridges:

- `hasDerivativeAtWith-local-cong`
- `hasPowerSeriesAtWith→hasDerivativeAtWithFromLocalModel`
- `hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel`
- `hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex`
- `hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndCoefficientBoundsOnSubballCanonicalIndex`
- `hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientBoundsOnSubballCanonicalIndex`

Remaining implementation targets:

- `centeredPowerSeriesSumFormalDerivativeAtWith`
- `centeredPowerSeriesSumEverywhereFormalDerivativeAtWith`
- `hasPowerSeriesOnBallWith→hasDerivativeAtWithOnSubball`
- `hasPowerSeriesAtWith→hasDerivativeAtWith`

The transport targets are deliberately separated from derivative-series
convergence. They do not prove new analytic convergence, but they remove a real
function-level proof obligation: once a centered model has a derivative and an
expansion path identifies the original function with that model near the base
point, the caller should not rewrite the linear remainder by hand.

Current blocker:

- The partial-sum derivative modulus record now has the strengthened
  uniform-lower-bound route:
  `PowerSeriesPartialSumsDerivativeUniformModulus χ μ ω` implies
  `PowerSeriesPartialSumsDerivativeModulusLarge χ μ ω`, and also after
  replacing an existing perturbation modulus by `λ ε → min⁺ (μ ε) (ν ε)`.
  What remains is the mathematical construction of that uniform datum from the
  convergence or majorant data used by the termwise derivative theorem. Without
  that construction, instance proofs can still be asked for a manual uniform
  witness or the older largeness witness.

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
