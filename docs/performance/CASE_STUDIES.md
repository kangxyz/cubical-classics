# Agda Performance Case Studies

This document records fixed Agda performance cases for this repository. Use
[the runbook](RUNBOOK.md) for the triage workflow and common slow patterns;
keep current measurements and unfinished diagnostics in
[baselines](BASELINES.md).

The historical examples below came from profiling the constructive
real-analysis stack with Agda 2.8.0. Add a new case only after the slow check
is understood and the response has been verified. Record the environment and
recipe, symptom, dominant profile signal, root cause, change, before/after
measurements, and checks whenever that evidence is available.

## Control Flow And Conversion

### Sequences.Order: avoid a dependent `with` split

`Constructive.Analysis.Reals.Sequences.Order` spent about 200 seconds in
`eventuallyApart-sym`. The proof used `with u#v n N≤n` over the apartness sum.
Replacing the `with` split by `Sum.rec inr inl (u#v n N≤n)` reduced the file
check to a few seconds.

### Series.Tail: name branches of a large boundedness target

`Constructive.Analysis.Reals.Series.Tail` spent about 28 seconds in
`tailBound-pair`. The hot spot was `with NatOrder.splitℕ-≤ m n` over a large
boundedness target. Rewriting it as `Sum.rec left right ...` with named branch
proofs avoided the expensive motive abstraction.

### PowerSeries.Base: local lossy unification

`Constructive.Analysis.Reals.PowerSeries.Base` spent about 58 seconds in
`powerSeriesConvergesFromFiniteTailBound`. The proof is a thin wrapper around
series convergence, and the cost was conversion/unification rather than
mathematical work. Adding `--lossy-unification` to the module reduced the
file-level check to a few seconds.

### PowerSeries.DerivativeConvergence: explicit scale expression

`Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence` became
anomalously slow while adding the strict-subball derivative-convergence proof,
with conversion/unification pressure around scalar-majorant transports and the
strict-subball scale expression. Keeping the scalar scale expression explicit
at use sites and adding `--lossy-unification` kept cached file checks around
5-6 seconds.

## Positivity And Proof-Data Packaging

### IVT.Uniform: replace a proof-data record with `Σ`

`Constructive.Analysis.Reals.IVT.Uniform` checked at about 52 seconds in a
cold local profile, with about 49 seconds under `Positivity`. The hot surface
was not a proof body; it was the public `IVTFunctionData` record over interval
functions and locator evidence. Replacing that record with a transparent
iterated `Σ` alias, plus a small `IVTFunctionData` projection module, reduced
the file check to about 4 seconds. Do not hide this alias behind `abstract`:
callers in the approximate IVT stack need the package to reduce definitionally.
Use qualified projections from the `IVTFunctionData` module at call sites.

### Interval.Extrema: simplify approximate extrema packages

`Constructive.Analysis.Reals.Interval.Extrema` checked at about 74 seconds,
with about 69 seconds under `Positivity`. The public `ApproxMaximum` and
`ApproxMinimum` records were just packaging a rational value, a truncated
witness, and an upper or lower bound. Encoding them as `Σ` packages with
constructor-shaped helper functions and qualified projection modules reduced
the file check to about 5 seconds. The constructors remain available as
helper functions, but callers should use the qualified projection modules
rather than relying on unqualified record-field opens.

### Calculus.Derivative: use function aliases for single-field records

`Constructive.Analysis.Reals.Calculus.Derivative` checked at about 29 seconds,
with about 25 seconds under `Positivity`. The single-field
`HasDerivativeAtWith` and `HasDerivativeWithinAtWith` records were replaced by
function type aliases, keeping projection-style helper functions for call
sites. The file then checked in about 4 seconds.

### Calculus.Derivative.BoundedSegment: localize path-heavy pressure

`Constructive.Analysis.Reals.Calculus.Derivative.BoundedSegment` became
anomalously slow after adding finite-subdivision derivative estimates and
ring-solver linear-remainder splitting. The local file check did not complete
after repeated 30 second waits. Keeping the helper module small and adding
`--lossy-unification` localized the conversion pressure from the path-heavy
subdivision proof.

### Series.Comparison: replace `SeriesMajorizedBy` with `Σ`

`Constructive.Analysis.Reals.Series.Comparison` checked at about 46 seconds,
with about 36 seconds under `Positivity`. Replacing the proof-packaging
`SeriesMajorizedBy` record with a `Σ` package and qualified projections reduced
the file check to about 4 seconds.

### PowerSeries.Majorant: replace the ball-majorant record

`Constructive.Analysis.Reals.PowerSeries.Majorant` checked at about 36 seconds
inside a cold local `PowerSeries` aggregate profile, with about 33 seconds
under `Positivity`. The `PowerSeriesMajorizedOnBall` record only packaged a
term majorization proof, a tail bound, and an antitone modulus. Replacing it
with a `Σ` package and qualified projections reduced the module to under a
second in the aggregate profile; standalone cached checks are about 5 seconds.

### PowerSeries.Recenter.Majorant: simplify recentering packages

`Constructive.Analysis.Reals.PowerSeries.Recenter.Majorant` checked at about
37 seconds inside a cold local `PowerSeries` aggregate profile, with about
40 seconds under `Positivity` in a direct internal profile. The file was
small; the hot surface was the public proof/data records
`RecenterCoefficientMajorantData` and `RecenterCoefficientMajorants`.
Replacing them with transparent `Σ` packages and projection modules, and
turning the only record literal into an explicit tuple/function package,
reduced the module to about 48 milliseconds in the aggregate profile.

### PowerSeries.TermwiseDerivative: remove two different hot surfaces

`Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative` checked at about
66 seconds inside the same aggregate profile, with about 68 seconds under
`Positivity` in a direct internal profile. The hot declaration was another
proof-packaging record, `PowerSeriesTermwiseDerivativeAtWith`. Replacing it
with a `Σ` package reduced the module to under a second in the aggregate
profile; standalone cached checks are about 5 seconds.

A later expansion of the same module reintroduced a cold aggregate cost of
about 19 seconds in
`Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative`. This time the
internal profile was dominated by `Typing.CheckRHS`, not `Positivity`: many
public convenience theorems forwarded through one another before reaching the
same primitive termwise-derivative bounds. The local fix was to remove the
unused wrapper ladder and keep a direct implementation of the canonical
centered theorem used by the exponential and trigonometric instances. In a
cold `PowerSeries` aggregate profile, the module dropped to about 6.2 seconds
and the aggregate dropped from about 27.8 seconds to about 15.4 seconds.

### SecondDerivativePartialSumBounds.Finite: eliminate nested `with` splits

`Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.SecondDerivativePartialSumBounds.Finite`
checked at about 24 seconds inside a cold local `PowerSeries` aggregate
profile. A direct definitions profile put about 22 seconds in a local
`bound` proof over partial-sum boundedness. The proof used `with` splits on
`NatOrder.≤-split` and `NatOrder.splitℕ-≤` over large dependent boundedness
targets. Rewriting both splits as `Sum.rec` with named `left` and `right`
branches reduced the module to about 171 milliseconds in the aggregate
profile.

## Constructive Reals Aggregate Pass

### Constructive.Analysis.Reals: aggregate before and after

`Constructive.Analysis.Reals` was profiled from a cold local copy after
removing only the repository `_build` directory and keeping external Cubical
interfaces cached. Before the Constructive cleanup, the aggregate profile was
about 224 seconds. The largest local modules were
`Constructive.Data.Rationals.Archimedean` at about 42 seconds,
`Constructive.Analysis.Reals.Series.Instances.Geometric.Real` at about
39 seconds, `Constructive.Analysis.Reals.Interval.TotallyBounded` at about
24 seconds, and `Constructive.Analysis.Reals.Interval.Grid` at about
17 seconds. After the fixes below, the same cold aggregate profile was about
104 seconds. A cold `/usr/bin/time -l agda Constructive/Analysis/Reals.agda`
run after the fixes reported `2061697024` bytes maximum resident set size and
about 106 seconds wall time.

### Rationals.Archimedean: prefer a direct rational proof

`Constructive.Data.Rationals.Archimedean` spent about 40 seconds in a direct
definitions profile, with about 37 seconds in `archimedean-unit-fraction`.
The trigger was routing a rational-specific unit-fraction fact through the
generic `isArchimedean→isArchimedeanInv` ordered-field theorem. Replacing it
with a direct proof from `ℚArch.isArchimedeanℚ 1ℚ ε`, and making the zero case
and multiplicative endpoint transport explicit, reduced the file profile to
about 10 seconds. In the fixed cold aggregate, the module was about
7.2 seconds.

### Series.Instances.Geometric.Real: unpack several proof-data records

`Constructive.Analysis.Reals.Series.Instances.Geometric.Real` looked like
`Miscellaneous` in a definitions profile, but `--profile=internal` showed
about 36 seconds under `Positivity`. The hot declarations were proof/data
records such as `RealGeometricBound`, `RealGeometricTerms`,
`RealGeometricPowerMajorant`, and `RealGeometricPowerBounds`. Replacing them
with transparent `Σ` packages or function aliases, while keeping projection
modules with the same names, reduced `Positivity` to about 10 milliseconds and
the standalone internal profile to about 5 seconds. In the fixed cold
aggregate, the module was about 1 second.

### Interval.Grid: retain public parameters in a `Σ` package

`Constructive.Analysis.Reals.Interval.Grid` spent about 19 seconds in a direct
internal profile, with about 15 seconds under `Positivity`, even though the
record only packaged grid points and endpoint paths. Replacing `Grid` with a
transparent `Σ` package removed the positivity cost. The first version of the
alias omitted the `a≤b` parameter from the right-hand side, which caused
downstream `Grid.point` calls to leave hidden `a≤b` metas unsolved. Keep a
small equality anchor for such API parameters in the package:
`Σ[ order ∈ a ≤ᶜ b ] Σ[ _ ∈ order ≡ a≤b ] ...`. With that anchor, the core
grid module checked in about 3.4 seconds standalone and about 59 milliseconds
inside the fixed cold aggregate, without patching downstream grid clients.

### Interval.TotallyBounded: explicit boundary parameters

`Constructive.Analysis.Reals.Interval.TotallyBounded` checked at about
24 seconds in the original cold aggregate, and a direct definitions profile
put about 22 seconds in local finite-net/grid packaging. Adding
`--lossy-unification` to this small interface module, and making the
`GridCovers` parameters explicit at the finite-net boundary, reduced the
standalone profile to about 4 seconds. In the fixed cold aggregate, the
module was about 38 milliseconds.

### `Σ`-package migration: recheck downstream aggregates

After changing a record package to a `Σ` package, recheck aggregate modules.
Projection functions no longer get record elaboration behavior, so dependent
uses may need explicit hidden parameters. In the IVT approximate modules,
passing `{a}`, `{b}`, and `{f}` explicitly to `locatedIVTFunctionData`,
`gridSampleValues`, `gridSampleClose`, and `adjacentSampleValuesClose` kept
the aggregate `Constructive.Analysis.Reals.IVT` check small and predictable.
In the power-series modules, passing explicit hidden parameters around
`PowerSeriesMajorizedOnBall` projections avoids large unresolved metas.

## Later Focused Cases

### PowerSeries.Recenter.FiniteIdentity: replace a solver call

`Constructive.Analysis.Reals.PowerSeries.Recenter.FiniteIdentity` initially
used the commutative-ring solver for the triangular snoc associativity step and
did not finish after 90 seconds. Replacing the solver call with an explicit
`add-assoc`/`add-comm` proof kept the target small and made the module check in
about five seconds.

### Logarithm.Global: isolate path-heavy ordered-ring transport

`Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.Global` became
slow after adding the automatic subunit bound for the atanh transform. The
trigger was a path-heavy ordered-ring proof combining rational radius
transports, reciprocal identities, and commutative-ring solver normalizations;
the local check did not finish after repeated 30 second waits. Keeping the
proof local to the global-log module and adding `--lossy-unification` reduced
the cached file check to about 14 seconds.

### CauchyReals.Arithmetic.BoundedDivision: reciprocal-bound transport

`Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision` became
slow after adding the tight positive-reciprocal bound
`reciprocalPositiveᶜ-posInv-bound`. The trigger was the ordered-ring transport
from `ε ≤ x` through multiplication by the reciprocal and the rational inverse
identity. The local check did not finish after repeated 30 second waits;
adding `--lossy-unification` kept the cached file check under 10 seconds.

### Logarithm.DomainScaling: fixed-denominator division and radius scaling

`Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.DomainScaling`
inherits the same path-heavy transport shape when packaging fixed-denominator
division as a finite linear power series and strict subunit radius scaling.
The module did not finish after repeated 30 second waits without lossy
unification; keeping it small and adding `--lossy-unification` made the cached
check complete in about 16 seconds.

### Logarithm.FunctionalEquation: factor argument transport

`Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation`
became slow when the local log functional-equation proof imported
`PowerSeries.CauchyProduct.Remainder` only to reuse
`seriesSumFromFiniteTailBound-cong`, and it stayed slow after copying that
congruence proof locally through sequence convergence uniqueness. Both
variants did not finish after repeated 30 second waits. Keep this module on
the small domain/algebra bridges for now; move the alternating-geometric
`powerSeriesSumOnBall` to `realPower` sum bridge into a dedicated small module
before using it in the full log identity.

The same module also became slow when a public theorem type mentioned
`atanhᶜFromSubunitBound` over a transported `logTransformᶜ (1 + u)` argument;
isolating that wrapper in a small submodule still did not finish after a
30 second wait. Keep the checked bridge at the algebraic `logTransformᶜ`
path level, and delay `atanhᶜFromSubunitBound` transport until the surrounding
normal form is already fixed by a smaller theorem.

The workable response was to factor only argument transport for
`atanhᶜFromSubunitBound` into
`PowerSeries.Instances.Logarithm.FunctionalEquation.AtanhTransport` and prove
it through `powerSeriesSumOnBall-center-path`. This avoids forcing Agda to
normalize the `powerSeriesSumOnBall` definition under `subst`; the small module
and the importing functional-equation module both check in under 10 seconds in
cached mode.

### PowerSeries residual RHS cleanup: name local proof targets

A 2026-07-10 cold local `PowerSeries` aggregate profile with Agda 2.8.0 found
no remaining positivity or proof-data record outlier. The largest PowerSeries
modules were RHS/reflection-heavy bridge files:
`TermwiseDerivative.Theorem`,
`Logarithm.FunctionalEquation.GlobalDerivative`,
`Logarithm.FunctionalEquation.QuotientDerivative`, and
`Logarithm.GlobalAnalytic`.

Direct isolated definitions profiles pointed at local RHS work rather than
large public signatures. Naming the translated centered sum in
`TermwiseDerivative.Theorem` kept repeated derivative-bound targets smaller
and reduced the direct definitions profile from about 8.7 seconds to about
8.5 seconds. Naming the reciprocal-error cancellation subproof as
`error-terms-zero` in the two logarithmic fractional-derivative modules shrank
their hot `remainder-path` checks: `GlobalDerivative` went from about
9.9 seconds to about 9.2 seconds, and `QuotientDerivative` went from about
9.6 seconds to about 8.7 seconds.

A broader attempt to extract the shared second-order reciprocal remainder
bound into a helper module was tested and rejected: the helper checked at
about 4.4 seconds and made both importers slower. In these bridge proofs,
prefer small local named subproofs with explicit targets over new shared
abstractions unless a profile shows a net win.
