# Performance Guide

This document records Agda performance triage practices for this repository.
Use it before changing proof shape just because a local check is unexpectedly
slow.

## Baseline Workflow

Start by separating dependency rebuild cost from the module you are
investigating.

```sh
agda Foo.agda
agda --profile=modules Foo.agda
agda --profile=definitions Foo.agda
agda --profile=conversion --profile=constraints --profile=instances Foo.agda
```

Use cached imports for the first pass.  Avoid `--ignore-interfaces` on an
aggregate module unless the target is dependency rebuild cost; it rechecks
Cubical and the whole imported analysis stack, which can hide the local
problem.

For a cold local profile that keeps external library caches intact, copy the
working tree without `_build`:

```sh
tmp=/private/tmp/cubical-classics-profile
rsync -a --exclude .git --exclude _build ./ "$tmp/"
cd "$tmp"
agda --profile=modules Constructive/Analysis/Reals.agda
```

When the symptom is high memory rather than only wall time, measure the same
cold or cached check with the platform resource tool.  On macOS:

```sh
/usr/bin/time -l agda Constructive/Analysis/Reals.agda
```

Record `maximum resident set size` with the timing.  A high RSS number without
a matching module profile is hard to interpret; collect both the module profile
and the memory measurement from the same cold/cached setup when possible.

When a module profile identifies a slow file, remove only that file's local
interface in the temporary copy and profile the file itself.  This gives a
repeatable measurement for one edit without rebuilding unrelated modules.
For unfamiliar symptoms, search GitHub issues and pull requests in
`agda/agda` and related libraries for similar performance reports,
explanations, and workarounds before inventing a local fix.  After fixing a
slow file, record the profile signal, local response, and verification in
`docs/PERFORMANCE_CASE_STUDIES.md`; leave unresolved items in
`Open Slow Files`.

## Reading Profiles

`--profile=modules` gives the cost distribution across imports.  Use it on
aggregate modules to find the few files worth investigating.

`--profile=definitions` is useful when one definition dominates.  If a single
definition accounts for most of the file time, inspect its proof shape first.

`--profile=conversion`, `--profile=constraints`, and `--profile=instances`
distinguish conversion problems from instance-search problems.  Large
`compare` counts with little instance activity usually point to conversion or
unification, not class search.

If most time is reported as `Miscellaneous`, the hot work may be in scope
checking, type signature elaboration, record/module elaboration, interface
serialization, or imported definitions rebuilt as dependencies.  In that case,
also try:

```sh
agda --profile=internal --profile=serialize --profile=sharing Foo.agda
```

Do not infer that a proof body is slow just because the file is slow.
If `Typing.TypeSig`, `InterfaceInstantiateFull`, or serialization dominates,
also try replacing a proof body by a hole in a temporary copy.  If the type
alone is slow, shrink the exposed signature before editing the proof.

If `Positivity` dominates an otherwise small module, inspect public record
declarations before proof bodies.  `record` declarations with dependent fields
can make positivity checking re-traverse large interval, locator, or series
types.  `--lossy-unification` does not address this bucket.  Good candidates
for simplification are single-field records and records that only package
proof/data evidence.  A transparent iterated `Σ` package with a small
projection module is often enough when callers do not need record syntax.

## Slow Patterns And Responses

Agda can be unexpectedly slow on otherwise small changes.  Match the profile
to one of these patterns before refactoring.

- Large module telescopes or parameterized blocks can make every definition in
  the block carry more structure than it needs.  Shrink anonymous-module
  telescopes when a profile points at many definitions inside the same block.
  Move only the parameters needed by a helper into that helper's type,
  especially universe levels, moduli, coefficients, interval endpoints, and
  record-valued structures.
- Instance search against large target types shows up in `--profile=instances`
  and constraint profiles.  Make instance arguments explicit at the use site
  instead of relying on search through a large goal.
- Conversion and unification problems usually show large `compare` counts with
  little instance activity.  Make large implicit arguments explicit around
  `subst`, `subst2`, order transport, and generic algebra lemmas.  This is
  especially important for ordered-field and ordered-ring records, where the
  inferred target can include a large record projection chain.
- `with` or `rewrite` over a large dependent target can force Agda to compare a
  large inferred motive.  Prefer direct eliminators when they express the same
  case split.  For sums, prefer named branches and `Sum.rec`:

```agda
slow p with p
... | inl x = left x
... | inr y = right y

fast p =
  Sum.rec left right p
```

- Pattern variables and holes with large inferred types can be expensive even
  before a proof is complete.  Avoid introducing unused pattern variables, and
  give large holes a smaller explicit type before asking Agda to elaborate the
  surrounding proof.
- Very large public type signatures can be the hot path even when the proof
  body is trivial.  Bind repeated projections, introduce named type aliases for
  long targets, and avoid exposing record/module projection chains in every
  local signature when a smaller equivalent signature is available.
- Long chains of public convenience wrappers can make `Typing.CheckRHS`
  dominate even when each wrapper is mathematically thin.  Keep the small
  internal combinators, but expose only entry points that are used at module
  boundaries.  If a downstream instance only needs one canonical theorem,
  implement that theorem directly from the primitive bounds instead of routing
  it through many partially specialized wrappers.
- Cubical Path/Glue comparison can dominate conversion.  Split path-heavy
  arguments into named intermediate lemmas when that gives Agda smaller
  endpoints to compare.
- Named dependent records with eta equality, nested projections,
  record-valued implicit metas, and signatures that quantify over records with
  large fields can make checking unexpectedly expensive.  `no-eta-equality`
  avoids one known cost, but it does not remove positivity or type-signature
  work.  If a record is only packaging data and proofs, try an iterated `Σ`
  type with a projection module before adding another public record.  For
  single-field records, a function type alias can be clearer and faster.  If a
  record is public or mathematically clarifies an interface, keep the record
  but make projections and parameters explicit near expensive uses.  When a
  record becomes a `Σ` package, make sure every public parameter still appears
  in the alias body.  If a parameter is needed only for the external API, keep
  a small equality anchor in the package; otherwise projection calls may leave
  hidden arguments unsolved downstream.  Expect some downstream calls to need
  explicit hidden arguments that record elaboration used to infer.
- Memory spikes usually follow the same causes as time spikes: large record
  positivity checks, big unresolved implicit metas, and conversion over large
  path or ordered-algebra targets.  Measure RSS with `/usr/bin/time -l`, then
  use module/internal profiles to find the source.  Reducing record positivity
  and shrinking large inferred targets is usually more effective than adding
  heap or waiting longer.
- Generic ordered-field and ordered-ring theorems can be too general for a
  rational-specific proof.  Avoid routing rational-specific facts through
  generic algebra when the generic theorem produces expensive conversion.  A
  direct rational proof with explicit arguments is often faster and clearer.
- Large proof bodies can hide a small hot subgoal.  Split large proofs into
  named local lemmas when it gives Agda a smaller target for each check.  Mark
  stable helper proofs `abstract` only when callers do not need their
  computational behavior.
- Solver calls should stay inside the algebraic fragments they cover.  Solver
  calls are usually not the problem here, but their surrounding `subst` targets
  can be.
- If a file-level check remains anomalously slow after the above triage, add
  `--lossy-unification` to that module's options and report that the flag was
  added.  Keep the flag local to the slow module, and verify a clean reload;
  upstream reports include cases where lossy unification interacts badly with
  instance arguments and literals.  Do not use this flag as the first response
  to a `Positivity`-dominated profile.

## When To Stop

Stop local refactoring once the touched module and the nearest aggregate
module check in normal cached mode.  Then run:

```sh
git diff --check
```

Run broader checks only when the change touches shared interfaces, module
paths, foundational definitions, or aggregate exports.

## Open Slow Files

There are no remaining anomalously slow PowerSeries files from the current
PowerSeries profiling pass.  In a cold local `PowerSeries` aggregate profile
after the `Recenter.Majorant` and finite partial-sum cleanup, the aggregate
checked in about 34.7 seconds.  The largest residual modules were
`Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Theorem` at about
5.6 seconds, `Instances.Logarithm.Global` at about 1.3 seconds,
`Recenter.StripFinite` at about 1.2 seconds, and `Radius.Centered` at about
1.1 seconds.

There are no single-file Constructive Reals outliers left from the 2026-07-08
profile on the scale of the fixed 17-42 second modules.  After the cleanup,
the cold local `Constructive.Analysis.Reals` aggregate checked in about
104 seconds and had about 2.06 GB maximum RSS.  The largest residual modules
were `Constructive.Data.Rationals.Archimedean` at about 7.2 seconds,
`Constructive.Analysis.Reals.CauchyReals.Order.Bounded` at about 5.9 seconds,
`Constructive.Analysis.Reals.Locator.Base` at about 5.7 seconds,
`Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication` at
about 4.2 seconds, and `Constructive.Data.Rationals.Bounds` at about
4.0 seconds.  These are broad foundational modules rather than isolated
proof-packaging outliers; profile them individually before applying another
structural change.

If a future aggregate profile finds another slow module, add it here with the
command used, the cold and cached timings, the dominant profile bucket, RSS if
memory is part of the symptom, and the next concrete experiment.

## Case Studies

Fixed performance case studies live in `docs/PERFORMANCE_CASE_STUDIES.md`.
Add new verified cases there; keep unresolved diagnostics in `Open Slow Files`
below.

## GitHub Matches

The upstream Agda issue tracker has several reports that match these symptoms:

- [`agda/agda#4517`](https://github.com/agda/agda/issues/4517) reports
  instance search becoming expensive when small candidates are checked against
  a huge target, with module parameters contributing to term size.  This
  supports shrinking module telescopes and making instance arguments explicit.
- [`agda/agda#7784`](https://github.com/agda/agda/issues/7784) reports a case
  where an almost identical category proof became slow before the body was
  meaningful; the type signature alone was already costly, and internal
  profiling pointed at type signatures, serialization, interface
  instantiation, and positivity.  This is the closest match for the current
  `Miscellaneous` files.
- [`agda/agda#4573`](https://github.com/agda/agda/issues/4573),
  [`agda/agda#4060`](https://github.com/agda/agda/issues/4060), and
  [`agda/agda#2228`](https://github.com/agda/agda/issues/2228) are examples
  where path-heavy or record-heavy checking improved when stable helpers were
  hidden behind `abstract` or a postulate in a reduced test.  In this repo,
  `abstract` is a local performance tool only when callers do not rely on the
  helper's computational behavior.
- [`agda/agda#6721`](https://github.com/agda/agda/issues/6721) records that
  record eta rules can be a serious performance cost.  Keep
  `no-eta-equality` on large proof/data records unless eta is needed, and make
  projections explicit near expensive uses.
- [`agda/agda#7289`](https://github.com/agda/agda/issues/7289) and
  [`agda/agda#5279`](https://github.com/agda/agda/issues/5279) are cautions
  about `--lossy-unification`: it can be essential for some slow files, but it
  should not be applied blindly, and every use should be checked by reloading
  the affected module.
- [`agda/agda#1646`](https://github.com/agda/agda/issues/1646) shows scope
  checking can blow up through module alias chains.  If an internal profile
  points at scoping, reduce nested module aliases and broad public opens before
  editing mathematical proofs.

Related upstream reports that may be useful for future triage:
[`agda/agda#8589`](https://github.com/agda/agda/issues/8589),
[`agda/agda#7975`](https://github.com/agda/agda/issues/7975),
[`agda/agda#6136`](https://github.com/agda/agda/issues/6136),
[`agda/agda#8485`](https://github.com/agda/agda/issues/8485),
[`agda/agda#5060`](https://github.com/agda/agda/issues/5060), and
[`agda/agda#4628`](https://github.com/agda/agda/issues/4628).
