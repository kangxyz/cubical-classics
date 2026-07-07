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

When a module profile identifies a slow file, remove only that file's local
interface in the temporary copy and profile the file itself.  This gives a
repeatable measurement for one edit without rebuilding unrelated modules.
For unfamiliar symptoms, search GitHub issues and pull requests in
`agda/agda` and related libraries for similar performance reports, explanations,
and workarounds before inventing a local fix.

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
- Cubical Path/Glue comparison can dominate conversion.  Split path-heavy
  arguments into named intermediate lemmas when that gives Agda smaller
  endpoints to compare.
- Named dependent records with eta equality, nested projections,
  record-valued implicit metas, and signatures that quantify over records with
  large fields can make conversion and unification unexpectedly expensive.  If
  a record is only packaging data and proofs inside a local construction, try
  an iterated `Σ` type before introducing a public record.  If a record is
  public or mathematically clarifies an interface, keep the record but make
  projections and parameters explicit near expensive uses.
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
  instance arguments and literals.

## Case Studies

The following examples came from profiling the constructive real-analysis
stack with Agda 2.8.0.

`Constructive.Analysis.Reals.Sequences.Order` spent about 200 seconds in
`eventuallyApart-sym`.  The proof used `with u#v n N≤n` over the apartness
sum.  Replacing the `with` split by `Sum.rec inr inl (u#v n N≤n)` reduced the
file check to a few seconds.

`Constructive.Analysis.Reals.Series.Tail` spent about 28 seconds in
`tailBound-pair`.  The hot spot was `with NatOrder.splitℕ-≤ m n` over a large
boundedness target.  Rewriting it as `Sum.rec left right ...` with named branch
proofs avoided the expensive motive abstraction.

`Constructive.Analysis.Reals.PowerSeries.Base` spent about 58 seconds in
`powerSeriesConvergesFromFiniteTailBound`.  The proof is a thin wrapper around
series convergence, and the cost was conversion/unification rather than
mathematical work.  Adding `--lossy-unification` to the module reduced the
file-level check to a few seconds.

`Constructive.Data.Rationals.Archimedean` spent about 36 seconds in
`archimedean-unit-fraction` when it called the generic
`isArchimedean→isArchimedeanInv` ordered-field theorem.  A rational-specific
proof from `ℚArch.isArchimedeanℚ 1ℚ ε` avoided the generic ordered-field
conversion path.  Make the zero case and multiplicative transport arguments
explicit; otherwise Agda can leave large quotient-rational constraints.

`Constructive.Analysis.Reals.IVT.Uniform`,
`Constructive.Analysis.Reals.Interval.Extrema`, and
`Constructive.Analysis.Reals.Calculus.Derivative` showed substantial
`Miscellaneous` time in cold profiles.  These should not be refactored by
guessing at proof bodies.  First check whether the cost is record/type
signature elaboration, imports rebuilt underneath the file, or interface
serialization.

## Open Slow Files

These files still need targeted follow-up.  Treat them as a diagnostic queue,
not as known proof failures.

- `Constructive.Analysis.Reals.IVT.Uniform` checked at about 52 seconds in a
  cold local profile, mostly under `Miscellaneous`.  The file is small, so the
  likely next target is its public record/type surface or imported interval and
  locator stack.  Profile it with `--profile=internal --profile=serialize
  --profile=sharing`; if `Typing.TypeSig` is visible, try a temporary variant
  with the `IVTFunctionData` fields expressed as a local `Σ` package or with
  narrower imports.
- `Constructive.Analysis.Reals.Interval.Extrema` checked at about 73 seconds
  even with `--lossy-unification`; only a small fraction of the time was
  attributed to `finiteMaximumFromSeed`.  Do not spend the next pass on the
  finite-search recursion first.  Instead test whether repeated
  `ImageFiniteNet.size imageNet` and `ImageFiniteNet.center imageNet`
  projections in local signatures are forcing large record comparisons.  A
  scratch variant should bind the size and center data once, then re-profile.
- `Constructive.Analysis.Reals.Calculus.Derivative` checked at about 27
  seconds and did not improve from `--lossy-unification` in the scratch copy.
  The module is mostly public derivative data.  The next useful experiment is
  to profile type signatures and record elaboration, then decide whether the
  public records should stay as records with smaller field aliases or whether
  any purely local packaging can be a `Σ` type.
- `Constructive.Analysis.Reals.Series.Comparison` still checked at about 36
  seconds after the `Series.Tail` hot spot was fixed.  Since this module
  already has `--lossy-unification`, the next pass should look for expensive
  public signatures, imported tail/finite-series interfaces, and record
  projection chains around `SeriesMajorizedBy` before changing proof bodies.

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

## When To Stop

Stop local refactoring once the touched module and the nearest aggregate
module check in normal cached mode.  Then run:

```sh
git diff --check
```

Run broader checks only when the change touches shared interfaces, module
paths, foundational definitions, or aggregate exports.

## Upstream References

- [`agda/agda#4517`](https://github.com/agda/agda/issues/4517)
- [`agda/agda#7784`](https://github.com/agda/agda/issues/7784)
- [`agda/agda#4573`](https://github.com/agda/agda/issues/4573)
- [`agda/agda#8589`](https://github.com/agda/agda/issues/8589)
- [`agda/agda#7975`](https://github.com/agda/agda/issues/7975)
- [`agda/agda#6136`](https://github.com/agda/agda/issues/6136)
- [`agda/agda#8485`](https://github.com/agda/agda/issues/8485)
- [`agda/agda#6721`](https://github.com/agda/agda/issues/6721)
- [`agda/agda#7289`](https://github.com/agda/agda/issues/7289)
- [`agda/agda#5279`](https://github.com/agda/agda/issues/5279)
- [`agda/agda#1646`](https://github.com/agda/agda/issues/1646)
- [`agda/agda#4060`](https://github.com/agda/agda/issues/4060)
- [`agda/agda#2228`](https://github.com/agda/agda/issues/2228)
- [`agda/agda#5060`](https://github.com/agda/agda/issues/5060)
- [`agda/agda#4628`](https://github.com/agda/agda/issues/4628)
