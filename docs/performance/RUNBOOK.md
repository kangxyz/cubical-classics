# Agda Performance Runbook

This runbook records the stable performance-triage workflow for this
repository. Use it before changing proof shape because a local Agda check is
unexpectedly slow.

Related records are kept separately:

- [Case studies](CASE_STUDIES.md) contain understood and verified fixes.
- [Baselines](BASELINES.md) contain current measurements and open diagnostics.
- [References](REFERENCES.md) contain relevant upstream Agda reports.

## Quick Workflow

1. Reproduce the check with the cached regression recipe below.
2. Run a cold local aggregate profile to find the few modules worth
   investigating.
3. If the aggregate identifies one slow file, run an isolated target profile
   after removing only that file's copied interface.
4. Choose `--profile=definitions`, `--profile=internal`, or
   `--profile=conversion --profile=constraints --profile=instances` based on
   the symptom.
5. Match the dominant bucket against `Slow Patterns And Responses` before
   refactoring proof shape.
6. Compare before and after timings from the same cached or cold setup.
7. Type-check the touched module and nearest aggregate when practical, run the
   repository diff checks, and update the appropriate performance record.

## Measurement Recipes

Cached checks, cold local aggregate profiles, and isolated target profiles
answer different questions. Do not use one mode for the before measurement
and another mode for the after measurement.

### Cached Regression Check

Use this first to reproduce the user-visible cost with existing local and
external interfaces:

```sh
agda Foo.agda
```

If a module profile is needed for that same recheck, run the profiled form
instead of first regenerating the target interface:

```sh
agda --profile=modules Foo.agda
```

This recipe answers whether the current working tree still exhibits the
regression under normal incremental development. Here, cached refers primarily
to valid dependency interfaces; `Foo.agda` should be newer than its interface
or otherwise require checking. If Agda immediately reuses `Foo.agdai`, use the
isolated target recipe instead of treating the near-zero result as a module
measurement.

When memory rather than wall time is the symptom, run the same cached check
with the platform resource tool. On macOS:

```sh
/usr/bin/time -l agda Foo.agda
```

Record `maximum resident set size` together with the timing and profile mode.
A high RSS number without a matching module profile is hard to interpret.

### Cold Local Aggregate Profile

Use this recipe to identify which repository modules dominate an aggregate
when repository interfaces are absent but external Cubical interfaces remain
available. Run it from the repository root:

```sh
repo=$PWD
tmp=$(mktemp -d "${TMPDIR:-/tmp}/cubical-classics-profile.XXXXXX")
rsync -a --exclude .git --exclude _build "$repo/" "$tmp/"
(
  cd "$tmp"
  agda --profile=modules Constructive/Analysis/Reals.agda
)
```

`mktemp -d` gives each run a fresh directory. Because the destination is new,
the copy does not need `rsync --delete`; this avoids deleting unrelated files
and permits concurrent profiling runs. Excluding the repository `_build`
directory makes local modules cold. The Agda library configuration remains
the one from the invoking environment, so external library interfaces can
still be reused.

Record the aggregate command, date, Agda and Cubical revisions, machine, wall
time, RSS when relevant, and the largest module-profile entries in
[Baselines](BASELINES.md).

### Isolated Target Profile

Use this recipe after a module profile points at one slow local file. It copies
the current local interfaces, removes only the target interface in the fresh
copy, and profiles a single recheck without rebuilding unrelated modules:

```sh
repo=$PWD
tmp=$(mktemp -d "${TMPDIR:-/tmp}/cubical-classics-profile.XXXXXX")
target=Constructive/Analysis/Reals/PowerSeries/Base
rsync -a --exclude .git "$repo/" "$tmp/"
find "$tmp/_build" -type f -path "*/agda/$target.agdai" -delete
(
  cd "$tmp"
  agda --profile=definitions "$target.agda"
)
```

The `find` expression is deliberately scoped to the copied `_build` tree and
the exact target path. Confirm that it identifies the intended interface when
adapting the recipe. This setup is an isolated target recheck, not a cold
aggregate: dependency interfaces remain present in the temporary copy.

Choose the file-level profile by symptom:

```sh
agda --profile=definitions Foo.agda
agda --profile=conversion --profile=constraints --profile=instances Foo.agda
agda --profile=internal --profile=serialize --profile=sharing Foo.agda
```

Avoid `--ignore-interfaces` on an aggregate unless dependency rebuild cost is
the object of the investigation. It rechecks Cubical and the whole imported
analysis stack, which can hide the local problem.

## Reading Profiles

`--profile=modules` gives the cost distribution across imports. Use it on
aggregate modules to find the few files worth investigating.

`--profile=definitions` is useful when one definition dominates. If a single
definition accounts for most of the file time, inspect its proof shape first.

`--profile=conversion`, `--profile=constraints`, and `--profile=instances`
distinguish conversion problems from instance-search problems. Large
`compare` counts with little instance activity usually point to conversion or
unification, not class search.

If most time is reported as `Miscellaneous`, the hot work may be in scope
checking, type signature elaboration, record/module elaboration, interface
serialization, or imported definitions rebuilt as dependencies. In that
case, also try:

```sh
agda --profile=internal --profile=serialize --profile=sharing Foo.agda
```

Do not infer that a proof body is slow just because the file is slow. If
`Typing.TypeSig`, `InterfaceInstantiateFull`, or serialization dominates, try
replacing a proof body by a hole in a temporary copy. If the type alone is
slow, shrink the exposed signature before editing the proof.

If `Positivity` dominates an otherwise small module, inspect public record
declarations before proof bodies. `record` declarations with dependent fields
can make positivity checking re-traverse large interval, locator, or series
types. `--lossy-unification` does not address this bucket. Good candidates for
simplification are single-field records and records that only package
proof/data evidence. A transparent iterated `Σ` package with a small projection
module is often enough when callers do not need record syntax.

## Slow Patterns And Responses

Agda can be unexpectedly slow on otherwise small changes. Match the profile
to one of these patterns before refactoring.

### Definitions And RHS

- Large module telescopes or parameterized blocks can make every definition in
  the block carry more structure than it needs. Shrink anonymous-module
  telescopes when a profile points at many definitions inside the same block.
  Move only the parameters needed by a helper into that helper's type,
  especially universe levels, moduli, coefficients, interval endpoints, and
  record-valued structures.
- Pattern variables and holes with large inferred types can be expensive even
  before a proof is complete. Avoid introducing unused pattern variables, and
  give large holes a smaller explicit type before asking Agda to elaborate the
  surrounding proof.
- Long chains of public convenience wrappers can make `Typing.CheckRHS`
  dominate even when each wrapper is mathematically thin. Keep the small
  internal combinators, but expose only entry points used at module
  boundaries. If a downstream instance only needs one canonical theorem,
  implement it directly from the primitive bounds instead of routing it
  through many partially specialized wrappers.
- Large proof bodies can hide a small hot subgoal. Split large proofs into
  named local lemmas when it gives Agda a smaller target for each check. Mark
  stable helper proofs `abstract` only when callers do not need their
  computational behavior.

### Conversion And Constraints

- Conversion and unification problems usually show large `compare` counts
  with little instance activity. Make large implicit arguments explicit around
  `subst`, `subst2`, order transport, and generic algebra lemmas. This is
  especially important for ordered-field and ordered-ring records, where the
  inferred target can include a large record projection chain.
- `with` or `rewrite` over a large dependent target can force Agda to compare
  a large inferred motive. Prefer direct eliminators when they express the
  same case split. For sums, prefer named branches and `Sum.rec`:

  ```agda
  slow p with p
  ... | inl x = left x
  ... | inr y = right y

  fast p =
    Sum.rec left right p
  ```

- Cubical Path/Glue comparison can dominate conversion. Split path-heavy
  arguments into named intermediate lemmas when that gives Agda smaller
  endpoints to compare.
- Generic ordered-field and ordered-ring theorems can be too general for a
  rational-specific proof. Avoid routing rational-specific facts through
  generic algebra when the generic theorem produces expensive conversion. A
  direct rational proof with explicit arguments is often faster and clearer.
- Solver calls should stay inside the algebraic fragments they cover. Solver
  calls are usually not the problem here, but their surrounding `subst`
  targets can be.

### Instances

- Instance search against large target types shows up in
  `--profile=instances` and constraint profiles. Make instance arguments
  explicit at the use site instead of relying on search through a large goal.

### Type Signatures, Records, And Positivity

- Very large public type signatures can be the hot path even when the proof
  body is trivial. Bind repeated projections, introduce named type aliases for
  long targets, and avoid exposing record/module projection chains in every
  local signature when a smaller equivalent signature is available.
- Named dependent records with eta equality, nested projections, record-valued
  implicit metas, and signatures that quantify over records with large fields
  can make checking unexpectedly expensive. `no-eta-equality` avoids one
  known cost, but it does not remove positivity or type-signature work. If a
  record is only packaging data and proofs, try an iterated `Σ` type with a
  projection module before adding another public record. For single-field
  records, a function type alias can be clearer and faster. If a record is
  public or mathematically clarifies an interface, keep it but make projections
  and parameters explicit near expensive uses. When a record becomes a `Σ`
  package, make sure every public parameter still appears in the alias body.
  If a parameter is needed only for the external API, keep a small equality
  anchor in the package; otherwise projection calls may leave hidden arguments
  unsolved downstream. Expect some downstream calls to need explicit hidden
  arguments that record elaboration used to infer.

### Memory

- Memory spikes usually follow the same causes as time spikes: large record
  positivity checks, big unresolved implicit metas, and conversion over large
  path or ordered-algebra targets. Measure RSS with `/usr/bin/time -l`, then
  use module/internal profiles to find the source. Reducing record positivity
  and shrinking large inferred targets is usually more effective than adding
  heap or waiting longer.

### Repository Policy For Lossy Unification

`--lossy-unification` is already a common local policy in parts of this
repository, especially the PowerSeries subtree. Existing use is not by itself
an anomaly to remove during unrelated work, and a regression in such a module
still needs normal profiling before its cause is inferred.

For a module that does not already enable the option, add it only when the
same-setup evidence shows conversion or unification pressure remains after
smaller targets, explicit arguments, and local proof-shape fixes have been
considered. In particular, do not use it as a response to a
`Positivity`-dominated profile.

When adding the option:

1. Record the command, before/after measurements, and dominant profile bucket.
2. Keep the option local to the affected module unless a documented subtree
   policy deliberately says otherwise.
3. Reload the affected module from a copied interface-free target check and
   type-check the nearest aggregate in normal cached mode.
4. Record the verified result in [Case studies](CASE_STUDIES.md).

Upstream reports include cases where lossy unification interacts badly with
instance arguments and literals, so a faster first check is not sufficient
evidence by itself.

## Recording Results

For unfamiliar symptoms, search GitHub issues and pull requests in
`agda/agda` and related libraries before inventing a local fix. Add an upstream
match to [References](REFERENCES.md) only when it explains a reusable local
symptom or workaround.

After a slow file is understood and fixed, record the profile signal, local
response, before/after setup, and verification in
[Case studies](CASE_STUDIES.md). Keep unresolved items in the `Open
Diagnostics` section of [Baselines](BASELINES.md). If triage reveals a
reusable slow pattern or response not covered above, update this runbook in
the same change.

## When To Stop

Stop local refactoring once the touched module and nearest aggregate check in
normal cached mode. Run the repository's documented verification matrix. At a
minimum, inspect the worktree and run the complete whitespace check:

```sh
git status --short
scripts/check-worktree-whitespace.sh
```

The [development guide](../DEVELOPMENT.md#complete-diff-and-whitespace-checks)
owns the checker details and path-scoping rules. Run broader Agda checks only
when the change touches shared interfaces, module paths, foundational
definitions, or aggregate exports.
