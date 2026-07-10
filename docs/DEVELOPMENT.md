# Development Guide

This document is authoritative for contribution workflow, verification, and
temporary work plans.  Read nearby code before changing it.  Use
[Architecture](ARCHITECTURE.md) for ownership, assumption boundaries,
dependency direction, and stable public entry points; use the
[style guide](../STYLE.md) for code and prose shape.

The supported dependency setup and the shortest user-facing build command are
recorded in the [README](../README.md).

## Standard Workflow

1. Record the starting worktree state:

   ```sh
   git status --short
   ```

2. Locate the definition, its public aggregate, and its downstream users.
   Prefer `rg --files` and `rg` over browsing the tree by guesswork.
3. Read the nearby modules and the relevant boundary in
   [Architecture](ARCHITECTURE.md).  For Cauchy-real, locatedness, modulus, or
   power-series interface choices, also read
   [HoTT and Bishop Analysis Interfaces](BISHOP_ANALYSIS.md).
4. Name the smallest mathematical outcome.  For proof work, identify the hard
   theorem or proof obligation before adding helpers or wrappers.
5. Make the narrowest change that reaches that outcome.  Keep support
   declarations private until reuse or a genuine interface boundary justifies
   exporting them.
6. Run the checks selected by the verification matrix below.
7. Review the complete diff and final worktree state.  Separate pre-existing
   changes from the paths changed for the current task.

Do not count aggregate imports, namespace copies, thin aliases, `With` or
`From...` forwarding variants, argument-order shims, or solver plumbing as
theorem progress.  They are support work and are justified only when they
remove a concrete downstream proof burden.

## Public Surface Changes

Prefer the stable aggregate named in [Architecture](ARCHITECTURE.md) as the
consumer import.  Before adding a public declaration, check whether existing
infrastructure already expresses the result and search for real downstream
use.

When changing a public module path, aggregate export, assumption boundary, or
foundational definition:

- audit direct importers and old names with `rg`;
- update affected aggregates and known downstream users in the same change;
- update [Architecture](ARCHITECTURE.md) when ownership, dependency direction,
  or stable entry points change;
- update the [README](../README.md) only when the user-facing library story,
  Quick Start, or stable public entry points change; and
- run the broad checks required by the verification matrix.

A new internal file or private helper does not by itself require a README
edit. Run `scripts/check-architecture.sh` after editing the documented stable
entry points.

## Verification Matrix

Every change gets the final worktree and whitespace checks in the next
section.  Add the checks below according to the largest applicable blast
radius.

| Change | Required verification |
| --- | --- |
| Documentation | Check links and paths; render nontrivial layout. |
| Local private code | Check the touched module and, when practical, its aggregate. |
| New module or aggregate import | Check both; audit direct imports and public exports. |
| Public theorem or declaration | Check touched modules, the aggregate, and known consumers. |
| Public path, shared API, or foundation | Run targeted checks, then `agda --build-library`. |
| Deletion, migration, or rename | Apply the matching row; search for stale names and imports. |
| Performance-sensitive code or pragma | Apply the matching row and the performance runbook. |

Typical targeted commands are:

```sh
agda path/to/Touched.agda
agda path/to/NearestAggregate.agda
rg 'OldName|Old\.Namespace' Constructive Classical
rg 'postulate|\?|TODO|FIXME' path/to/touched/area
```

Do not infer that a moved module is independent merely because a broad
aggregate type-checks from cache.  Audit its direct imports and type-check the
module itself.

If a required check fails for a clearly unrelated pre-existing reason, record
the exact command and first actionable error.  Continue with narrower checks
that still validate the in-scope change; do not report the broader check as
passed.

## Complete Diff And Whitespace Checks

Before reporting completion, inspect the worktree and run the repository
checker:

```sh
git status --short
scripts/check-worktree-whitespace.sh
```

With no arguments, the script checks unstaged, staged, and untracked files
across the worktree without modifying the index. Optional arguments are Git
pathspecs, interpreted from the repository root, for a narrower check:

```sh
scripts/check-worktree-whitespace.sh -- docs README.md
```

Always review `git status --short` separately so unrelated user work is not
staged or reported as part of the change.

## Performance Triage

If Agda checking is anomalously slow, follow the
[performance runbook](performance/RUNBOOK.md) before changing proof shape,
adding `--lossy-unification`, or treating a timeout as a proof failure.

- Put resolved, reproducible investigations in
  [case studies](performance/CASE_STUDIES.md).
- Put stable timing and memory measurements in
  [baselines](performance/BASELINES.md).
- Put durable external issue, manual, and paper links in
  [references](performance/REFERENCES.md).
- Keep unresolved one-off diagnostic notes in the task's temporary work note
  or issue, not in the permanent runbook.

Report any newly added performance pragma and the evidence that made it
necessary.

## Temporary `PLAN.md` Files

`PLAN.md` files are disposable work notes, not part of the documentation tree.
Do not add them to the documentation index or create an archive for them.  A
small, local change does not need a plan.

Create a plan only when a multi-step task needs coordination or when a hard
proof target and its non-goals would otherwise be easy to lose.  Put this
header at the top:

```text
Status: Draft | Active | Blocked
Scope: <paths and mathematical area in scope>
Hard theorem target: <closed result that counts as progress>
Non-goals: <explicit exclusions>
Acceptance checks: <exact commands or observable completion criteria>
```

For a non-theorem task, write `Hard theorem target: N/A` and name the concrete
outcome under `Scope`.  For theorem work, wrappers, aliases, reexports, API
plumbing, and proof scaffolding do not satisfy the hard theorem target.

Delete the plan when the task is completed or abandoned.  Move only durable
conclusions to their authoritative home:

- ownership, dependency, and public API decisions to
  [Architecture](ARCHITECTURE.md);
- constructive-analysis interface reasoning to
  [HoTT and Bishop Analysis Interfaces](BISHOP_ANALYSIS.md);
- reusable profiling procedures and evidence to the relevant
  [performance document](performance/RUNBOOK.md); and
- local proof rationale to comments next to the code when it will help future
  readers.

Do not churn existing plan files merely to retrofit this format.

## Completion Report

Report the mathematical or user-facing outcome, not the volume of scaffolding.
List changed paths, exact checks, any public declarations kept or removed, and
remaining blockers.  Recheck `git status --short` immediately before staging
or committing, and stage explicit paths or hunks so unrelated user work stays
untouched.
