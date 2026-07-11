# Agda Performance Baselines

This document records the current repository-level performance measurements
and unresolved diagnostics. It is a diagnostic snapshot, not a promise that
future runs will reproduce the same wall time on different hardware or
revisions.

Use the recipes in [the runbook](RUNBOOK.md) so before and after measurements
use the same cache state. Move understood, fixed cases to
[case studies](CASE_STUDIES.md).

## Measurement Record

Every new or updated baseline should include these fields:

- **Date:** ISO date of the measurement.
- **Repository state:** commit when clean, or a short description of relevant
  worktree changes.
- **Agda:** version and important command-line options.
- **Cubical:** revision or library-registration state.
- **Environment:** OS, architecture, CPU, memory, and other material limits.
- **Recipe:** cached regression, cold local aggregate, or isolated target.
- **Command:** exact command measured.
- **Result:** wall time and maximum RSS when memory is relevant.
- **Profile signal:** largest modules or dominant internal buckets.
- **Status:** current baseline or open diagnostic, with the next experiment.

Use `unknown (not recorded)` for missing historical metadata; do not infer it.
Do not compare numbers from different recipes as if they were the same
benchmark.

## Update Rules

- Repeat a before and after measurement with the same recipe, tool versions,
  machine, and relevant worktree state.
- Keep only the latest representative aggregate snapshot in `Current
  Baselines`; retain material historical changes in a dated case study.
- Put a residual module in `Open Diagnostics` only when there is a concrete
  symptom and next experiment. A merely largest module is not automatically a
  regression.
- When an open diagnostic is understood and fixed, remove it from this file
  and add a verified entry to [case studies](CASE_STUDIES.md).
- Update this file in the same change that intentionally establishes a new
  repository baseline.

## Current Baselines

### Whole Constructive Aggregate

- **Date:** 2026-07-10
- **Repository state:** working tree after the whole-`Constructive`
  proof-packaging cleanup described in [case studies](CASE_STUDIES.md)
- **Agda:** 2.8.0; `--profile=modules`
- **Cubical:** unknown (library registration from the invoking environment)
- **Environment:** macOS Darwin 25.5.0 arm64 local sandbox; CPU and memory not
  recorded
- **Recipe:** cold local aggregate profile over every repository module under
  `Constructive`
- **Command:** fresh temporary copy via the runbook recipe, generate
  `ConstructiveAllProfile.agda` importing every `Constructive/**/*.agda`, then
  `agda --profile=modules ConstructiveAllProfile.agda`
- **Result:** about 183.2 seconds; RSS not recorded. A matching
  `/usr/bin/time -l agda ConstructiveAllProfile.agda` resource attempt
  completed in about 186.6 seconds, but the sandbox rejected the resource
  query with `sysctl kern.clockrate: Operation not permitted`.
- **Profile signal:**
  - `Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.Global`:
    about 11.3 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Radius.Centered`: about
    9.0 seconds
  - `Constructive.Analysis.Reals.Series.Geometric.Positive`:
    about 7.8 seconds
  - `Constructive.Data.Rationals.Archimedean`: about 7.1 seconds
  - `Constructive.Analysis.Reals.Locator`: about 5.7 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation.GlobalDerivative`:
    about 5.6 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation.QuotientDerivative`:
    about 5.4 seconds
  - `Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision`:
    about 5.1 seconds
- **Status:** no confirmed whole-`Constructive` proof-packaging or positivity
  outlier remains. `Constructive.Analysis.Reals.PowerSeries.Convergence`,
  which dominated the prior whole-`Constructive` profile at about 58.1
  seconds, is now about 228 milliseconds.

### PowerSeries Aggregate

- **Date:** 2026-07-11
- **Repository state:** commit `0c622dfa` plus the uncommitted constructive
  Analysis consolidation described in [case studies](CASE_STUDIES.md)
- **Agda:** 2.8.0; `--profile=modules`
- **Cubical:** library registration from the invoking environment; revision
  not recorded
- **Environment:** macOS Darwin 25.5.0 arm64 local sandbox; CPU and memory not
  recorded
- **Recipe:** cold local aggregate profile
- **Command:** fresh temporary copy via the runbook recipe, then
  `agda --profile=modules Constructive/Analysis/Reals/PowerSeries.agda`
- **Result:** Agda total 135.529 seconds; wall 137.58 seconds; RSS not recorded
- **Profile signal:**
  - `Constructive.Analysis.Reals.PowerSeries.Radius.Centered`: about
    9.8 seconds
  - `Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision`:
    about 8.5 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Recenter.Coefficients`: about
    5.2 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation.GlobalDerivative`:
    about 5.3 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation.Algebra`:
    about 4.6 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation.QuotientDerivative`:
    about 4.9 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Differentiation.Limit`:
    about 4.8 seconds
- **Status:** the same-machine Phase 0 baseline was Agda total 151.347 seconds
  and wall 153.55 seconds, so this run is about 10.5% faster. Repeated cold
  runs on the nearly final tree ranged from 153.024 to 135.529 seconds, so the
  result establishes no regression but is not evidence for attributing the
  full difference to one source change. The older 99.8-second snapshot used a
  different repository state and is retained in
  [case studies](CASE_STUDIES.md), not treated as a like-for-like threshold.
  No positivity or record-packaging outlier reappeared.

### Constructive Reals Aggregate

- **Date:** 2026-07-11
- **Repository state:** commit `0c622dfa` plus the uncommitted constructive
  Analysis consolidation described in [case studies](CASE_STUDIES.md)
- **Agda:** 2.8.0; `--profile=modules`
- **Cubical:** library registration from the invoking environment; revision
  not recorded
- **Environment:** macOS Darwin 25.5.0 arm64 local sandbox; CPU and memory not
  recorded
- **Recipe:** cold local aggregate profile
- **Command:** fresh temporary copy via the runbook recipe, then
  `agda --profile=modules Constructive/Analysis/Reals.agda`
- **Result:** Agda total 103.201 seconds; wall 104.55 seconds; RSS not recorded
- **Profile signal:**
  - `Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision`:
    about 8.3 seconds
  - `Constructive.Data.Rationals.Archimedean`: about 6.9 seconds
  - `Constructive.Analysis.Reals.Locator`: about 6.1 seconds
  - `Constructive.Analysis.Reals.Series.Geometric.Real`: about 5.3 seconds
  - `Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication`:
    about 4.3 seconds
  - `Constructive.Data.Rationals.Bounds`: about 3.8 seconds
- **Status:** the same-machine Phase 0 baseline was Agda total 116.446 seconds
  and wall 118.18 seconds, so this run is about 11.4% faster. A preceding run
  on the nearly final tree reported 116.390 seconds, confirming substantial
  cold-run variance; use the result as a no-regression signal rather than a
  precise speedup claim. The older approximately 104-second snapshot had
  incomplete environment and temporary-copy metadata. No single-file outlier
  remains on the scale of the fixed 17-42 second modules.

## Open Diagnostics

There are no confirmed anomalously slow files recorded at present.

The largest residual modules in the 2026-07-10 whole-`Constructive` baseline
are broad foundational modules or path-heavy bridge modules rather than an
isolated proof-packaging outlier. Do not apply another structural change from
aggregate rank alone. If one becomes a practical regression, profile it
individually and record the exact symptom before choosing a response.

Add a future diagnostic here only with:

- the measurement fields above;
- the user-visible symptom or regression threshold;
- the dominant profile bucket;
- the smallest next experiment; and
- the condition that will count as resolved.
