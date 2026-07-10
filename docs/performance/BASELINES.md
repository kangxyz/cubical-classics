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
  - `Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.Global`:
    about 11.3 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Radius.Centered`: about
    9.0 seconds
  - `Constructive.Analysis.Reals.Series.Instances.Geometric.Positive`:
    about 7.8 seconds
  - `Constructive.Data.Rationals.Archimedean`: about 7.1 seconds
  - `Constructive.Analysis.Reals.Locator.Base`: about 5.7 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.GlobalDerivative`:
    about 5.6 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.QuotientDerivative`:
    about 5.4 seconds
  - `Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision`:
    about 5.1 seconds
- **Status:** no confirmed whole-`Constructive` proof-packaging or positivity
  outlier remains. `Constructive.Analysis.Reals.PowerSeries.Radius.Sum`,
  which dominated the prior whole-`Constructive` profile at about 58.1
  seconds, is now about 228 milliseconds.

### PowerSeries Aggregate

- **Date:** 2026-07-10
- **Repository state:** working tree after the PowerSeries RHS cleanup
  described in [case studies](CASE_STUDIES.md)
- **Agda:** 2.8.0; `--profile=modules`
- **Cubical:** unknown (not recorded)
- **Environment:** macOS local sandbox; CPU and memory not recorded
- **Recipe:** cold local aggregate profile
- **Command:** fresh temporary copy via the runbook recipe, then
  `agda --profile=modules Constructive/Analysis/Reals/PowerSeries.agda`
- **Result:** about 99.8 seconds; RSS not recorded
- **Profile signal:**
  - `Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Theorem`:
    about 4.1 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.GlobalDerivative`:
    about 3.6 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.QuotientDerivative`:
    about 3.4 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.GlobalAnalytic`:
    about 2.9 seconds
  - `Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.LogOnePlusGlobal`:
    about 1.0 seconds
- **Status:** no confirmed anomalously slow PowerSeries files remain. The
  residual PowerSeries costs are RHS/reflection-heavy proof bridges, not
  positivity or record-packaging outliers.

### Constructive Reals Aggregate

- **Date:** 2026-07-08
- **Repository state:** after the constructive real-analysis performance
  cleanup described in [case studies](CASE_STUDIES.md)
- **Agda:** 2.8.0; additional options not recorded
- **Cubical:** unknown (not recorded)
- **Environment:** machine details unknown; maximum RSS was measured on macOS
- **Recipe:** cold local aggregate profile, with a matching cold resource run
- **Command:** `agda --profile=modules Constructive/Analysis/Reals.agda` for
  the module profile and
  `/usr/bin/time -l agda Constructive/Analysis/Reals.agda` for the resource
  run; the exact temporary-copy command was not recorded
- **Result:** about 104 seconds in the module profile and about 106 seconds in
  the resource run; `2061697024` bytes (about 2.06 GB) maximum RSS
- **Profile signal:**
  - `Constructive.Data.Rationals.Archimedean`: about 7.2 seconds
  - `Constructive.Analysis.Reals.CauchyReals.Order.Bounded`: about 5.9 seconds
  - `Constructive.Analysis.Reals.Locator.Base`: about 5.7 seconds
  - `Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication`:
    about 4.2 seconds
  - `Constructive.Data.Rationals.Bounds`: about 4.0 seconds
- **Status:** no single-file Constructive Reals outlier remained on the scale
  of the fixed 17-42 second modules

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
