# Documentation

This directory contains the stable documentation for `cubical-classics`.
Choose an entry by task rather than reading the documents in filename order.

## Start By Task

| I want to… | Start here | Continue with |
| --- | --- | --- |
| Install or try the library | [Project README](../README.md#quick-start) | [Stable entry points](../README.md#stable-entry-points) |
| Find the right module to import | [Architecture](ARCHITECTURE.md#stable-public-entry-points) | [Standard workflow](DEVELOPMENT.md#standard-workflow) |
| Understand constructive versus classical assumptions | [Architecture](ARCHITECTURE.md#assumption-boundary) | [HoTT and Bishop interfaces](BISHOP_ANALYSIS.md) |
| Contribute a proof or module | [Development guide](DEVELOPMENT.md) | [Style guide](../STYLE.md) |
| Diagnose a slow Agda check | [Performance runbook](performance/RUNBOOK.md) | [Case studies](performance/CASE_STUDIES.md) and [baselines](performance/BASELINES.md) |
| Check performance sources and terminology | [Performance references](performance/REFERENCES.md) | [Performance runbook](performance/RUNBOOK.md) |
| Run an automated agent | [Agent rules](../AGENTS.md) | [Development guide](DEVELOPMENT.md) and [style guide](../STYLE.md) |

## Document Responsibilities

- The [project README](../README.md) is the user-facing overview, reproducible
  quick start, and short list of stable entry points.
- [Architecture](ARCHITECTURE.md) owns assumption boundaries, dependency
  direction, completion boundaries, and the distinction between public
  aggregates and implementation modules.
- [Development](DEVELOPMENT.md) owns contribution workflow, public-surface
  changes, verification, completion reporting, and temporary-plan rules.
- The [style guide](../STYLE.md) owns naming, imports, module shape, comments,
  proof-code style, and documentation conventions.
- [Agent rules](../AGENTS.md) contain only instructions specific to automated
  work in this repository.
- [HoTT and Bishop analysis interfaces](BISHOP_ANALYSIS.md) explain the design
  distinction between bare Cauchy-real data, located data, explicit rational
  moduli, and truncated continuity.
- The [performance runbook](performance/RUNBOOK.md) owns active diagnostic
  procedures. [Case studies](performance/CASE_STUDIES.md) record resolved
  incidents, [baselines](performance/BASELINES.md) record measurements, and
  [references](performance/REFERENCES.md) record external sources.

## Sources Of Truth

The Agda source is authoritative for theorem statements and exports. In
particular, an aggregate's `open import … public` declarations determine what it
reexports; the architecture guide is a maintained map, not a substitute for
checking the module.

[`classics.agda-lib`](../classics.agda-lib) is authoritative for library
dependencies and project-wide Agda flags. The documents above are authoritative
only for the responsibilities assigned to them in this index.

Files named `PLAN.md` are temporary working notes. They are not stable
documentation or authoritative descriptions of the current API; when a plan
and checked code differ, the checked code and the documents above govern.
