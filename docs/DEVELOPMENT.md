# Development Guide

This document is a compact map for contributors and agents.  It does not
replace reading the modules near the change.  Use it to find the right entry
point, keep assumptions on the correct side of a boundary, and choose the
right checks before reporting work as done.

## First Checks

- Check the worktree before editing:

  ```sh
  git status --short
  ```

- Search with `rg` and read nearby modules before changing code.
- Preserve user changes in the worktree.  Do not revert, delete, stage, or
  commit unrelated files.
- Follow `STYLE.md` for names, comments, documentation tone, and module
  organization.

## Type Checking

The known dependency setup is recorded in `README.md`.  The project tracks a
recent development checkout of the Cubical Agda library, not the latest tagged
release.

Useful checks:

```sh
agda Constructive/Analysis/Metric.agda
agda Constructive/Analysis/Reals.agda
agda --build-library
git diff --check
```

For a narrow change, type-check the module touched and the nearest aggregate
module when practical.  Run `agda --build-library` for changes to shared
interfaces, public module paths, foundational definitions, or aggregate
exports.  Always run `git diff --check` before reporting completion.

## Boundaries

- `Constructive/` is for code that does not use the library's classical
  `Oracle`.  Do not import classical modules into constructive modules unless
  the boundary is being deliberately redesigned and documented.
- `Classical/` may use `Oracle`, excluded middle, choice, resizing, and
  powerset-style classical interfaces.  Keep those assumptions explicit in the
  module context or exported theorem.
- `Constructive/Foundations/Powerset` is predicative support for constructive
  cuts and order-completeness notions.  `Classical/Foundations/Powerset` is the
  impredicative classical development.
- Do not replace one notion with a stronger or weaker one without checking the
  surrounding module.  This matters especially for locatedness, apartness,
  trichotomy, MacNeille completeness, Cauchy completeness, and interval
  compactness.

## Main Entry Points

- `Constructive.Analysis.Completions.CauchyCompletion` is the generic
  HoTT-style completion interface.
- `Constructive.Analysis.Reals.CauchyReals` is the rational Cauchy-real
  instance and public construction/algebra/order interface.
- `Constructive.Analysis.Completions.DedekindCompletion` is the generic
  constructive two-sided located-cut completion.
- `Constructive.Analysis.Reals.DedekindReals` is the rational instance of the
  constructive Dedekind completion.
- `Constructive.Analysis.Metric` owns the precision-indexed metric interface,
  Cauchy approximations, maps, and total boundedness support.
- `Classical.DedekindCut` is the Oracle-based cut completion of an
  Archimedean ordered field.
- `Classical.Analysis.Real` and `Classical.Analysis.Function` contain the
  classical real-analysis results, including exact compactness and IVT-style
  theorems.

Prefer aggregate modules as public entry points.  When adding or moving a
public module, update imports, aggregate modules, and `README.md` in the same
change.

## Constructive Analysis Conventions

- Use explicit positive-rational precision data for constructive analysis:
  moduli of continuity, moduli of convergence, finite nets, and approximate
  conclusions.
- Keep exact classical claims in `Classical/Analysis`.  Do not move exact IVT,
  arbitrary Bolzano-Weierstrass, arbitrary suprema, or pointwise-continuity
  compactness principles into `Constructive/Analysis` without adding the
  necessary assumptions.
- Generic metric notions belong under `Constructive/Analysis/Metric`.
  Real-specific interval, locator, sequence, and IVT material belongs under
  `Constructive/Analysis/Reals`.
- The Cauchy-real construction should not absorb analysis-specific APIs unless
  they are part of the construction, algebra, order, or generic completion
  interface.

## Proof Engineering

- Reuse existing infrastructure before adding local helper APIs.
- Avoid thin aliases that merely rename an existing definition.
- Promote a helper only when it clarifies a repeated pattern or a real public
  interface boundary.
- Prefer explicit qualification over import-order fixes when names collide.
- Use solvers only for the fragments they cover, and leave the remaining
  reasoning explicit.
- Check universe levels and implicit arguments early in generic modules.

## Common Pitfalls

- The constructive and classical real developments are related but separate.
  A theorem true under `Oracle` is not automatically a constructive theorem.
- Precision-indexed Cauchy completeness is not the same statement as
  completeness for arbitrary unmodulated `Nat`-indexed Cauchy sequences.
- Located cuts, lower/upper predicates, order-apartness, and trichotomy carry
  different assumptions.  Match the local vocabulary before reusing a lemma.
- A module path in the tree is not public just because the file exists.  Check
  the aggregate module before using it as a public dependency.
- If a new result changes the public story of constructive or classical
  analysis, update `README.md`.
