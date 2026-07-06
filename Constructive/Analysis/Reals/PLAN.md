# Phase 3: Series And Elementary Bounds Plan

This plan is independent of the root constructive-analysis plan.  Its target
is Phase 3 only: a constructive series library for HoTT Cauchy reals with
explicit tail data and elementary bounds.

## Scope

Create:

- `Constructive/Analysis/Reals/Series.agda`
- `Constructive/Analysis/Reals/Series/Finite.agda`
- `Constructive/Analysis/Reals/Series/Tail.agda`
- `Constructive/Analysis/Reals/Series/Cauchy.agda`
- `Constructive/Analysis/Reals/Series/Comparison.agda`
- `Constructive/Analysis/Reals/Series/Instances/Geometric.agda`
- `Constructive/Analysis/Reals/Series/Instances/Geometric/`

The public API should cover:

- finite sums over `Fin n`;
- partial sums for `Nat -> ℝᶜ`;
- convergence from explicit tail bounds;
- a Cauchy criterion for series with a modulus;
- comparison with a modulated majorant;
- geometric-series convergence;
- a Neumann-series style inverse for `1 - x`, only if the order and reciprocal
  APIs make the proof local.

## Non-Goals

- Do not use classical compactness, excluded middle, countable choice, or
  arbitrary real trichotomy.
- Do not prove convergence from arbitrary monotone bounded partial sums.
- Do not introduce arbitrary suprema for constructive reals.
- Do not add a full sequence library unless the series proof genuinely needs
  shared sequence infrastructure.
- Do not move Phase 3 definitions into the Cauchy-real construction modules.
  Analysis-specific APIs should live under `Constructive.Analysis.Reals`.

## Starting Assumptions

The current useful infrastructure is:

- `Constructive.Analysis.Metric.Cauchy` for precision-indexed Cauchy
  approximations and limits;
- `Constructive.Analysis.Metric.Instances.CauchyReals` for Cauchy completeness
  of `ℝᶜ`;
- `Constructive.Analysis.Reals.CauchyReals.Arithmetic` for real algebra;
- `Constructive.Analysis.Reals.CauchyReals.Order.Magnitude` for `absᶜ`;
- `Constructive.Data.PositiveRationals` for precision splitting;
- `Constructive.Data.Rationals` for rational order arithmetic and
  Archimedean search.

Use these before adding local helper APIs.

## Layer 1: Finite Sums

Define finite sums over `Fin n` in `Series.agda`.

Expected definitions:

```agda
sumFin : (n : Nat) -> (Fin n -> ℝᶜ) -> ℝᶜ

partialSum : (Nat -> ℝᶜ) -> Nat -> ℝᶜ
```

The exact names should follow local conventions, but the API should support:

- zero-length sum;
- successor decomposition;
- singleton sum;
- reindexing by successor for tails;
- pointwise addition and negation;
- constant zero sequence;
- finite triangle inequality for absolute values.

Keep this layer algebraic and finite.  Do not introduce infinite reasoning in
the same definitions.

## Layer 2: Tail Bounds

State convergence through explicit tails, not through unmodulated sequence
claims.

One practical interface is:

```agda
TailBound :
  (u : Nat -> ℝᶜ) ->
  (mu : ℚ⁺ -> Nat) ->
  Type _
```

The intended meaning is that for every precision `epsilon`, all tails after
`mu epsilon` have absolute value bounded by `epsilon`.

A useful low-level form may quantify over finite tail sums:

```agda
SeriesTailBound u mu =
  (epsilon : ℚ⁺) ->
  (m k : Nat) ->
  mu epsilon <= m ->
  absᶜ (tailSum u m k) <ᶜ rational (radius epsilon)
```

Use the local order vocabulary and decide whether the bound should be strict
or non-strict after checking which real-order transfer lemmas are easiest.

## Layer 3: Cauchy Criterion

Use explicit tail bounds to construct a `CauchyApproximation` in the Cauchy
real metric.

Expected result:

```agda
seriesCauchyApproximation :
  (u : Nat -> ℝᶜ) ->
  SeriesTailBound u mu ->
  CauchyApproximation CauchyRealsMetricSpace
```

Then use `CauchyRealsIsCauchyComplete` to define the sum:

```agda
seriesSum :
  (u : Nat -> ℝᶜ) ->
  SeriesTailBound u mu ->
  ℝᶜ
```

Prove the convergence statement in terms of the same explicit tail modulus.

Expected public theorem set:

- explicit tail bound implies convergence;
- the produced sum is unique;
- changing finitely many initial terms changes the sum by the corresponding
  finite sum;
- sums respect pointwise addition when the tail moduli are combined.

## Layer 4: Comparison Test

Define a comparison interface with a modulated majorant.

Expected shape:

```agda
SeriesMajorizedBy :
  (u v : Nat -> ℝᶜ) ->
  Type _
```

The constructive version should assume explicit data such as:

- `absᶜ (u n) <= v n`;
- `0 <= v n`;
- a tail modulus for `v`.

Expected theorem:

```agda
comparisonTest :
  SeriesTailBound v mu ->
  SeriesMajorizedBy u v ->
  SeriesTailBound u mu'
```

If strict versus non-strict order causes friction, first prove a rational
epsilon-relaxed comparison theorem.

## Layer 5: Absolute Summability

Define absolute summability through an explicit tail bound on absolute-value
terms.

Expected shape:

```agda
AbsolutelySummableWith :
  (u : Nat -> ℝᶜ) ->
  (mu : ℚ⁺ -> Nat) ->
  Type _
```

Expected theorem:

```agda
absoluteSummable->summable :
  AbsolutelySummableWith u mu ->
  SeriesTailBound u mu'
```

This should use finite triangle inequalities and comparison, not monotone
convergence.

## Layer 6: Rational Geometric Series

Start `Series/Instances/Geometric/Rational.agda` with rational ratios.  This keeps the
first geometric proof in rational arithmetic, where order is decidable.

Expected definitions:

```agda
rationalPower : ℚ -> Nat -> ℚ
realRationalPower : ℚ -> Nat -> ℝᶜ
```

Expected results:

- finite geometric sum identity;
- explicit tail bound for `abs r <= rho` and `rho < 1`;
- convergence of `lambda n -> rational (rationalPower r n)`;
- identified sum when the reciprocal API is convenient.

Do not require the closed-form sum theorem before proving convergence.  The
tail-bound convergence theorem is the priority.

## Layer 7: Real Geometric Series

After the rational theorem type-checks, add a real-ratio theorem with explicit
boundedness data.

Expected assumptions:

- `x : ℝᶜ`;
- a rational `rho`;
- `0 <= rho`;
- `rho < 1`;
- `absᶜ x <= rational rho`;
- multiplication bounds sufficient to prove `absᶜ (x ^ n) <= rho ^ n`.

Expected result:

```agda
geometricSeriesConverges :
  ... ->
  SeriesTailBound (lambda n -> x ^ n) mu
```

Only add real powers if they are not already available.  Keep them local to
series until a second module needs the same API.

## Layer 8: Neumann Series

Add the Neumann-series inverse only after geometric-series convergence and
power algebra are stable.

Target:

```agda
(1ᶜ -ᶜ x) ·ᶜ seriesSum (lambda n -> x ^ n) == 1ᶜ
```

Use the local spelling for subtraction and equality.  If proving the product
with the series sum needs a large new continuity theorem for multiplication,
split that theorem into its own small milestone first.

## Implementation Order

1. Add `Series.agda` with finite sums and partial sums.
2. Prove basic finite-sum algebra and finite triangle bounds.
3. Define finite tail sums and explicit series tail bounds.
4. Construct a Cauchy approximation from tail bounds.
5. Define `seriesSum` using Cauchy completeness.
6. Prove convergence and uniqueness for `seriesSum`.
7. Add the comparison test.
8. Add absolute summability from explicit majorants.
9. Add `Series/Instances/Geometric/Rational.agda` for rational ratios.
10. Generalize geometric convergence to real ratios with explicit bounds.
11. Add the Neumann-series inverse if the supporting multiplication lemmas stay
    narrowly scoped.
12. Export stable modules from `Constructive/Analysis/Reals.agda`.

## Acceptance Criteria

- Series convergence is always backed by explicit tail data or a modulus.
- The first complete theorem does not depend on a future sequence library.
- No constructive module imports classical analysis or `Oracle`.
- No theorem assumes arbitrary suprema, arbitrary monotone convergence, or
  real trichotomy.
- Shared helpers are promoted only after a second module needs them.
- Touched modules and the nearest aggregate module type-check.
- `git diff --check` passes before reporting completion.

## Verification Targets

For finite sums and core series:

```sh
agda Constructive/Analysis/Reals/Series.agda
agda Constructive/Analysis/Reals.agda
git diff --check
```

For geometric series:

```sh
agda Constructive/Analysis/Reals/Series/Instances/Geometric.agda
agda Constructive/Analysis/Reals/Series/Instances/Geometric/Rational.agda
agda Constructive/Analysis/Reals/Series/Instances/Geometric/Positive.agda
agda Constructive/Analysis/Reals/Series/Instances/Geometric/Majorant.agda
agda Constructive/Analysis/Reals/Series/Instances/Geometric/Real.agda
agda Constructive/Analysis/Reals.agda
git diff --check
```

For aggregate exports or shared API changes:

```sh
agda --build-library
git diff --check
```
