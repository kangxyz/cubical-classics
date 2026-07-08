# Phase 5: Derivative Is Analytic

## Summary

Phase 5 proves that the derivative model of a power-series function is itself
analytic on strict subballs.  This is stronger than Phase 4, which only proves
`HasDerivativeAtWith` at a chosen point.

The phase should not start with a naked
`HasPowerSeriesAtWith -> derivative analytic` theorem.  The first closed target
is the data-rich, constructive theorem:

```agda
PowerSeriesMajorizedOnBall a σ v ν →
BoundedByᶜ δ d →
radius (δ +⁺ τ) < radius σ →
HasPowerSeriesOnBallWith (recenterPowerSeries a d) τ μ
```

After this re-centering theorem exists, apply it to `derivativePowerSeries a`
and transport the centered-sum function equality through the local expansion.

## External References Checked

- Mathlib `Analysis.Analytic.Basic` defines `HasFPowerSeriesOnBall`,
  `HasFPowerSeriesAt`, and `AnalyticAt` by a formal series plus convergence on a
  ball or some positive-radius ball:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/Basic.html
- Mathlib `Analysis.Calculus.FDeriv.Analytic` proves derivative consequences
  including `HasFPowerSeriesOnBall.fderiv`, `AnalyticAt.fderiv`, and notes that
  derivative-on-ball results need completeness away from the expansion center:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Analytic.html
- Mathlib's implementation uses `p.changeOrigin` and `p.derivSeries` for
  derivative power-series results.  The mature pattern is: prove re-centering
  for formal series first, then derivative analyticity is a short theorem.
- Mathlib `Analysis.Analytic.Composition` is a scope warning.  Composition and
  origin-change are mostly summability and coefficient-reindexing work:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/Composition.html
- CoRN remains the constructive real-analysis reference point.  Its design
  supports the same local rule used here: carry constructive data explicitly
  rather than hiding it behind classical existence:
  https://github.com/rocq-community/corn
- O'Connor's exact-real work and Krebbers-Spitters' exact-real work support the
  engineering choice that elementary analytic functions should carry moduli,
  approximants, and correctness data explicitly:
  https://arxiv.org/abs/0805.2438
  https://arxiv.org/abs/1105.2751

## Local Design Lesson

Mathlib can use topological balls, `HasSum`, and completeness instances.  This
repository uses rational moduli and Cauchy reals.  Therefore the local theorem
must expose the strict radius margin as rational data and build explicit tail
moduli.

Use this split:

- Phase 5A: re-center a power series on a strict subball.
- Phase 5B: prove the derivative model is analytic by applying Phase 5A to
  `derivativePowerSeries a`.
- Phase 5C: transport the result from the centered derivative model to the
  derivative function obtained in Phase 4.
- Phase 5D: add instance-level wrappers only after the generic theorem checks.

Do not implement composition, inverse functions, or general analytic-on-open-set
APIs in this phase.

## Main Theorem Targets

### Re-centering definitions

New module cluster:

```text
Constructive/Analysis/Reals/PowerSeries/Recenter.agda
Constructive/Analysis/Reals/PowerSeries/Recenter/Base.agda
Constructive/Analysis/Reals/PowerSeries/Recenter/Binomial.agda
Constructive/Analysis/Reals/PowerSeries/Recenter/Majorant.agda
Constructive/Analysis/Reals/PowerSeries/Recenter/Theorem.agda
```

Public definitions:

```agda
recenterPowerSeries :
  PowerSeries →
  ℝᶜ →
  PowerSeries
```

Intended coefficient:

```text
recenterPowerSeries a d n =
  Σ_{k≥0} binomial (n+k) n * a (n+k) * d^k
```

The coefficient is itself a Cauchy-real series sum.  The definition therefore
requires a private coefficient-convergence construction in the data-rich
modules before exposing a stable public API.  If the direct definition needs
majorant data, use a data-carrying record first and expose the plain function
only after the coefficient sums can be constructed from existing radius data.

### Core strict-subball theorem

Primary public theorem:

```agda
recenterPowerSeriesOnStrictSubballFromMajorizedOnBall :
  BoundedByᶜ δ d →
  radius (δ +⁺ τ) < radius σ →
  PowerSeriesMajorizedOnBall a σ v ν →
  HasPowerSeriesOnBallWith
    (recenterPowerSeries a d)
    τ
    (recenterStrictSubballModulus δ τ σ ν)
```

The theorem should state only what is actually constructible.  If the first
closed version needs an explicit rational-bound majorant rather than the
existing `PowerSeriesMajorizedOnBall`, introduce a small record:

```agda
PowerSeriesRecenterMajorantData a σ v ν
```

and then prove adapters from the existing majorant/coefficient-bound routes.

### Centered-sum re-centering

After convergence of the re-centered series:

```agda
centeredPowerSeriesSumRecenteredOnStrictSubball :
  BoundedByᶜ δ d →
  BoundedByᶜ τ h →
  radius (δ +⁺ τ) < radius σ →
  PowerSeriesMajorizedOnBall a σ v ν →
  centeredPowerSeriesSumOnBall a σ μ (d +ᶜ h) ≡
  centeredPowerSeriesSumOnBall
    (recenterPowerSeries a d)
    τ
    (recenterStrictSubballModulus δ τ σ ν)
    h
```

The exact function names will follow the existing `centeredPowerSeriesSum...`
APIs.  Keep the finite reindexing helpers private unless they are reused by
composition later.

### Derivative model is analytic

Use Phase 3 derivative-radius closure and Phase 5A:

```agda
derivativePowerSeriesModelHasPowerSeriesAtWith :
  BoundedByᶜ δ (centeredDisplacement c x) →
  radius (δ +⁺ τ) < radius σ →
  PowerSeriesMajorizedOnBall (derivativePowerSeries a) σ v ν →
  HasPowerSeriesAtWith
    (λ y →
      centeredPowerSeriesSumEverywhere
        (derivativePowerSeries a)
        c
        derivativeRadius
        y)
    x
    (recenterPowerSeries
      (derivativePowerSeries a)
      (centeredDisplacement c x))
    τ
    μ
```

### Function-level derivative is analytic

After the centered model theorem checks, add a wrapper that uses the Phase 4
derivative theorem to identify the derivative value:

```agda
hasPowerSeriesAtWith→derivativeHasPowerSeriesAtWithFromMajorized :
  HasPowerSeriesAtWith f c a ρ μ →
  BoundedByᶜ δ (centeredDisplacement c x) →
  radius (δ +⁺ τ) < radius ρ →
  PowerSeriesMajorizedOnBall (derivativePowerSeries a) ρ v ν →
  HasPowerSeriesAtWith
    (powerSeriesDerivativeModel f a c ...)
    x
    (recenterPowerSeries
      (derivativePowerSeries a)
      (centeredDisplacement c x))
    τ
    χ
```

Do not name this as a naked `HasPowerSeriesAtWith -> derivative analytic`
theorem until the missing bridges from bare convergence to usable majorants are
proved.

## Proof Strategy

### 1. Binomial and finite algebra

Prove the finite identity first:

```text
Σ_{m < N} a_m (d + h)^m
=
Σ_{n < N} (Σ_{k < N-n} binomial(n+k,n) a_{n+k} d^k) h^n
```

Needed helpers:

- natural binomial coefficients into rationals/reals,
- finite binomial theorem for `d + h`,
- triangular finite-sum reindexing,
- compatibility with existing recursive `partialSum` definitions.

This step is pure finite algebra.  It should not mention convergence.

### 2. Coefficient convergence

For fixed `n`, prove convergence of:

```text
k ↦ binomial(n+k,n) * a(n+k) * d^k
```

under `|d| ≤ δ < σ`.  Use the standard geometric-polynomial estimate:

```text
binomial(n+k,n) * (δ / σ)^k
```

is summable for fixed `n` when `δ / σ < 1`.

Keep this machinery private if the public theorem can hide it behind
`recenterPowerSeries`.

### 3. Double-series majorant

For `|h| ≤ τ` and `δ + τ < σ`, control the absolute double series by the
original majorant:

```text
Σ_n Σ_k |a(n+k)| binomial(n+k,n) δ^k τ^n
=
Σ_m |a_m| (δ + τ)^m
```

Use the finite binomial theorem for the equality at finite truncation, then the
original majorant/tail on the probe radius `δ + τ`.  This avoids needing a
closed form for the binomial sums.

### 4. Limit exchange

Show the finite re-centered polynomials converge to both sides:

- finite original partial sums converge to the old centered sum at `d + h`;
- triangular re-centered partial sums converge to the new centered sum at `h`;
- the finite identity transports equality to the limits.

This is the real hard step.  Prefer a specialized theorem for triangular sums
over a general Fubini/Tonelli API.

### 5. Derivative analytic theorem

Once re-centering is available, derivative analyticity should be short:

1. Use Phase 3 to get convergence/radius data for `derivativePowerSeries a`.
2. Re-center `derivativePowerSeries a` at `centeredDisplacement c x`.
3. Use Phase 4 to identify the local derivative function with the centered
   derivative model where needed.

## Data-Rich First, Bare Later

The first checked theorem should be majorant-based.  Then add adapters:

- coefficient bounds plus convergence tail data,
- ball-term bounds,
- elementary-function instance majorants,
- truncated existence theorem if only bare Cauchy-real coefficient bounds are
  available propositionally.

The naked theorem:

```agda
HasPowerSeriesAtWith f c a ρ μ →
...
```

is not Phase 5's first target.  It remains blocked until there is a bridge from
bare convergence data to the majorants or coefficient bounds required by the
re-centering proof.

## Module Plan

1. `Recenter/Binomial.agda`
   - status: completed,
   - binomial coefficients,
   - finite binomial theorem,
   - real-power specialization of Cubical's commutative-ring binomial theorem,
   - triangular row/anti-diagonal finite-sum skeleton for later reindexing.

2. `Recenter/Base.agda`
   - status: completed,
   - `recenterCoefficientSeries`,
   - data-carrying `recenterPowerSeriesWith`,
   - coefficient path lemmas at `d = 0`,
   - canonical coefficient convergence data at `d = 0`.

   The plain `recenterPowerSeries` name is intentionally not exposed yet:
   coefficient sums require convergence data, which the majorant phase will
   construct from majorants.

3. `Recenter/Majorant.agda`
   - status: completed for the fixed-coefficient majorant core,
   - `RecenterCoefficientMajorantData`,
   - conversion from coefficient majorant data to
     `RecenterCoefficientConvergenceData`,
   - conversion from a family of coefficient majorants to
     `RecenterPowerSeriesData`,
   - data-carrying `recenterPowerSeriesFromCoefficientMajorants`.

   The double-series majorant and strict-subball tail modulus are deferred to
   `Recenter/Theorem.agda`.  A direct on-ball wrapper in this module made Agda
   spend anomalous time in checking the exposed majorant/radius signature; keep
   this module as the checked coefficient-majorant layer and prove the
   strict-subball theorem in the smaller theorem module.

4. `Recenter/Theorem.agda`
   - status: strict-subball convergence and centered-sum equality completed for
     the majorant/data-rich theorem,
   - checked theorem-level transport for the degenerate `d = 0`
     re-centering case,
   - checked finite triangular row/diagonal reindexing lives in
     `Recenter/FiniteIdentity.agda`,
   - checked fixed-degree binomial-geometric bounds live in
     `Recenter/BinomialGeometric.agda`,
   - checked coefficient convergence from
     `PowerSeriesMajorizedOnBall a σ v ν`, `|d| ≤ δ`, and `δ < σ` lives in
     `Recenter/CoefficientConvergence.agda`,
   - checked strict-subball bookkeeping lives in `Recenter/StrictSubball.agda`.

   The arbitrary-displacement convergence theorem
   `recenterPowerSeriesOnStrictSubballFromMajorizedOnBall` is implemented, and
   the sum identity
   `centeredPowerSeriesSumRecenteredOnStrictSubball` identifies the old sum at
   `d + h` with the re-centered sum at `h`.
   For fixed `n`, the library constructs convergence data for

   ```text
   k ↦ binomial(n+k,n) * a(n+k) * d^k
   ```

   from the old majorant tail for `v`.  The outer strict-subball tail is now
   closed by `Recenter/StripFinite.agda`, `Recenter/FiniteLimits.agda`, and
   `Recenter/StripTail.agda`: finite strip approximants are compared against
   the old `v` tail and then passed through the coefficient-row limits.

   The finite-to-limit bridge for the finite prefix rows is closed in
   `Recenter/PrefixLimit.agda`:

   ```text
   partialSum (recenterPowerSeriesWith a d data) m
   ```

   is compared with the old triangular partial sum by shifting the finite
   coefficient-row approximants, bounding the finite prefix difference by the
   old majorant tail, and closing the bound under limits.  The strip-tail
   theorem controls the outer rows `n ≥ m`; the prefix bridge controls the
   complementary finite prefix row tails `n < m`.

5. `DerivativeAnalytic.agda`
   - status: completed for the majorant/data-rich derivative model theorem,
   - `derivativePowerSeriesModelHasPowerSeriesAtWithFromMajorized` applies
     strict-subball re-centering to `derivativePowerSeries a`,
   - `derivativePowerSeriesModelHasPowerSeriesAtOnBallFromMajorized` and
     `derivativePowerSeriesModelAnalyticAtFromMajorized` package the checked
     local expansion at the requested center,
   - `derivativePowerSeriesModelHasPowerSeriesAtWithFromRadiusAndMajorized`
     uses Phase 3's derivative-radius closure from the original radius data,
   - `derivativeFunctionHasPowerSeriesAtWithFromModelPathAndMajorized`
     transports the checked expansion to any derivative function locally
     identified with the centered derivative model.

6. Aggregates
   - status: completed,
   - `Constructive.Analysis.Reals.PowerSeries` re-exports the theorem-level
     re-centering and derivative-analytic modules.
   - keep binomial and triangular bookkeeping private unless Phase 6 or
     composition needs it.

## Acceptance Criteria

- A caller with majorant/rational-bound data for `a`, a displacement bound
  `|x-c| ≤ δ`, and a strict margin `δ + τ < σ` can get a power-series expansion
  of the same function centered at `x`.
- Applying the theorem to `derivativePowerSeries a` gives a local power-series
  expansion for the derivative model on any strict subball.
- No public theorem claims the naked `HasPowerSeriesAtWith` version unless the
  necessary majorant/bounds bridge has been proved.
- `exp`, `sin`, and `cos` have a clear path to Phase 6 simplification through
  existing majorant data.
- No `postulate`, no classical choice, and no hidden extraction from truncated
  boundedness.

## Test Plan

Focused checks as each module lands:

```sh
agda Constructive/Analysis/Reals/PowerSeries/Recenter/Binomial.agda
agda Constructive/Analysis/Reals/PowerSeries/Recenter/Base.agda
agda Constructive/Analysis/Reals/PowerSeries/Recenter/Majorant.agda
agda Constructive/Analysis/Reals/PowerSeries/Recenter/Theorem.agda
agda Constructive/Analysis/Reals/PowerSeries/DerivativeAnalytic.agda
agda Constructive/Analysis/Reals/PowerSeries.agda
git diff --check
rg "postulate|\\?|TODO|FIXME" Constructive/Analysis/Reals/PowerSeries -g '*.agda'
```

If a module becomes anomalously slow, follow `docs/PERFORMANCE.md`.  Add
`--lossy-unification` only to the slow module and record the pattern there.
