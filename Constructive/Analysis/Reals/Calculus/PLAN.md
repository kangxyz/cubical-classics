# Constructive Calculus Plan

This plan is independent of the root constructive-analysis plan.  It gives a
specific route for one-variable differentiation, Riemann integration, and the
fundamental theorem of calculus over the HoTT Cauchy reals `ℝᶜ`.

The intended namespace is `Constructive.Analysis.Reals.Calculus`.  The first
target is constructive Bishop-style calculus with explicit rational precision
data, not a classical copy of textbook real analysis.

## Current Status

This is a future-calculus roadmap.  The current implementation has derivative
modules under `Constructive.Analysis.Reals.Calculus.Derivative`; the planned
step-function, integral, and FTC modules below do not currently exist.

## Literature Basis

- Bishop and Bridges, *Constructive Analysis* (1985), give the mathematical
  style: real analysis is carried out with positive data, apartness, moduli,
  and approximation principles rather than hidden choice.
- O'Connor, *Certified Exact Transcendental Real Number Computation in Coq*
  (2008), builds constructive elementary functions from complete metric spaces
  and explicit error bounds:
  https://arxiv.org/abs/0805.2438
- O'Connor and Spitters, *A computer verified, monadic, functional
  implementation of the integral* (2008), is the closest integration design:
  step functions, `L¹` and `L∞` metrics, completion, and an embedding of
  uniformly continuous functions:
  https://arxiv.org/abs/0809.1552
- Krebbers and Spitters, *Computer certified efficient exact reals in Coq*
  (2011), confirms that power-series and exact-real computation scale better
  when moduli and efficient approximants are first-class:
  https://arxiv.org/abs/1105.2751
- CoRN contains a broad constructive Coq real-calculus development, including
  continuity, differentiability, integration, Taylor's theorem, and FTC:
  https://github.com/coq-community/corn
- Mathlib's higher-order differential calculus documents the advantages of
  derivative-as-linear-approximation and domain-aware derivative statements.
  The long-term lesson is useful, although the library itself is classical:
  https://arxiv.org/abs/2509.04922
- MathComp-Analysis and recent Coq work on Lebesgue differentiation show a
  later route to measure-theoretic FTC.  That is not the first target here:
  https://arxiv.org/abs/2403.18229

## Scope

Develop calculus first for functions on real intervals:

```agda
f : [ a , b ]ᶜ → ℝᶜ
```

and for whole-line functions:

```agda
f : ℝᶜ → ℝᶜ
```

The core results should be constructive and data-bearing:

- a derivative is a uniform first-order approximation with an explicit
  remainder modulus;
- an integral is the limit of controlled step-function approximations;
- FTC statements are exact equalities, proved by showing approximations at
  every rational precision.

## Non-Goals

- Do not start with multivariable Fréchet calculus.  The one-dimensional
  derivative should be phrased so it can later embed into a linear-map
  formulation, but the first API should be usable for `ℝᶜ → ℝᶜ`.
- Do not prove classical "every continuous function on `[a,b]` is uniformly
  continuous" in the constructive namespace.  Require an explicit uniform
  modulus or a separate compactness principle.
- Do not define Lebesgue integration in this phase.
- Do not prove the full classical mean-value theorem before FTC.  The
  constructive FTC proof should use telescoping sums and explicit remainder
  bounds instead.

## Derivative Definition

Avoid quotient-style difference quotients as the primitive definition.  They
force apartness of the increment and make interval-domain bookkeeping awkward.
Use first-order approximation instead.

For whole-line functions, the intended core predicate is:

```agda
HasDerivativeAtWith :
  (f : ℝᶜ → ℝᶜ) →
  (x d : ℝᶜ) →
  (μ : ℚ⁺ → ℚ⁺) →
  Type₀
```

with meaning:

```text
for every requested slope error ε,
for every positive size η ≤ μ ε,
for every increment h bounded by η,
the remainder

  f (x + h) - f x - d * h

is bounded by ε * η.
```

Agda shape:

```agda
record HasDerivativeAtWith f x d μ : Type₀ where
  field
    remainderBound :
      (ε η : ℚ⁺) →
      radius η ≤ radius (μ ε) →
      (h : ℝᶜ) →
      BoundedByᶜ η h →
      BoundedByᶜ (ε *⁺ η)
        (f (x +ᶜ h) +ᶜ (-ᶜ f x) +ᶜ (-ᶜ (d ·ᶜ h)))
```

The interval version should not require manufacturing an interval proof for
`x + h`.  State it in terms of a nearby interval point:

```agda
HasDerivativeWithinAtWith :
  {a b : ℝᶜ} →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (x : [ a , b ]ᶜ) →
  (d : ℝᶜ) →
  (μ : ℚ⁺ → ℚ⁺) →
  Type₀
```

with meaning:

```text
if y is within η of x and η ≤ μ ε, then

  f y - f x - d * (point y - point x)

is bounded by ε * η.
```

This is the derivative "within the interval".  At endpoints it is a one-sided
condition because `y` ranges only over the interval.  For two-sided interior
derivatives, add an explicit interior-radius hypothesis:

```agda
InteriorRadius a b x ρ
```

meaning the closed `ρ`-neighbourhood of `x` stays inside `[a,b]`.

### Public Derivative Records

Expose data-bearing and existential variants:

```agda
HasDerivativeAtWith f x d μ
HasDerivativeAt f x d =
  Σ[ μ ∈ (ℚ⁺ → ℚ⁺) ] HasDerivativeAtWith f x d μ

DifferentiableAt f x =
  Σ[ d ∈ ℝᶜ ] HasDerivativeAt f x d
```

For interval statements:

```agda
HasDerivativeWithinAtWith f x d μ
HasDerivativeOnIntervalWith f f' μ
```

where the last form is uniform in `x` and is the right hypothesis for FTC.

## Derivative Theorems

First prove the local API:

- derivative uniqueness, using `MetricSpace.close-separated`;
- differentiability implies continuity, with an explicit modulus assembled
  from the derivative modulus and a bound on the derivative;
- constant, identity, rational scalar, addition, negation;
- product rule under local bounds for both factors;
- reciprocal rule only under explicit bounded-away-from-zero data;
- chain rule for whole-line functions, then an interval-domain version.

Do not hide local boundedness.  Multiplication and product rules in the
existing real development already require boundedness evidence in several
places, so calculus should continue that style.

## Integral Definition

Follow O'Connor-Spitters in structure, but keep the first version
one-dimensional and interval-specific.

Create:

- `Constructive/Analysis/Reals/Calculus/StepFunction.agda`
- `Constructive/Analysis/Reals/Calculus/Integral/Base.agda`
- `Constructive/Analysis/Reals/Calculus/Integral/Uniform.agda`

### Step Functions

Represent step functions over a normalized rational grid of `[0,1]`, then map
that grid into `[a,b]ᶜ` by the existing affine-grid infrastructure.

Suggested records:

```agda
record RationalPartition : Type₀ where
  field
    size : ℕ
    node : Fin (suc size) → ℚ
    ordered : ...
    leftEndpoint : node zero ≡ 0ℚ
    rightEndpoint : node (fromℕ size) ≡ 1ℚ

record StepFunction (a b : ℝᶜ) : Type₀ where
  field
    partition : RationalPartition
    value : Fin size → ℝᶜ
```

Define:

```agda
stepIntegral :
  (a b : ℝᶜ) →
  StepFunction a b →
  ℝᶜ
```

as a finite sum of `value i * width i * (b - a)`.  The first implementation may
start with rational endpoints, then generalize to located endpoints when the
affine interval API is convenient enough.

### Metrics On Step Functions

Define two precision relations:

- `L∞CloseStep ε s t`: pointwise closeness of step values after refining to a
  common partition;
- `L¹CloseStep ε s t`: closeness of the integrals of absolute differences,
  again after common refinement.

Expected theorem:

```text
L∞ close with bound ε on an interval of length κ
implies L¹ close with bound κ * ε.
```

This is the bridge from uniform continuity to integrability.

### Integrable Functions

There are two possible APIs.

The robust API is completion-based:

```agda
IntegrableFunction a b =
  CauchyCompletion (StepFunctionMetricL¹ a b)
```

and `integral` is the extension of `stepIntegral` to the completion.

The smaller initial API is data-based:

```agda
record RiemannIntegrableWith
    (a b : ℝᶜ)
    (f : [ a , b ]ᶜ → ℝᶜ) : Type₀ where
  field
    approximant : ℚ⁺ → StepFunction a b
    approximates : ...
```

The completion-based API is preferable long-term because it matches the
existing Cauchy-completion machinery.  The data-based API can be added as a
constructor interface for uniformly continuous functions.

### Uniformly Continuous Functions Are Integrable

For:

```agda
f : [ a , b ]ᶜ → ℝᶜ
uc : IsUniformlyContinuous (IntervalMetric a b) CauchyRealsMetricSpace f
```

construct step approximants by sampling `f` on a rational affine grid whose
mesh is below the requested modulus.  The existing located/evaluable IVT grid
code shows the shape of the finite-grid proofs.

If explicit sampled values are needed, require:

```agda
LocatedMap f
```

for witness-producing integrals.  For truncated/existence-only integrability,
keep results propositionally truncated where appropriate.

## Fundamental Theorem Of Calculus

Create:

- `Constructive/Analysis/Reals/Calculus/Derivative.agda`
- `Constructive/Analysis/Reals/Calculus/Integral.agda`
- `Constructive/Analysis/Reals/Calculus/FTC.agda`

### FTC II First

Prove the Newton-Leibniz direction first, because it avoids defining a
variable-upper-limit integral.

Hypotheses:

```agda
F f : [ a , b ]ᶜ → ℝᶜ
dF : HasDerivativeOnIntervalWith F f μ
f-integrable : RiemannIntegrableWith a b f
```

Target:

```agda
integral a b f f-integrable ≡
F (rightEndpoint a≤b) +ᶜ (-ᶜ F (leftEndpoint a≤b))
```

Proof route:

1. Choose a partition with mesh below the derivative modulus for `ε`.
2. Expand the telescoping sum:

   ```text
   F b - F a = Σ (F xᵢ₊₁ - F xᵢ)
   ```

3. Replace each increment by:

   ```text
   f xᵢ * (xᵢ₊₁ - xᵢ)
   ```

   plus a controlled remainder.
4. Bound the total remainder by summing `ε * widthᵢ`.
5. Compare with the step/Riemann integral approximation.
6. Use separatedness of `ℝᶜ` to turn all-precision closeness into equality.

This proof is constructive and does not require the mean-value theorem.

### FTC I Second

For uniformly continuous `f`, define:

```agda
areaFunction :
  (a b : ℝᶜ) →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  ...
  [ a , b ]ᶜ → ℝᶜ

areaFunction x = integral over [ a , point x ] of f restricted to that interval
```

Target, for interior points:

```agda
HasDerivativeWithinAt
  (areaFunction a b f ...)
  x
  (f x)
```

Proof route:

1. Use additivity of the integral over adjacent intervals.
2. Write the difference quotient without division:

   ```text
   area(y) - area(x) - f x * (y - x)
   = integral over [x,y] of (f t - f x)
   ```

3. Use uniform continuity of `f` to bound the integrand by `ε` on short
   intervals.
4. Bound the integral of the error by `ε * |y - x|`.

This gives the derivative predicate directly in first-order-approximation
form.

## Elementary Function Interface

Once derivative and integral are stable, connect them to the planned
elementary functions:

- polynomials: derivative by algebraic rules;
- power series: derivative inside a convergence radius by termwise
  differentiation with explicit majorants;
- `exp`: derivative equals itself, integral computes `exp b - exp a`;
- `sin` and `cos`: derivative cycle after factorial and alternating-series
  infrastructure.

Do not block the first FTC implementation on these functions.

## Suggested Implementation Order

1. Add finite partition and common-refinement infrastructure.
2. Define one-dimensional derivative predicates and prove uniqueness,
   constants, identity, addition, negation, scalar multiplication.
3. Add product and chain rules with explicit local bounds.
4. Define step functions and their finite integrals.
5. Define `L∞` and `L¹` step-function closeness plus refinement invariance.
6. Extend step integrals to Cauchy/integrable functions.
7. Embed uniformly continuous interval functions into integrable functions.
8. Prove integral linearity, interval additivity, and integral error bounds.
9. Prove FTC II by telescoping sums.
10. Define area functions and prove FTC I.
11. Add polynomial and power-series applications.

## Verification Strategy

Each phase should type-check its module and the nearest aggregate module:

```sh
agda Constructive/Analysis/Reals/Calculus/Derivative.agda
agda Constructive/Analysis/Reals/Calculus/Integral.agda
agda Constructive/Analysis/Reals/Calculus/FTC.agda
agda Constructive/Analysis/Reals.agda
git diff --check
```

If a module becomes too slow, add `--lossy-unification` to that module only and
report it in the change summary.

## Open Design Questions

- Whether `IntegrableFunction` should be exposed as a completion type or
  hidden behind `RiemannIntegrableWith` constructors.
- Whether the first interval integral should require located endpoints, or
  start with rational endpoints and later lift to located endpoints.
- Whether endpoint derivatives should be exported as one-sided derivatives or
  only as `HasDerivativeWithinAt`.
- How much of the O'Connor-Spitters step-function monad should be reproduced.
  The first version only needs enough structure for FTC and uniformly
  continuous functions.
