# Constructive Power Series Plan

This plan gives a route for a complete one-variable power-series library over
the HoTT Cauchy reals `ℝᶜ`.  It is intended to support elementary functions and
their derivative rules, while staying constructive: convergence, domains, and
error estimates must be explicit data.

The intended namespace is `Constructive.Analysis.Reals.PowerSeries`.  Existing
series infrastructure under `Constructive.Analysis.Reals.Series` should remain
the foundation; power series should specialize and extend it, not duplicate it.

## Literature And Implementation Basis

- Russell O'Connor, *Certified Exact Transcendental Real Number Computation in
  Coq* (2008), uses complete metric spaces to construct elementary real
  functions with correctness proofs:
  https://arxiv.org/abs/0805.2438
- Robbert Krebbers and Bas Spitters, *Computer certified efficient exact reals
  in Coq* (2011), confirms that exact-real power-series work scales better
  when moduli, efficient approximants, and approximate division are first-class:
  https://arxiv.org/abs/1105.2751
- CoRN is the mature constructive Coq reference for real calculus.  Its public
  description includes continuity, differentiability, integration, Taylor's
  theorem, FTC, exact real computation, functions, integrals, and differential
  equations:
  https://github.com/rocq-community/corn
- Mathlib's analytic API separates formal series data from the proposition that
  a function has that series on a ball.  Its `HasFPowerSeriesOnBall`,
  `HasFPowerSeriesAt`, and `AnalyticAt` API is classical and much more general,
  but the separation of formal coefficients, ball radius, and function
  expansion is the right design lesson:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/Basic.html
- Fredrik Johansson's Arb work on elementary functions is not a proof-assistant
  implementation, but it is a mature exact/ball-arithmetic implementation
  reference for later performance work: argument reduction, Taylor series,
  rectangular splitting, denominator collection, and rigorous error bounds:
  https://arxiv.org/abs/1410.7176

## Existing Local Basis

Reuse these modules before adding new infrastructure:

- `Constructive.Analysis.Reals.Series.Finite` for partial sums;
- `Constructive.Analysis.Reals.Series.Tail` for tails and drops;
- `Constructive.Analysis.Reals.Series.Cauchy` for `seriesSum` and convergence
  from explicit tail bounds;
- `Constructive.Analysis.Reals.Series.Comparison` for majorant arguments;
- `Constructive.Analysis.Reals.Series.Instances.Geometric` for geometric
  series, positive majorants, and real powers;
- `Constructive.Analysis.Reals.Calculus.Derivative` for the derivative
  predicate once the termwise derivative theorem is ready.

## Scope

Build power series for one real variable:

```agda
PowerSeries = ℕ → ℝᶜ
```

with terms centered at zero:

```agda
powerSeriesTerm a h n = a n ·ᶜ realPower h n
```

and centered at `c` by using `h = x - c`.

The first complete target is:

- convergence and sums on rational closed subballs;
- local radius data as rational lower bounds, not a classical supremum radius;
- algebra of convergent power series;
- termwise differentiation;
- elementary instances `exp`, `sin`, `cos`, `log` through controlled series.

## Current Status

Phases 1 through 9 are implemented for the constructive, data-rich API:
closed-ball convergence, majorants, algebra, continuity, termwise
differentiation, exponential/trigonometric instances, radius-one logarithm,
atanh/atan subunit-ball instances, and the function-facing analytic predicates
are exported through `PowerSeries.agda`.  The remaining planned work is Phase
10-style evaluation and argument-reduction work, plus any future theorem that
explicitly packages global reciprocal/composition domains for `log`.

## Non-Goals

- Do not begin with multivariable analytic maps or Fréchet power series.  The
  first API should be one-dimensional and fit the current `ℝᶜ` arithmetic.
- Do not define elementary functions as syntax first.  Define executable
  functions with convergence data first; expression syntax can come later.
- Do not expose a public aggregate module until the core API stabilizes.
- Do not optimize evaluation before the correctness-oriented API is in place.

## Core Definitions

Use a uniform-on-closed-ball predicate as the main convergence data.  This is
strong enough for continuity, algebra, and termwise differentiation.

```agda
PowerSeries : Type₀
PowerSeries = ℕ → ℝᶜ

powerSeriesTerm :
  PowerSeries → ℝᶜ → ℕ → ℝᶜ

record HasPowerSeriesOnBallWith
    (a : PowerSeries)
    (ρ : ℚ⁺)
    (μ : ℚ⁺ → ℕ) :
    Type₀ where
  field
    antitoneModulus :
      AntitoneTailModulus μ
    tailBound :
      (h : ℝᶜ) →
      BoundedByᶜ ρ h →
      TailBound (powerSeriesTerm a h) μ
```

The corresponding sum should be a thin wrapper around the existing
`seriesSumFromFiniteTailBound`, with no new completion machinery:

```agda
powerSeriesSumOnBall :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  ℝᶜ
```

Open-radius data should be represented by closed subballs:

```agda
record HasPowerSeriesRadius
    (a : PowerSeries)
    (R : ℚ⁺) :
    Type₀ where
  field
    onSubball :
      (ρ : ℚ⁺) →
      radius ρ < radius R →
      Σ[ μ ∈ (ℚ⁺ → ℕ) ] HasPowerSeriesOnBallWith a ρ μ
```

This avoids needing a classical exact radius of convergence.  Later, a
separate record can package arbitrary large radii for entire functions:

```agda
HasInfinitePowerSeriesRadius a =
  (ρ : ℚ⁺) → Σ[ μ ∈ (ℚ⁺ → ℕ) ] HasPowerSeriesOnBallWith a ρ μ
```

Centered expansions should not be global functions without domain evidence:

```agda
record InPowerSeriesBall (c : ℝᶜ) (ρ : ℚ⁺) (x : ℝᶜ) : Type₀ where
  field
    displacementBound : BoundedByᶜ ρ (x +ᶜ (-ᶜ c))
```

## Module Layout

Create modules in this order:

```text
Constructive/Analysis/Reals/PowerSeries.agda
Constructive/Analysis/Reals/PowerSeries/Base.agda
Constructive/Analysis/Reals/PowerSeries/Radius.agda
Constructive/Analysis/Reals/PowerSeries/Continuity.agda
Constructive/Analysis/Reals/PowerSeries/Analytic.agda
Constructive/Analysis/Reals/PowerSeries/Majorant.agda
Constructive/Analysis/Reals/PowerSeries/Algebra.agda
Constructive/Analysis/Reals/PowerSeries/CauchyProduct.agda
Constructive/Analysis/Reals/PowerSeries/Differentiation.agda
Constructive/Analysis/Reals/PowerSeries/DerivativeConvergence.agda
Constructive/Analysis/Reals/PowerSeries/Instances.agda
Constructive/Analysis/Reals/PowerSeries/Instances/Polynomial.agda
Constructive/Analysis/Reals/PowerSeries/Instances/Geometric.agda
Constructive/Analysis/Reals/PowerSeries/Instances/Exponential.agda
Constructive/Analysis/Reals/PowerSeries/Instances/Trigonometric.agda
Constructive/Analysis/Reals/PowerSeries/Instances/Logarithm.agda
Constructive/Analysis/Reals/PowerSeries/Instances/Arctangent.agda
```

`PowerSeries.agda` and `Instances.agda` should be aggregate modules only after
their children type-check.

## Phase 1: Base And Pointwise Sums

Implement:

- `PowerSeries`;
- `powerSeriesTerm`;
- `powerSeriesPartialSum`;
- `powerSeriesSumFromFiniteTailBound`;
- convergence-at-point wrappers around `Series.Cauchy`;
- basic extensionality lemmas for equal coefficient streams and equal centers.

Do not introduce new Cauchy-completion definitions.  The proof obligation is to
translate power-series terms into existing series terms.

## Phase 2: Uniform Closed-Ball Convergence

Implement `HasPowerSeriesOnBallWith` and derive:

- pointwise convergence for every `h` with `BoundedByᶜ ρ h`;
- convergence of partial sums to `powerSeriesSumOnBall`;
- monotonicity from a larger ball to a smaller ball;
- stability under replacing the ball bound by a larger rational bound when
  existing `BoundedByᶜ` monotonicity supplies the proof.

This phase is the first useful milestone for elementary functions.

## Phase 3: Majorants

Add a majorant API instead of proving every tail estimate directly:

```agda
record PowerSeriesMajorizedOnBall
    (a : PowerSeries)
    (ρ : ℚ⁺)
    (v : ℕ → ℝᶜ)
    (μ : ℚ⁺ → ℕ) :
    Type₀ where
  field
    termMajorized :
      (h : ℝᶜ) →
      BoundedByᶜ ρ h →
      SeriesMajorizedBy (powerSeriesTerm a h) v
    majorTail :
      TailBound v μ
    majorAntitone :
      AntitoneTailModulus μ
```

Then prove:

```agda
majorizedOnBall→hasPowerSeriesOnBallWith :
  PowerSeriesMajorizedOnBall a ρ v μ →
  HasPowerSeriesOnBallWith a ρ μ
```

This should reuse `Series.Comparison` and the existing geometric majorants.

## Phase 4: Algebra

Prove algebraic closure with explicit convergence data:

- zero and constant series;
- addition and negation;
- rational and real scalar multiplication, with explicit scalar bounds where
  multiplication requires them;
- finite polynomial series and equality with polynomial evaluation;
- Cauchy-product coefficients, their formal algebra, polynomial closure, and
  later Cauchy product under absolute/majorant convergence;
- shift and drop lemmas:

```text
Σ aₙ hⁿ = a₀ + h * Σ aₙ₊₁ hⁿ
```

The Cauchy product should be implemented after the finite convolution lemmas
are available.  Avoid using unordered infinite rearrangements without an
explicit majorant theorem.

## Phase 5: Continuity And Differentiation

First prove continuity on closed subballs:

- partial sums are uniformly continuous on bounded balls;
- uniform limit of uniformly continuous partial sums is uniformly continuous,
  using explicit moduli;
- power-series sums are continuous within the ball.

Then define formal derivative coefficients:

```agda
derivativeCoefficients :
  PowerSeries → PowerSeries
derivativeCoefficients a n =
  rational (fromNat (suc n)) ·ᶜ a (suc n)
```

Prove the termwise derivative theorem:

```text
if a converges on a ball of radius R
and derivativeCoefficients a converges on every smaller ball,
then the sum of a has derivative equal to the sum of derivativeCoefficients a
on every smaller ball.
```

The proof should use:

- finite polynomial derivative identities;
- uniform tail control for the original and derivative series;
- the existing `HasDerivativeAtWith` remainder definition, so the final theorem
  directly plugs into calculus.

## Phase 6: Factorial And Exponential Infrastructure

Start with recurrence-defined reciprocal factorial coefficients, then create
factorial support only as far as power series need:

```text
Constructive/Data/Nat/Factorial.agda
Constructive/Data/Rationals/Factorial.agda
```

Targets:

- factorial positivity;
- rational embedding of `n!`;
- reciprocal coefficients `1/n!`;
- cancellation lemmas for `(n + 1) * 1/(n + 1)! = 1/n!`;
- formal exponential coefficient stream and `D exp = exp`;
- estimates showing factorial terms eventually dominate powers on every
  rational bounded ball;
- antitone tail modulus for exponential majorants.

Then implement:

```text
expCoefficients n = 1 / n!
expᶜ x = Σ expCoefficients n * x^n
```

with infinite-radius convergence.

## Phase 7: Trigonometric Series

Define sine and cosine either as subseries with direct factorial majorants or as
separate coefficient streams:

```text
sin x = Σ (-1)^n * x^(2n+1) / (2n+1)!
cos x = Σ (-1)^n * x^(2n) / (2n)!
```

Initial theorems:

- convergence on every rational closed ball;
- formal coefficient rules `sin' = cos`;
- formal coefficient rules `cos' = - sin`;
- `sin 0 = 0`;
- `cos 0 = 1`.

Addition formulas and `sin² + cos² = 1` should wait until Cauchy products and
series rearrangement are solid.

## Phase 8: Logarithm And Arctangent

Start with radius-one series:

```text
atanh z = Σ z^(2n+1) / (2n+1), |z| < 1
log x = 2 * atanh ((x - 1) / (x + 1))
```

The checked Phase 8 API exposes the radius-one, domain-evidenced pieces:
`Logarithm.agda` provides `logOnePlusPowerSeries` and its local within-ball
function, while `Arctangent.agda` provides `atanhPowerSeries`,
`atanPowerSeries`, their subunit-ball majorants, convergence/radius data,
coefficient bounds, continuity wrappers, and analytic-within witnesses.

The logarithm must carry domain data:

- `x` is positive, preferably with a positive lower bound;
- `x` has an upper bound when needed to prove `|(x - 1)/(x + 1)| < 1`;
- reciprocal calls must use bounded-away-from-zero evidence for `x + 1`.

For arctangent:

```text
atan x = Σ (-1)^n x^(2n+1)/(2n+1), |x| < 1
```

Global `atan` should wait for argument reduction.  Global `log` through the
atanh transform should likewise be exposed only after the reciprocal/domain
composition API can carry the positivity and bounded-away-from-zero evidence
without hiding it.

## Phase 9: Analytic API

After the preceding pieces work, introduce function-facing predicates:

```agda
record HasPowerSeriesAtWith
    (f : ℝᶜ → ℝᶜ)
    (c : ℝᶜ)
    (a : PowerSeries)
    (ρ : ℚ⁺)
    (μ : ℚ⁺ → ℕ) :
    Type₀
```

Fields:

- `convergence : HasPowerSeriesOnBallWith a ρ μ`;
- exact equality between `f x` and the power-series sum whenever
  `x - c` is bounded by `ρ`;
- optional located/domain data only when the function is partial.

Also define interval/domain variants later:

```text
HasPowerSeriesWithinAtWith f s c a ρ μ
AnalyticAt f c
AnalyticWithinAt f s c
```

This mirrors the mature `HasFPowerSeriesOnBall` / `HasFPowerSeriesAt`
separation, but keeps the first implementation one-dimensional and
constructive.

## Phase 10: Optimized Evaluation

Only after correctness:

- add Horner evaluation for finite partial sums;
- add rectangular splitting for long Taylor sums;
- add argument reduction for `exp`, `sin`, `cos`, `log`, and `atan`;
- keep optimized evaluators propositionally equal to the baseline sums or prove
  they are within a requested precision.

This phase follows the implementation lessons from exact-real and Arb-style
work, but it must not be a prerequisite for the mathematical API.

## Verification Strategy

For every Agda module:

- type-check the touched module;
- type-check the nearest aggregate module when it exists;
- run `git diff --check`;
- use `--lossy-unification` only when a file-level check is otherwise too slow,
  and record that in the file pragma and final report.

For anomalously slow checks, follow `docs/DEVELOPMENT.md` before changing proof
shape:

- run `agda --profile=modules`, then `agda --profile=definitions`, then
  `agda --profile=conversion --profile=constraints --profile=instances` on the
  slow module;
- profile the local module with cached imports when diagnosing PowerSeries
  definitions.  Avoid `--ignore-interfaces` on the aggregate unless the target
  is dependency rebuild cost, because it rechecks Cubical and the whole imported
  analysis stack;
- if a hot definition is caused by a large implicit target, first make module
  parameters, coefficient paths, moduli, and series arguments explicit; then
  split the proof into named lemmas or mark stable intermediates `abstract`.

Do not update `README.md` until the namespace is exported through aggregate
modules.  A private plan and non-exported modules do not change the public API.

## Open Risks

- Factorial estimates may require more rational-order infrastructure than
  currently exists.
- Cauchy products need careful finite-convolution lemmas and explicit absolute
  majorants.
- Uniform convergence on closed balls is stronger than pointwise convergence,
  but it is the right tradeoff for calculus and elementary functions.
- `log` and reciprocal-based functions must keep domain assumptions explicit;
  hiding positivity or bounded-away-from-zero data would weaken the constructive
  boundary.
- Performance work can easily distort proofs.  Keep baseline mathematical sums
  simple, then prove optimized evaluators correct later.
