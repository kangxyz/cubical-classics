# Frank Approximate IVT Plan

This plan is independent of the existing grid-search approximate IVT.  Its
target is Matthew Frank's version from *Interpolating Between Choices for the
Approximate Intermediate Value Theorem*:

https://arxiv.org/abs/1701.02227

Frank proves that a pointwise continuous `f : [a,b] -> R` with
`f a < 0 < f b` has values arbitrarily close to zero, without uniform
continuity, countable choice, or inspecting rational approximants of real
values.  The proof still needs real Cauchy-sequence completeness.

## Target

Add a separate public module:

```agda
Constructive.Analysis.Reals.IVT.Frank
```

The first public theorem should have a propositional conclusion:

```agda
frank-approximate-IVT :
  {a b : ℝᶜ} ->
  (a≤b : a ≤ᶜ b) ->
  (f : [ a , b ]ᶜ -> ℝᶜ) ->
  PointwiseContinuousOnInterval a b f ->
  f (leftEndpoint a≤b) <ᶜ 0ᶜ ->
  0ᶜ <ᶜ f (rightEndpoint a≤b) ->
  (ε : ℚ⁺) ->
  ∥ Σ[ x ∈ [ a , b ]ᶜ ]
      absᶜ (f x) <ᶜ rational (radius ε) ∥₁
```

The exact name can be adjusted to the local naming style.  The important
boundary is that this theorem must not require:

- `Locator a`, `Locator b`, or `LocatedMap f`;
- `ApproxEvaluable f`;
- uniform continuity;
- countable choice;
- exact zeros.

An untruncated `Σ` theorem is not part of Frank's result.  It may be added
later only under stronger hypotheses, such as the current located/evaluable
assumptions.

## Source Proof

Frank's construction fixes the requested precision `ε` and defines, by
recursion,

```text
a_1 = a
b_1 = b
c_n = (a_n + b_n) / 2
d_n = max(0, min(1/2 + f(c_n) / ε, 1))
a_(n+1) = c_n - d_n * (b - a) / 2^n
b_(n+1) = b_n - d_n * (b - a) / 2^n
```

Here `d_n` lies in `[0,1]`.  If `f(c_n) > ε/2`, then `d_n = 1` and the next
interval is the left half.  If `f(c_n) < -ε/2`, then `d_n = 0` and the next
interval is the right half.  In the middle case, `|f(c_n)| < ε` already gives
an approximate zero.

The core claim is:

```text
For every m, either
  (i)  some j <= m has |f(c_j)| < ε, or
  (ii) f(a_m) < 0 and 0 < f(b_m).
```

The intervals are nested and have length `(b - a) / 2^(n-1)`, so the sequence
`c_n` is Cauchy.  Let `c` be its limit.  Pointwise continuity is used only once,
at this final `c`: choose `δ` for precision `ε`, then choose `m` with
`|c - c_m| < δ/2` and `(b - a) / 2^m < δ/2`.  If the finite near-zero branch of
the claim holds, use that witness.  Otherwise `a_m` and `b_m` are both within
`δ` of `c`, so `f(c)` is within `ε` of both a negative and a positive value,
hence `|f(c)| < ε`.

This is why the formal theorem should return truncated existence: the proof
produces a witness from a finite disjunction plus a limit case, but without
choosing signs or rational approximants as computational data.

## Required Interfaces

### Pointwise Continuity

Create `Constructive.Analysis.Reals.IVT.Pointwise` or a more general metric
module if it is clearly reusable.

Use a truncated local modulus for the public Frank theorem:

```agda
ContinuousAtOnInterval a b f x =
  (ε : ℚ⁺) ->
  ∥ Σ[ δ ∈ ℚ⁺ ]
      ((y : [ a , b ]ᶜ) ->
       MetricSpace.Close (IntervalMetric a b) x δ y ->
       MetricSpace.Close CauchyRealsMetricSpace (f x) ε (f y)) ∥₁

PointwiseContinuousOnInterval a b f =
  (x : [ a , b ]ᶜ) -> ContinuousAtOnInterval a b f x
```

It is useful to also have an internal dataful witness type for local proofs,
but the public theorem should accept the truncated version.  Since the final
result is truncated, eliminating the single continuity witness at the limit
point is allowed and does not imply countable choice.

### Frank State

Represent the recursive construction by a state containing:

- `left right mid : [ a , b ]ᶜ`;
- proofs that `pointᶜ mid = (pointᶜ left + pointᶜ right) / 2`;
- a length invariant for `pointᶜ right - pointᶜ left`;
- containment/nestedness proofs needed for Cauchy estimates.

The public theorem should not ask for a rational bound on `b - a`.  Internally,
the current `ℝᶜ` library can supply a merely existing rational bound, and the
proof can eliminate that boundedness only into the truncated final result.  Any
module that constructs a concrete Cauchy modulus for `c_n` should therefore be
parameterized by:

```agda
Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ (b +ᶜ (-ᶜ a))
```

or by the upper-bound half of this data.  This avoids adding a public
`Locator` requirement while still matching the repository's explicit-modulus
completion API.

Do not expose this state from the public API.  Put it under:

```agda
Constructive.Analysis.Reals.IVT.Frank/
```

Suggested internal modules:

- `Dyadic.agda`: positive dyadic scales and Archimedean search for
  `scale n * (b - a) < δ`;
- `Clamp.agda`: `clamp01 x = 0ᶜ ⊔ᶜ (x ⊓ᶜ 1ᶜ)` and its order/equality lemmas;
- `State.agda`: the recursive `a_n`, `b_n`, `c_n`, `d_n` construction;
- `Cauchy.agda`: nested-interval bounds and convergence of `c_n`;
- `Claim.agda`: Frank's finite claim;
- `Proof.agda`: assembly of the public theorem.

## Main Lemmas

1. Clamp bounds:

```agda
0ᶜ ≤ᶜ clamp01 x
clamp01 x ≤ᶜ 1ᶜ
1ᶜ ≤ᶜ x -> clamp01 x ≡ 1ᶜ
x ≤ᶜ 0ᶜ -> clamp01 x ≡ 0ᶜ
```

2. Frank decision interpolation:

```agda
d_n = clamp01 (1/2ᶜ + scalarMulᶜ (1 / radius ε) (f c_n))

f c_n > ε/2  -> d_n ≡ 1ᶜ
f c_n < -ε/2 -> d_n ≡ 0ᶜ
```

3. Interval update algebra:

```agda
d_n ≡ 1ᶜ -> a_(n+1) ≡ a_n  × b_(n+1) ≡ c_n
d_n ≡ 0ᶜ -> a_(n+1) ≡ c_n  × b_(n+1) ≡ b_n
b_n - a_n = (b - a) / 2^(n-1)
[a_(n+1), b_(n+1)] is contained in [a_n, b_n]
```

Use repeated halving rather than introducing a broad exponentiation API unless
the existing rational code already provides the needed power lemmas.

4. Overlapping trichotomy around the target precision:

```agda
f c_n < -ε/2
  ∨ |f c_n| < ε
  ∨ ε/2 < f c_n
```

In Cubical/HoTT this should probably be a propositional-truncated disjunction,
built from the existing weak linear/order infrastructure.  Avoid decidable
comparison of arbitrary reals.

5. Finite claim:

```agda
FrankClaim m =
  ∥ (Σ[ j ∈ FinUpTo m ] absᶜ (f c_j) <ᶜ rational (radius ε))
    ⊎ (f a_m <ᶜ 0ᶜ × 0ᶜ <ᶜ f b_m) ∥₁
```

The induction should consume the truncated trichotomy and produce another
truncated claim.  This keeps the proof faithful to Frank's no-choice argument.

6. Cauchy convergence:

```agda
|c_m - c_n| <= (b - a) / 2^(m-1)  for m < n
```

Given a rational bound on `b - a`, convert this to the existing
`CauchyWithModulus` or directly to
`CauchyApproximation CauchyRealsMetricSpace`, then use
`CauchyRealsIsCauchyComplete`.  Also prove that the resulting limit lies in the
original interval, so it can be used as an element of `[ a , b ]ᶜ` in the final
continuity step.

7. Final continuity step:

Use pointwise continuity at the limit `c`.  After choosing `m`, combine:

```agda
|c - a_m| < δ
|c - b_m| < δ
f a_m < 0
0 < f b_m
```

to prove `absᶜ (f c) < rational (radius ε)`.

## Order Of Work

1. Add the pointwise-continuity interface and check that uniform continuity
   implies it.  This gives a bridge from the current IVT assumptions but should
   not be used in Frank's theorem statement.
2. Prove the clamp and scalar-order lemmas needed to turn high/low values of
   `f(c_n)` into `d_n = 1` or `d_n = 0`.
3. Implement dyadic scales and the interval-state recursion.
4. Prove length, containment, and Cauchy convergence of the midpoint sequence,
   parameterized by a rational bound on the initial interval length.
5. Formalize the overlapping trichotomy and the finite claim.
6. Assemble the final theorem using one pointwise-continuity witness at the
   Cauchy limit and one truncated rational bound for `b - a`.
7. Reexport only the public theorem and continuity interface from
   `Constructive.Analysis.Reals.IVT`; keep proof modules internal to the
   `Frank/` directory.

## Checks

Type-check, at minimum:

```text
Constructive/Analysis/Reals/IVT/Pointwise.agda
Constructive/Analysis/Reals/IVT/Frank.agda
Constructive/Analysis/Reals/IVT.agda
```

Also run a whitespace/diff check over `Constructive/Analysis/Reals/IVT`.

## Risks

- The current real-order API may not yet have all lattice absorption and
  scalar-order lemmas needed by the clamp proof.
- The wide trichotomy must be stated with truncation or another constructive
  disjunction; a decidable real comparison would break the intended theorem.
- The interval-state recursion needs many bounds.  Keep these private and do
  not add public wrapper aliases unless a lemma is reused outside Frank's
  proof.
- The repository's Cauchy-completeness interface is modulus-based.  Frank's
  paper speaks about the ordinary Cauchy sequence `c_n`, so the formalization
  needs a rational bound on `b - a` to build a modulus; hide this under the
  truncated final result rather than adding it to the theorem statement.
- If pointwise continuity is made dataful in the public theorem, the result
  becomes stronger than Frank's internal-logic statement.  Prefer the truncated
  interface and use dataful witnesses only internally.
