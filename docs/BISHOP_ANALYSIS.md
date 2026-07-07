# HoTT And Bishop Analysis Interfaces

This note records the distinction between the HoTT Cauchy-real interface used
in this repository and the Bishop-style data needed by some analysis
definitions.  The distinction matters for continuity, power-series
convergence, and derivative-convergence automation.

## Cauchy Reals And Located Data

The main Cauchy-real type is `ℝᶜ`.  It is the HoTT-style Cauchy completion of
the rational metric space, with rational-indexed closeness:

```agda
MetricSpace.Close CauchyRealsMetricSpace x ε y
```

where `ε : ℚ⁺`.  A bare `x : ℝᶜ` supports enough approximation to prove
boundedness only propositionally:

```agda
merely-boundedᶜ :
  (x : ℝᶜ) →
  ∥ Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ x ∥₁
```

This says that some rational bound exists, but it does not expose a concrete
`κ` that can be used to define a modulus.

Located Cauchy reals add chosen approximation and comparison data:

```agda
record Locator (x : ℝᶜ) : Type₀ where
  field
    compare :
      (q r : ℚ) →
      q < r →
      (rational q <ᶜ x) ⊎ (x <ᶜ rational r)

    approximate :
      (ε : ℚ⁺) →
      Σ[ q ∈ ℚ ] x ∼[ ε ] rational q
```

Because `approximate` is not truncated, a located real gives an explicit
rational bound: take a fixed precision, for example `1/2`, obtain a rational
approximation `q`, and use the existing rational-approximation bound lemma.

Thus:

```text
bare x : ℝᶜ        gives  ∥ Σ κ, BoundedByᶜ κ x ∥₁
Locator x          gives    Σ κ, BoundedByᶜ κ x
```

## Explicit Moduli

The metric and Cauchy APIs in this repository are precision-indexed by positive
rationals.  A strong continuity statement usually has an explicit modulus:

```agda
Σ[ ν ∈ PrecisionModulus ] ...
```

where a `PrecisionModulus` is a function from requested output precision to
input precision, typically:

```agda
ν : ℚ⁺ → ℚ⁺
```

This is stronger than ordinary epsilon-delta continuity.  It does not merely
say that a suitable `δ` exists for each `ε`; it gives a chosen function
computing such a `δ`.

For a linear map `x ↦ a * x`, the usual proof needs a rational bound
`A : ℚ⁺` with `|a| ≤ A`.  Then one defines a modulus such as
`δ = ε / A`.  If `a` is a bare Cauchy real, the repository can prove only
truncated existence of such an `A`, not extract a concrete one.  If `a` is
located, or if a bound is provided as data, the explicit modulus can be built.

## Propositional Continuity

The weaker epsilon-local form avoids choosing a global modulus:

```agda
(ε : ℚ⁺) →
  ∥ Σ[ δ ∈ ℚ⁺ ]
      ({y : ℝᶜ} →
        Close x δ y →
        Close (f x) ε (f y))
  ∥₁
```

This form is closer to ordinary constructive epsilon-delta continuity.  It
permits proofs that use truncated boundedness locally for a fixed `ε`.  It
does not produce a reusable `ν : ℚ⁺ → ℚ⁺`.

The practical split is:

```text
explicit rational bounds   -> explicit rational modulus continuity
bare Cauchy coefficients   -> propositional/truncated continuity
located coefficients       -> explicit rational modulus continuity
```

## Power Series

For power series, the same distinction appears in the analytic interfaces.

`HasPowerSeriesAtWith` records expansion and convergence data with explicit
tail moduli.  It is enough to control the series value through convergence
tails, but it does not by itself expose rational bounds for every coefficient.

For continuity automation with explicit rational moduli, use a data-rich
package:

```agda
HasPowerSeriesAtWithBounds f c a ρ μ =
  Σ[ expansion ∈ HasPowerSeriesAtWith f c a ρ μ ]
    PowerSeriesCoefficientBounds a
```

The coefficient-bound component supplies:

```agda
PowerSeriesCoefficientBounds a
```

that is, a concrete rational bound for each coefficient.  This is the data
needed to build Lipschitz estimates for finite partial sums and hence explicit
uniform-continuity moduli.

Majorant data is another valid data-rich route.  A majorant provides rational
or explicitly bounded comparison terms and can often produce the estimates
needed for convergence and continuity without asking users for individual
coefficient bounds.

## Radius And Coefficient Bounds

Knowing only a convergence radius does not imply that the raw coefficients
`a n` are uniformly bounded.  For example, the power series with coefficients
`a n = n` has radius `1`, but the coefficients are not bounded.

Convergence at a positive radius gives control over weighted terms such as
`a n * σ ^ n`.  That is the right information for strict-subball arguments.
If `ρ < σ`, then the factor `(ρ / σ) ^ n` supplies decay on the smaller ball.
For derivative convergence one also controls the extra factor `suc n` using
the fact that `(suc n) * q ^ n` is bounded when `q < 1`.

Thus strict-subball derivative convergence should be proved from data that
actually exposes the weighted convergence or majorant bounds, for example:

```agda
PowerSeriesMajorizedOnBall a σ v ν
```

It should not be claimed from a bare expansion interface unless the missing
bridge from bare convergence to usable bounds has been proved.

## Real-Radius Variants

Another possible design is to formulate continuity with positive real radii
instead of rational radii.  This matches informal arguments such as "`|a|`
itself bounds `a`" more directly.

The cost is that the existing metric API is rational-indexed.  A real-radius
definition therefore needs either:

- a new closeness relation indexed by positive Cauchy reals, or
- a bridge that turns a positive real radius into a rational radius below it.

The second route again needs locatedness or some equivalent data to extract a
usable rational precision.  For this reason, real-radius continuity should be
added as a parallel interface, not as a replacement for the current
`ℚ⁺`-modulus API.

## Implementation Rule Of Thumb

Use the weakest interface that supports the theorem being stated.

- Use explicit `PrecisionModulus` conclusions when the proof has explicit
  rational bounds, located data, or majorants.
- Use propositional/truncated continuity when working from bare Cauchy-real
  data.
- Use `HasPowerSeriesAtWithBounds` or majorant-bearing records for automatic
  continuity of elementary power-series expansions.
- Do not silently replace a bare expansion theorem by a stronger
  bounds-bearing theorem; make the extra data visible in the type.
