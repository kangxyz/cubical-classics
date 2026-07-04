# Constructive Dedekind Cut Roadmap

This folder tracks a LEM-free Dedekind real development.  The code may depend
on `Constructive/`, but the constructive core must not depend on `Classical/`,
`Oracle`, `LEM`, or propositional resizing.

## Target Shape

There are three separate goals.

1. Constructive Dedekind completeness.
   Prove that every real-valued located Dedekind cut is represented by a unique
   `DedekindCut`.

2. Constructive ordered field structure.
   Prove that `DedekindCut` forms an Archimedean ordered field, with inverses
   stated using apartness where constructively necessary.

3. Classical bridge.
   Under LEM, show that the constructive Dedekind completeness theorem gives
   the powerset supremum principle called `MacNeilleCompleteness` in the
   existing classical development.  Combining this with the ordered-field
   structure gives the final classical `MacNeilleCompleteOrderedField` shape.

## Literature Constraints

- HoTT Book, Chapter 11: Dedekind cuts use lower and upper predicates
  `L U : Q -> hProp`, inhabitedness, roundedness, disjointness, and locatedness
  `q < r -> L q \/ U r`.
- The algebra/order of Dedekind reals is constructive.  Field inverses should
  use apartness, not mere non-equality.
- Dedekind completeness is constructive when formulated as located cuts of
  reals or equivalent cuts in the order.
- Cauchy completeness must use Cauchy approximations or explicit moduli; plain
  sequence completeness can require choice.
- Under LEM, powerset/MacNeille supremum completeness can be recovered from the
  constructive completeness statement by turning arbitrary bounded subsets into
  located real-valued cuts.

## Invariants

- No `LEM`, `Oracle`, `PropResizing`, or `Classical.*` imports in the
  constructive core files.
- Cuts stay universe-polymorphic over `Q -> hProp ell`; resizing is not
  assumed.
- Existential witnesses from cut structure stay truncated unless a local
  decidability/search argument constructively splits them.
- Any LEM-dependent bridge lives in a separate module.

## Milestones

### M0. Core Cut Infrastructure

Status: done.

- `DedekindCut ell`, extensional equality, set-truncation.
- Rational embedding at `ell-zero` and lifted embeddings at arbitrary `ell`.
- Constructive order: `<=`, `<`, apartness, rational density/locatedness.
- Lattice operations `meet` and `join`.
- Rational embedding order reflection/preservation.
- Archimedean rational upper/lower bounds.
- Negation and order reversal.

### M1. Rational Approximation

Status: done.

- Prove every positive rational epsilon admits close rational lower/upper
  bounds for any cut:

```agda
close-bounds :
  (x : DedekindCut ell) (epsilon : Q) ->
  0 < epsilon ->
  || CloseBounds x epsilon ||_1
```

This is used by algebra and can also support completeness estimates.

### M2. Constructive Dedekind Completeness

Status: done, same-universe version.

Defined in `Cubical.DedekindCut.Completeness`.

Define a real-valued located cut as predicates on `DedekindCut ell`:

- inhabited lower side and upper side;
- lower/upper closure for the cut order;
- roundedness with respect to strict order;
- disjointness;
- locatedness for `x < y`.

Then prove:

```agda
representing-cut :
  RealValuedCut ell ell' -> DedekindCut (ell-max ell ell')

represented-lower :
  x is in the lower side iff x < representing-cut C

represented-upper :
  x is in the upper side iff representing-cut C < x

representing-cut-unique :
  uniqueness by extensionality / order antisymmetry
```

The current checked theorem is universe-internal: predicates on
`DedekindCut ell` valued in `hProp ell`.  This avoids resizing and is enough
for the first constructive representation theorem.  A later lifted/mixed-level
variant can be added if a bridge theorem needs it.

### M3. Ordered Field Structure

Status: done for the constructive target. Required for the final theorem.

- Addition and additive group.
  - Done: addition as a Dedekind cut in
    `Cubical.DedekindCut.Arithmetic`.
  - Done: addition commutativity.
  - Done: addition associativity.
  - Done: additive zero laws.
  - Done: additive inverse.
  - Done: addition preserves non-strict order and strict order under
    translation.
  - Done: nonnegative multiplication core.
    - Done: product lower/upper predicates and the cut axioms that do not
      require the located estimate: inhabitedness, closure, roundedness,
      disjointness.
    - Done: nonnegative upper endpoints are positive, plus a
      `NonnegativeCloseBounds` wrapper around `close-bounds`.
    - Done: bounded rational approximations
      `bounded-close-bounds` / `NonnegativeBoundedCloseBounds`, preserving a
      chosen upper bound for later multiplication estimates.
    - Done: positive rational inverse and positive scaling helpers for the
      later multiplicative error bound.
    - Done: multiplication-specific paired close-bounds and located scale
      constructors.
    - Done: product lower/upper predicates are symmetric.
    - Done: rational error estimates for the located proof, including the
      nonpositive-endpoint cases and the positive-endpoint split
      `ux*uy = lx*ly + (ux-lx)*uy + lx*(uy-ly)`.
    - Done: locatedness for nonnegative multiplication.
    - Done: packaged nonnegative multiplication cut `nnMul` and commutativity.
- Signed multiplication using positive and negative parts.
  - Done: positive and negative parts `x+ = x join 0` and
    `x- = (-x) join 0`, with nonnegativity proofs.
  - Done: signed multiplication definition from the four nonnegative
    products.
  - Done: signed multiplication commutativity.
- Ordered commutative ring laws.
  - Done: library-level interface split:
    `Constructive.Algebra.OrderedField` is now the LEM-free ordered field
    interface with inverses from apartness `x # 0`, while the previous
    trichotomous/`Field`-based API lives under
    `Constructive.Algebra.StrictlyOrderedField`.
  - Done: rational `1D` cut and nonnegativity of `1D`.
  - Done: nonnegative multiplication zero laws `nnMul-zeroR` and
    `nnMul-zeroL`.
  - Done: proof irrelevance/congruence for `nnMul` arguments.
  - Done: addition preserves nonnegativity.
  - Done: `nnMul` preserves nonnegativity.
  - Done: positive/negative part simplifications for nonnegative cuts:
    `x+ = x` and `x- = 0`.
  - Done: `positiveProducts` / `negativeProducts` are nonnegative.
  - Done: for nonnegative inputs, signed multiplication agrees with
    `nnMul`.
  - Done: signed multiplication zero laws `*-zeroR` and `*-zeroL`.
  - Done: `nnMul` is monotone in each nonnegative argument for `<=`.
  - Done: right-nonnegative form of signed multiplication
    `x * z = x+ *nn z - x- *nn z`.
  - Done: multiplication by a nonnegative factor preserves `<=` on either
    side.
  - Done: rational helper lemmas for future unit-law proofs:
    nonnegative products, positive-inverse cancellation, and the order facts
    `q < a -> q/a < 1` and `r < q -> 1 < q/r`.
  - Done: nonnegative multiplication unit laws in
    `Cubical.DedekindCut.Arithmetic.Unit`.
  - Done: signed multiplication unit laws `*-idR` and `*-idL`, via the
    constructive decomposition `x = x+ - x-`.
  - Done: reusable additive-group normalization lemmas in
    `Cubical.DedekindCut.Arithmetic.AdditiveGroup`, including cancellation,
    uniqueness of inverses, `-(a+b) = -a + -b`, and
    `-(a-b) = b-a`.
  - Done: signed multiplication commutes with negation in
    `Cubical.DedekindCut.Arithmetic.Negation`:
    `(- x) * y = - (x * y)`, `x * (- y) = - (x * y)`, and
    `(- x) * (- y) = x * y`.
  - Done: nonnegative multiplication associativity in
    `Cubical.DedekindCut.Arithmetic.NonnegativeLaws`.  The proof uses
    `<=` antisymmetry and only lower inclusions, avoiding new upper-endpoint
    epsilon estimates.
  - Done: nonnegative multiplication distributes over addition on both sides
    in `Cubical.DedekindCut.Arithmetic.NonnegativeLaws`.  The proof handles
    the constructive lower-cut sign split for rational addends directly and
    does not use LEM.
  - Done: full signed distributivity in
    `Cubical.DedekindCut.Arithmetic.Distributivity`.
  - Done: full signed associativity in
    `Cubical.DedekindCut.Arithmetic.Associativity`.
  - Done: `CommRing` packaging in
    `Cubical.DedekindCut.Arithmetic.CommRing`.
  - Done: strict positive-factor monotonicity, positive-product preservation,
    and positive-sum splitting in
    `Cubical.DedekindCut.Arithmetic.Order`.
  - Done: `OrderedCommRing` packaging in
    `Cubical.DedekindCut.Arithmetic.OrderedCommRing`.
  - Done: positive reciprocal cuts and the proof
    `x * posInvCut x = 1` for `0 < x` in
    `Cubical.DedekindCut.Arithmetic.PositiveInverse`.
  - Done: apartness-based inverses for all `x # 0`, with both right and left
    inverse forms exported by
    `Cubical.DedekindCut.Arithmetic.ApartnessField`.
  - Done: formal `Constructive.Algebra.OrderedField` instance
    `DedekindCutOrderedField`.
  - Done: checked M3 aggregate entry point
    `Cubical.DedekindCut.Arithmetic.M3`.
  - Engineering note: the unit-law proof is intentionally split into
    `Arithmetic.Unit` with abstract rational scaling witnesses; keeping it
    inline in `Arithmetic` made typechecking too slow.
- Archimedean statement for the constructive apartness-field structure is
  still available separately from `Cubical.DedekindCut.Archimedean` and should
  be packaged with the final bridge if a single record is introduced.

Note: the old `Constructive.Algebra.OrderedField` record factored through
`StrictlyOrderedCommRing`, whose structure field includes trichotomy, and
Cubical's `Field` asks for inverses from mere inequality `x != 0`.  That
strict API has been moved to `Constructive.Algebra.StrictlyOrderedField`.
The new `Constructive.Algebra.OrderedField` record is the LEM-free target and
uses inverses from apartness `x # 0`.

### M4. LEM Bridge to MacNeille Completeness

Status: pending.  M2 and M3 are now available constructively.

In a separate LEM-dependent module:

1. Take a nonempty bounded powerset/subset `A` of `DedekindCut`.
2. Use LEM to define the associated located real-valued cut:
   lower side: `x` is below some member of `A`;
   upper side: `x` is an upper bound of `A`, rounded upward.
3. Apply M2 to obtain the representing cut.
4. Prove it is the supremum of `A`.
5. Package this with M3 as `MacNeilleCompleteOrderedField`.

## Current Work Item

M3 is complete for the LEM-free target.  The next step is the LEM bridge from
constructive Dedekind completeness to the existing MacNeille completeness
interface.
