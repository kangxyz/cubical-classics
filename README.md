# ¬¬||🧊|| : Cubical Classics

> From program halts in the tale,
> towards program only *Übermensch* is able to run.

`cubical-classics` is an experimental Agda library for doing classical
mathematics in Cubical Agda. It contains classical principles, ordered algebra, Dedekind cuts, real
numbers, and some basic real analysis.

We are open to advice and contributions!

## Dependencies

This project tracks the current development version of
[the Cubical Agda library](https://github.com/agda/cubical), not the latest
tagged release.

Known working setup:

- Agda 2.8.0
- Cubical Agda library `master`, tested at commit `9216603`

Older Cubical releases, including the `v0.9` checkout, are not expected to
work. The code uses APIs from:

- `Cubical.Axiom.Choice`, `Cubical.Axiom.ExcludedMiddle`, and
  `Cubical.Axiom.Omniscience`;
- `Cubical.Data.Int` and `Cubical.Data.Rationals`;
- `Cubical.Algebra.OrderedCommRing` and `Cubical.Algebra.Field`;
- the current `Lift` API.

To type-check the library:

```sh
agda --build-library
```

## Layout

- `Constructive/` is for code that does not use the library's classical
  `Oracle`: preliminary lemmas, ordered rings and fields, morphisms, and the
  `ℤ` and `ℚ` instances.
- `Classical/` is for the axiom interface and the parts that use it:
  powersets, topology, Dedekind cuts, the real numbers, and real analysis.

## Contents

At the moment the library has:

- excluded middle, choice, Diaconescu's theorem, omniscience principles, and
  local propositional resizing;
- constructive lemmas for logic and natural numbers, plus classical wrappers
  for LPO and oracle-based search;
- ordered commutative rings, strictly ordered commutative rings, ordered
  fields, ordered morphisms, Archimedean structures, and the canonical
  embeddings of `ℤ` and `ℚ`;
- impredicative powersets, with membership, Boolean operations, finiteness,
  and finite big operations;
- topological spaces, neighbourhoods, Hausdorff spaces, compactness, and
  metric spaces;
- Dedekind cuts and the construction of the real numbers as a complete
  Archimedean ordered field;
- elementary real analysis, including sequences, Cauchy convergence,
  monotone convergence, Bolzano-Weierstrass, Heine-Borel, and the
  intermediate value theorem.
