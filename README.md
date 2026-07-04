# Cubical Classics

`cubical-classics` is an experimental Agda library for formalizing classical
mathematics in Cubical Agda. It develops classical principles, impredicative
powersets, ordered algebra, Dedekind cuts, and elementary real analysis on top
of the Cubical Agda library.

## Dependencies

This project tracks the current development version of
[the Cubical Agda library](https://github.com/agda/cubical), not the latest
tagged release.

Known working setup:

- Agda 2.8.0
- Cubical Agda library `master`, tested at commit `9216603`

Older Cubical releases, including the `v0.9` checkout, are not expected to
work. In particular, this repository uses APIs from:

- `Cubical.Axiom.Choice`, `Cubical.Axiom.ExcludedMiddle`, and
  `Cubical.Axiom.Omniscience`;
- `Cubical.Data.Int` and `Cubical.Data.Rationals`;
- `Cubical.Algebra.OrderedCommRing` and `Cubical.Algebra.Field`;
- the current `Lift` API.

To type-check the library:

```sh
agda --build-library
```

## Contents

The library currently includes:

- a classical interface over Cubical's excluded middle, choice,
  Diaconescu's theorem, and omniscience principles, plus local
  propositional resizing;
- basic logical and natural-number lemmas, with minimum search and LPO
  wrappers built on Cubical's natural-number minimality and omniscience
  machinery;
- strictly ordered commutative rings built on Cubical's ordered
  commutative rings, with integer and rational instances;
- ordered fields, ordered morphisms, Archimedean structures, and the
  canonical embeddings of `ℤ` and `ℚ`;
- impredicative powersets, with membership, Boolean operations, finiteness,
  and finite big operations;
- topological spaces, neighbourhoods, Hausdorff spaces, compactness, and
  metric spaces;
- Dedekind cuts and the construction of the real numbers as a complete
  Archimedean ordered field;
- elementary real analysis, including sequences, Cauchy convergence,
  monotone convergence, Bolzano-Weierstrass, Heine-Borel, and the
  intermediate value theorem.
