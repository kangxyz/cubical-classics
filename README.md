# ¬¬||🧊|| : Cubical Classics
> From program halts in the tale,
> towards program only *Übermensch* is able to run.

The `cubical-classics` is an experimental Agda library for formalizing classical mathematics in cubical type theory.
I hope someday it will have some important ideas of modern mathematics eventually.

We are open to advice and contributions!

## Dependencies

This project tracks the current development version of
[the Cubical Agda library](https://github.com/agda/cubical), not the latest
tagged release.

Known working setup:

- Agda 2.8.0
- Cubical Agda library `master`, tested at commit `9216603`

Older Cubical releases, including the `v0.9` checkout, are not expected to
work. In particular, this repository uses the newer `Cubical.Data.Int`,
`Cubical.Data.Rationals`, and `Lift` APIs.

## Contents

The library currently includes:

- classical principles such as excluded middle, Diaconescu's theorem, choice principles,
  and propositional resizing;
- basic logical and natural-number lemmas used by the later developments;
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
