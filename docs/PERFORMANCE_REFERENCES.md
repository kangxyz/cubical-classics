# Performance References

This document records upstream Agda performance reports that match local
profiling symptoms.  Use it as background when `docs/PERFORMANCE.md` points at
an unfamiliar bucket.

## GitHub Matches

The upstream Agda issue tracker has several reports that match symptoms seen in
this repository:

- [`agda/agda#4517`](https://github.com/agda/agda/issues/4517) reports
  instance search becoming expensive when small candidates are checked against
  a huge target, with module parameters contributing to term size.  This
  supports shrinking module telescopes and making instance arguments explicit.
- [`agda/agda#7784`](https://github.com/agda/agda/issues/7784) reports a case
  where an almost identical category proof became slow before the body was
  meaningful; the type signature alone was already costly, and internal
  profiling pointed at type signatures, serialization, interface
  instantiation, and positivity.  This matches `Miscellaneous` profiles where
  the exposed type is hot before the proof body matters.
- [`agda/agda#4573`](https://github.com/agda/agda/issues/4573),
  [`agda/agda#4060`](https://github.com/agda/agda/issues/4060), and
  [`agda/agda#2228`](https://github.com/agda/agda/issues/2228) are examples
  where path-heavy or record-heavy checking improved when stable helpers were
  hidden behind `abstract` or a postulate in a reduced test.  In this repo,
  `abstract` is a local performance tool only when callers do not rely on the
  helper's computational behavior.
- [`agda/agda#6721`](https://github.com/agda/agda/issues/6721) records that
  record eta rules can be a serious performance cost.  Keep
  `no-eta-equality` on large proof/data records unless eta is needed, and make
  projections explicit near expensive uses.
- [`agda/agda#7289`](https://github.com/agda/agda/issues/7289) and
  [`agda/agda#5279`](https://github.com/agda/agda/issues/5279) are cautions
  about `--lossy-unification`: it can be essential for some slow files, but it
  should not be applied blindly, and every use should be checked by reloading
  the affected module.
- [`agda/agda#1646`](https://github.com/agda/agda/issues/1646) shows scope
  checking can blow up through module alias chains.  If an internal profile
  points at scoping, reduce nested module aliases and broad public opens before
  editing mathematical proofs.

Related upstream reports that may be useful for future triage:
[`agda/agda#8589`](https://github.com/agda/agda/issues/8589),
[`agda/agda#7975`](https://github.com/agda/agda/issues/7975),
[`agda/agda#6136`](https://github.com/agda/agda/issues/6136),
[`agda/agda#8485`](https://github.com/agda/agda/issues/8485),
[`agda/agda#5060`](https://github.com/agda/agda/issues/5060), and
[`agda/agda#4628`](https://github.com/agda/agda/issues/4628).
