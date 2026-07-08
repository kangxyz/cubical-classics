# Style Guide

Repository-wide style and naming conventions.  Use this file together with
`docs/DEVELOPMENT.md`; this file governs names, module shape, comments, and
proof-code style, while `docs/DEVELOPMENT.md` records boundaries and checks.

## Cubical Defaults

Follow the Cubical Agda library unless this repository has a more specific
local convention.  In particular, follow Cubical's `NAMING.md` and, for
algebraic structures and laws, `Cubical/Algebra/NAMING.md`.

- Read nearby modules before introducing a new naming pattern.
- Keep public names stable when reasonable.
- Prefer short mathematical names over implementation labels.
- Avoid names that encode temporary project state, generation strategy, or
  proof-search history.
- Deviate from Cubical naming only when the local mathematical boundary needs
  a different convention, and make the boundary explicit in the type, module
  context, or surrounding documentation.

## Basic Names

- Use descriptive universe-level names only when they clarify the statement;
  otherwise use `ℓ`, `ℓ'`, `ℓ''`, and so on.
- Names of types and structures begin with an uppercase letter, such as
  `OrderedField` or `MacNeilleCompleteness`.
- Names of non-type terms begin with a lowercase letter, symbolic operator, or
  established mathematical abbreviation.
- Properties begin with `is` or `has` when they are proof-relevant predicates,
  such as `isProp`, `isLocated`, or `hasLimit`.
- Do not name a public theorem after bound variables.  Prefer `+Comm`,
  `predExt`, or `limitUnique` over names like `m+n≡n+m`.
- Use `Path` or `≡` for path results, not `Eq`, `Id`, or identity-themed
  synonyms.  Results about `PathP` should end in `P` when the distinction
  matters.
- Use `Equiv` or `≃` for equivalences and `Iso` or `≅` for isomorphisms.
- For conversions, put source and target in type order, using `→` or `To` as
  appropriate: `LEM→DNE`, `isoToEquiv`, `OrderedField→Field`.
- Use `elim` and `rec` for eliminators and recursors.  Prefer qualified module
  names such as `Empty.rec`, `Prop.rec`, or `SetQuot.elim` over local renames
  like `rec-⊥`.

## Algebra And Order Names

Follow Cubical algebra naming for operation laws.

- Put the operation first and the property second: `+Comm`, `·Assoc`,
  `∧AbsorbL∨`.
- Use `L` and `R` suffixes for left and right variants: `·IdL`, `·IdR`,
  `+InvL`, `·CancelR`.
- Name distributivity by the distributed operation, side, and target operation:
  `·DistR+` for `x · (y + z)` and `·DistL+` for `(x + y) · z`.
- Use Cubical's common abbreviations: `Assoc`, `Comm`, `Dist`, `Id`, `Inv`,
  `Cancel`, `Annihil`, `Idem`, `Invol`.
- Name preservation fields and lemmas as `pres<operation>` when possible, for
  example `pres+` or `pres·`.
- Structure instances include the structure name, such as `ℚCommRing` or
  `UnitGroup`.
- Use textbook mathematical names for constructions rather than category-level
  names when both are available and the code is not explicitly categorical.

For order and analysis, match the local vocabulary exactly.  Locatedness,
apartness, trichotomy, MacNeille completeness, Cauchy completeness, interval
compactness, and precision-indexed estimates are not interchangeable.

## Modules And Imports

- Use descriptive noun-based module names for mathematical objects,
  structures, and theorem clusters.
- Prefer existing file roles such as `Base`, `Properties`, `Morphism`,
  `Univalence`, `Completeness`, `Instances`, and domain-specific theorem names.
- Keep aggregate modules as public entry points.  Public imports belong mainly
  in aggregate modules whose purpose is re-exporting.
- In non-aggregate modules, avoid `public` imports unless the file is defining
  a stable interface by re-exporting a structure's fields.
- Put foundational Cubical imports first, then Cubical data/HITs/relations,
  then Cubical algebra/tactics, then repository imports from broader to nearer
  modules.
- Prefer explicit qualification or an `as` import over relying on import order
  when names collide.
- When opening a structure module, use the structure's established `Str` module
  and exported field names before adding aliases.
- When adding or moving a public module path, update aggregate modules and
  `README.md` in the same change.

## Constructive And Classical Boundaries

This repository is split by assumptions.

- `Constructive/` code must not import classical modules or use `Oracle`
  unless that boundary is deliberately redesigned and documented.
- `Classical/` code may use `Oracle`, excluded middle, choice, resizing, and
  powerset-style classical interfaces, but those assumptions should remain
  visible in the module context or exported theorem.
- When a theorem depends on `Oracle`, keep the instance argument in the
  theorem/module boundary rather than hiding it in a helper.
- Do not replace a constructive notion with a classically stronger theorem, or
  a classical theorem with a weaker constructive one, without making the change
  explicit in the name and type.

## Public API And Helpers

Public names are maintenance obligations.

- Export theorem-level results, definitions that name real mathematical
  concepts, and helpers that remove repeated proof burden across modules.
- Keep one-step wrappers, argument-order shims, namespace aliases, and solver
  plumbing private unless they clarify a real interface boundary.
- Use `private`, `where`, or `let` for local proof ingredients so the main
  results of a file remain visible.
- Promote a helper only after it is reused or appears naturally in a public
  statement.
- Avoid adding thin aliases that merely repeat Cubical or local definitions
  without shortening code, clarifying assumptions, or fixing universe/implicit
  argument policy.
- Do not expose generated scaffolding, milestone names, or temporary theorem
  names.

## Proof-Code Style

- Use `Type ℓ`, not `Set ℓ`.
- Prefer `private variable` blocks for shared variables and universe levels.
- Keep definitions maximally universe-polymorphic unless a construction is
  intentionally level-specific.
- Make arguments implicit when callers usually infer them; keep them explicit
  when they carry mathematical content or are usually supplied by hand.
- Use solvers only for fragments they cover.  Leave the surrounding order,
  apartness, truncation, and constructive data explicit.
- Prefer copattern matching when instantiating records, especially for
  structures, equivalences, and isomorphisms.
- Define records with `no-eta-equality` unless there is a concrete reason to
  use eta equality.
- Keep proof blocks readable: split long path calculations, name non-obvious
  intermediate statements, and avoid clever local abbreviations that obscure
  the theorem.

## Comments And Documentation

- Keep comments concise, mathematical, and useful for review.
- Explain definitions, assumptions, non-obvious proof choices, and links to
  external papers or theorem numbers when a file follows a source.
- Do not name top-level results `thm123`, `lem321`, or similar paper-local
  labels.  Put such references in comments above informative Agda names.
- Do not leave temporary notes, milestone labels, scratch explanations, or
  generated-code commentary in public modules.
- README-style prose should state what the library proves or provides without
  promotional wording.
- If a result is imported from Cubical or another dependency, describe it as
  imported rather than implying this repository reproves it.
- Keep lines reasonably short, with Agda and Markdown lines under 100
  characters when practical.
