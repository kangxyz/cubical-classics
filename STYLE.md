# Style Guide

This file is authoritative for naming, module and declaration shape, import
style, proof layout, comments, and repository prose.  Use it with
[Architecture](docs/ARCHITECTURE.md), which owns mathematical boundaries and
public entry points, and the [development guide](docs/DEVELOPMENT.md), which
owns workflow and verification.

## Cubical Defaults

Follow the Cubical Agda library unless this repository has a more specific
local convention.  In particular, follow Cubical's
[general naming guide](https://github.com/agda/cubical/blob/9216603/NAMING.md)
and, for algebraic structures and laws, its
[algebra naming guide](https://github.com/agda/cubical/blob/9216603/Cubical/Algebra/NAMING.md).
These links use the Cubical revision tested by this repository; local rules
take precedence when they are more specific.

- Read nearby modules before introducing a naming or layout pattern.
- Keep public names stable when reasonable.
- Prefer short mathematical names over implementation labels.
- Avoid names that encode temporary project state, generation strategy, or
  proof-search history.
- Deviate from Cubical naming only when a local mathematical distinction
  requires it.  Make that distinction visible in the type, module context, or
  adjacent documentation.

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

## Algebra And Mathematical Vocabulary

Follow Cubical algebra naming for operation laws.

- Put the operation first and the property second: `+Comm`, `·Assoc`,
  `∧AbsorbL∨`.
- Use `L` and `R` suffixes for left and right variants: `·IdL`, `·IdR`,
  `+InvL`, `·CancelR`.
- Name distributivity by the distributed operation, side, and target
  operation: `·DistR+` for `x · (y + z)` and `·DistL+` for `(x + y) · z`.
- Use Cubical's common abbreviations: `Assoc`, `Comm`, `Dist`, `Id`, `Inv`,
  `Cancel`, `Annihil`, `Idem`, `Invol`.
- Name preservation fields and lemmas as `pres<operation>` when possible, for
  example `pres+` or `pres·`.
- Structure instances include the structure name, such as `ℚCommRing` or
  `UnitGroup`.
- Use textbook mathematical names for constructions rather than
  category-level names when the code is not explicitly categorical.
- Match local analysis vocabulary exactly.  Locatedness, apartness,
  trichotomy, MacNeille completeness, Cauchy completeness, interval
  compactness, and precision-indexed estimates are not interchangeable.

## Modules And Imports

- Use descriptive noun-based module names for mathematical objects,
  structures, and theorem clusters.
- Prefer established file roles such as `Base`, `Properties`, `Morphism`,
  `Univalence`, `Completeness`, `Instances`, and domain-specific theorem names.
- Split a module around a stable mathematical concept or theorem cluster, not
  around a milestone, agent session, or generated phase number.
- Keep aggregate modules small and declarative.  Their role is to expose the
  stable imports selected by the architecture, not to contain proof logic.
- Public imports belong mainly in aggregate modules.  In non-aggregate
  modules, use a public import only when the file intentionally reexports a
  structure's fields as a stable interface.
- Put foundational Cubical imports first, then Cubical data, HIT, and relation
  imports, then Cubical algebra and tactics, then repository imports from
  broader to nearer modules.
- Prefer explicit qualification or an `as` import over relying on import order
  when names collide.
- When opening a structure module, use its established `Str` module and field
  names before adding aliases.
- Follow [Architecture](docs/ARCHITECTURE.md) to decide where a definition
  belongs and which aggregate is public.  Follow the
  [development guide](docs/DEVELOPMENT.md) when adding or moving a public path.

## Public Declarations And Helpers

Public names are maintenance obligations.

- Export theorem-level results, definitions that name mathematical concepts,
  and helpers that remove a repeated proof burden across modules.
- Keep one-step wrappers, argument-order shims, namespace aliases, and solver
  plumbing private unless they express a real interface boundary.
- Use `private`, `where`, or `let` for local proof ingredients so the main
  results remain visible.
- Promote a helper only after reuse demonstrates a stable role, or when it
  appears naturally in a public statement.
- Avoid thin aliases that repeat Cubical or local definitions without
  shortening code, clarifying assumptions, or fixing universe or implicit
  argument policy.
- Do not expose generated scaffolding, milestone names, or temporary theorem
  names.

## Proof-Code Shape

- Use `Type ℓ`, not `Set ℓ`.
- Prefer `private variable` blocks for shared variables and universe levels.
- Keep definitions universe-polymorphic unless the construction is
  intentionally level-specific.
- Make arguments implicit when callers normally infer them; keep them explicit
  when they carry mathematical content or are normally supplied by hand.
- Use solvers only for the fragment they cover.  Leave surrounding order,
  apartness, truncation, and constructive data explicit.
- Prefer copattern matching when instantiating records, especially structures,
  equivalences, and isomorphisms.
- Define records with `no-eta-equality` unless there is a concrete reason to
  use eta equality.
- Split long path calculations and name non-obvious intermediate statements.
  Avoid clever local abbreviations that obscure the theorem.

## Comments And Documentation

- Keep comments concise, mathematical, and useful for review.
- Explain definitions, assumptions, non-obvious proof choices, and links to
  external papers or theorem numbers when a file follows a source.
- Do not name top-level results `thm123`, `lem321`, or similar paper-local
  labels.  Put source labels in comments above informative Agda names.
- Do not leave scratch notes, milestones, prompt text, or generated-code
  commentary in public modules.
- Repository prose should state what the library proves or provides without
  promotional wording.
- Describe dependency results as imported rather than implying that this
  repository reproves them.
- Use descriptive Markdown links for durable navigation.  Mark illustrative
  code as schematic when it omits arguments or differs from a copyable API.
- Keep Agda and Markdown lines under 100 characters when practical.
