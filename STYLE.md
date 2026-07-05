# Style Guide

Repository-wide style and naming conventions.

## General Style

- Align with the Cubical Agda library's naming, module organization, imports,
  and proof style whenever there is an established Cubical convention.
- Follow the style of nearby modules before introducing a new pattern.
- Prefer short mathematical names over implementation labels.
- Keep public names stable when reasonable.
- Avoid names that encode temporary project state or implementation strategy.

## Modules And Imports

- Use descriptive module names that match the mathematical object or structure.
- Keep aggregate modules as the public entry points for larger topics.
- When moving a module, update imports, aggregate modules, and documentation in
  the same change.
- Prefer explicit qualification over import-order fixes when names are
  ambiguous.

## Comments

- Keep comments concise and mathematical.
- Explain definitions, assumptions, or non-obvious proof choices.
- Do not leave temporary notes, milestone names, or scratch explanations in
  public modules.

## Documentation

- Keep README-style prose direct and specific.
- State what the library proves or provides without promotional wording.
- If a result is imported from Cubical or another dependency, describe it as
  such rather than implying this repository reproves it.

## Proof Names

- Name lemmas after the mathematical relation they express.
- Prefer existing vocabulary from Cubical and nearby project modules.
- Use helper names only for local, private proof plumbing.
- Promote a helper to a meaningful name when it becomes shared or appears in a
  public interface.
