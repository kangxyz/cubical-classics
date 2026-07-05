# Agent Notes

DO NOT send optional commentary

Repository-wide operating rules for agents. For naming, comments,
documentation tone, and module style, follow `STYLE.md`.

## Working Principles

- Read the relevant code before changing it.
- Keep changes narrowly scoped to the user's request. Avoid unrelated
  refactors, formatting churn, or opportunistic cleanup.
- Preserve public APIs and user-facing behavior when possible.

## Boundaries And Assumptions

- Respect established boundaries between parts of the repository.
- Do not move assumptions across a boundary without making them explicit in the
  type, module context, or documentation.
- Do not replace one mathematical notion with a stronger or weaker one unless
  the surrounding code justifies it.

## Proof Engineering

- Reuse existing infrastructure before adding local helper APIs.
- Add shared lemmas only when they clarify a repeated pattern or real
  interface boundary.
- Use solvers only for the fragments they cover; keep the remaining reasoning
  explicit.
- In generic code, check universe levels and implicit arguments early.

## Verification

- Type-check the module you touched and the nearest aggregate module when
  practical.
- Run broader checks when changing shared interfaces, module paths, or
  foundational definitions.
- Always run whitespace/diff checks before reporting completion.
- If a check fails for an unrelated pre-existing reason, record the exact
  blocker and still verify the part you changed as far as possible.

## Git Hygiene

- Check the worktree state before editing and before committing.
- The worktree may contain user changes. Do not revert, delete, stage, or
  commit unrelated work.
- Stage explicit paths or hunks. Be especially careful with files that contain
  both your changes and pre-existing changes.
- Do not run destructive cleanup commands unless the user explicitly asks for
  them.
