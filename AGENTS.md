# Agent Notes

This file contains rules specific to automated agents.  Repository policy has
one authoritative home for each other concern:

- [Documentation index](docs/README.md) for task-oriented navigation.
- [Architecture](docs/ARCHITECTURE.md) for ownership, assumption boundaries,
  dependency direction, and stable public entry points.
- [Style guide](STYLE.md) for names, module and proof shape, comments, and
  documentation tone.
- [Development guide](docs/DEVELOPMENT.md) for contribution workflow, plans,
  verification, and completion reporting.
- [Performance runbook](docs/performance/RUNBOOK.md) for anomalous Agda checks.

Read the relevant authority and nearby code before making a change.  Do not
copy its rules into this file.

## Communication

- Do not send routine progress commentary for expected searches, reads, or
  edits.
- Send an interim message only when the runtime requires one, the user asks
  for status, an approval or material clarification is required, or a
  long-running operation needs a status update under the runtime rules.
- Keep required updates factual: current action, discovered blocker, or next
  verification step.  Do not narrate routine searches and edits.
- In the final response, lead with the outcome and list the exact checks run.
  Distinguish passed, failed, and skipped checks, and give the exact blocker
  for any incomplete verification.

## Agda Curation Skill

- Use `$agda-theorem-first-curation` only when work requires deciding what
  counts as theorem progress or what belongs in the public Agda surface:
  generated or duplicated module cleanup, theorem-content selection or
  migration, API slimming, or review of wrapper, reexport, namespace-copy, or
  proof-plumbing inflation.
- Do not invoke it for routine proof fixes, import repairs, performance triage,
  mechanical moves or renames, or ordinary documentation.  Start with the
  standard development workflow and invoke the skill only if the task expands
  into theorem-selection or public-surface decisions.
- If the skill is unavailable, continue with the theorem-first rules in the
  [development guide](docs/DEVELOPMENT.md): name the results to prove or
  preserve, or the concrete cleanup outcome; keep support work subordinate and
  verify according to blast radius.  Report that fallback in the final
  response.

## Worktree Safety

- Check `git status --short` before editing and before any commit or staging
  operation.
- Treat existing tracked modifications and untracked files as user work.
  Preserve them unless the user explicitly puts them in scope.
- Do not revert, delete, stage, or commit unrelated paths.  Stage explicit
  paths or hunks when a file mixes user changes with agent changes.
- Do not run destructive cleanup commands unless the user explicitly requests
  them.  Remove empty directories only when they result from an in-scope move
  or deletion.
- Keep edits narrowly scoped.  Do not combine requested work with unrelated
  refactors, formatting churn, or opportunistic cleanup.
