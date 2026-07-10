#!/usr/bin/env bash

set -o pipefail

repo_root=$(git rev-parse --show-toplevel 2>/dev/null) || {
  printf '%s\n' 'error: run this script inside a Git worktree' >&2
  exit 2
}
cd "$repo_root" || exit 2

if [[ ${1-} == -- ]]; then
  shift
fi

failed=0

if ! git diff --check -- "$@"; then
  failed=1
fi

if ! git diff --cached --check -- "$@"; then
  failed=1
fi

check_untracked() {
  local source_file exit_code
  local untracked_failed=0

  while IFS= read -r -d '' source_file; do
    if [[ -d "$source_file" && ! -L "$source_file" ]]; then
      printf 'error: cannot check untracked directory: %q\n' "$source_file" >&2
      untracked_failed=1
      continue
    fi

    git diff --no-index --check -- /dev/null "$source_file"
    exit_code=$?

    # Status 1 is the expected difference from an empty file.
    case "$exit_code" in
      0|1) ;;
      *) untracked_failed=1 ;;
    esac
  done

  return "$untracked_failed"
}

if ! git ls-files --others --exclude-standard -z -- "$@" |
  check_untracked
then
  failed=1
fi

exit "$failed"
