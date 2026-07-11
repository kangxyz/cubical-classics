#!/usr/bin/env bash

set -o pipefail

repo_root=$(git rev-parse --show-toplevel 2>/dev/null) || {
  printf '%s\n' 'error: run this script inside a Git worktree' >&2
  exit 2
}
cd "$repo_root" || exit 2

document=docs/ARCHITECTURE.md
temporary_directory=$(mktemp -d "${TMPDIR:-/tmp}/architecture-audit.XXXXXX") || exit 2
trap 'rm -rf "$temporary_directory"' EXIT

rows_file=$temporary_directory/rows
seen_modules=$temporary_directory/modules
seen_files=$temporary_directory/files
: > "$seen_modules"
: > "$seen_files"

if ! awk '
  $0 == "<!-- BEGIN STABLE PUBLIC ENTRY TABLE -->" {
    if (inside || starts != 0) bad = 1
    inside = 1
    starts++
    next
  }
  $0 == "<!-- END STABLE PUBLIC ENTRY TABLE -->" {
    if (!inside || ends != 0) bad = 1
    inside = 0
    ends++
    next
  }
  inside && $0 == "| Module | Kind | Scope |" { headers++; next }
  inside && $0 == "| --- | --- | --- |" { separators++; next }
  inside && /^\|/ { print; next }
  inside && NF {
    printf "error: unexpected table content at %s:%d\n", FILENAME, NR > "/dev/stderr"
    bad = 1
  }
  END {
    if (starts != 1 || ends != 1 || inside || headers != 1 || separators != 1 || bad)
      exit 1
  }
' "$document" > "$rows_file"; then
  printf '%s\n' 'error: malformed or missing stable-entry table markers' >&2
  exit 1
fi

row_pattern='^\| \[`([^`]*)`\]\(\.\./([^)]*[.]agda)\) \| `(aggregate|direct)` \| [^|]+ \|$'
failed=0
entry_count=0
aggregate_count=0
direct_count=0

while IFS= read -r row; do
  if [[ ! $row =~ $row_pattern ]]; then
    printf 'error: malformed stable-entry row: %s\n' "$row" >&2
    failed=1
    continue
  fi

  module_name=${BASH_REMATCH[1]}
  source_file=${BASH_REMATCH[2]}
  kind=${BASH_REMATCH[3]}
  entry_count=$((entry_count + 1))

  if grep -Fqx "$module_name" "$seen_modules"; then
    printf 'error: duplicate stable module: %s\n' "$module_name" >&2
    failed=1
  else
    printf '%s\n' "$module_name" >> "$seen_modules"
  fi

  if grep -Fqx "$source_file" "$seen_files"; then
    printf 'error: duplicate stable module path: %s\n' "$source_file" >&2
    failed=1
  else
    printf '%s\n' "$source_file" >> "$seen_files"
  fi

  expected_module=${source_file%.agda}
  expected_module=${expected_module//\//.}
  if [[ $module_name != "$expected_module" ]]; then
    printf 'error: label %s does not match path %s\n' "$module_name" "$source_file" >&2
    failed=1
  fi

  if [[ ! -f $source_file ]]; then
    printf 'error: stable module does not exist: %s\n' "$source_file" >&2
    failed=1
    continue
  fi

  declared_module=$(awk '$1 == "module" { print $2; exit }' "$source_file")
  if [[ $declared_module != "$module_name" ]]; then
    printf 'error: %s declares module %s, expected %s\n' \
      "$source_file" "${declared_module:-<none>}" "$module_name" >&2
    failed=1
  fi

  if [[ $kind == aggregate ]]; then
    aggregate_count=$((aggregate_count + 1))
    if ! awk '
      /^[[:space:]]*open[[:space:]]+import([[:space:]]|$)/ { in_import = 1 }
      in_import && /(^|[[:space:]])public([[:space:]]|$)/ { found = 1 }
      in_import && /^[[:space:]]*$/ { in_import = 0 }
      in_import && /^[^[:space:]]/ &&
        !/^[[:space:]]*open[[:space:]]+import([[:space:]]|$)/ { in_import = 0 }
      END { exit(found ? 0 : 1) }
    ' "$source_file"; then
      printf 'error: aggregate has no public import: %s\n' "$source_file" >&2
      failed=1
    fi
  else
    direct_count=$((direct_count + 1))
  fi
done < "$rows_file"

if (( entry_count == 0 )); then
  printf '%s\n' 'error: stable-entry table has no modules' >&2
  failed=1
fi

if (( failed != 0 )); then
  exit 1
fi

analysis_root=Constructive/Analysis

while IFS= read -r -d '' source_file; do
  expected_module=${source_file%.agda}
  expected_module=${expected_module//\//.}
  declared_module=$(awk '$1 == "module" { print $2; exit }' "$source_file")
  if [[ $declared_module != "$expected_module" ]]; then
    printf 'error: %s declares module %s, expected %s\n' \
      "$source_file" "${declared_module:-<none>}" "$expected_module" >&2
    failed=1
  fi

  while IFS= read -r imported_module; do
    imported_file=${imported_module//.//}.agda
    if [[ ! -f $imported_file ]]; then
      printf 'error: unresolved Analysis import %s in %s\n' \
        "$imported_module" "$source_file" >&2
      failed=1
    fi
  done < <(
    perl -0ne '
      while (/(?:open\s+)?import\s+(Constructive[.]Analysis[.][A-Za-z0-9_.]+)/g) {
        print "$1\n";
      }
    ' "$source_file" | sort -u
  )
done < <(find "$analysis_root" -type f -name '*.agda' -print0)

forbidden_pattern='Arithmetic[.]RationalTranslation|Arithmetic[.]Sign|Extension[.]Unary[.]Core|Closeness[.]Prelength|Reals[.]Comparison|Series[.]Instances[.]Geometric|PowerSeries[.]Instances|PowerSeries[.]TermwiseDerivative|PowerSeries[.]DerivativeConvergence|StrictSubball[.]OnBall|Recenter[.](StripFinite|Theorem)|PowerSeries[.]Radius[.]Sum|PowerSeries[.]Analytic[.]Core|PowerSeries[.]Continuity[.](Theorem|Subball)|PowerSeries[.]Algebra[.]Convergence|Atanh[.]Derivative[.]Core|Logarithm[.]FunctionalEquation[.]Core'
if rg -n "$forbidden_pattern" Constructive Classical docs README.md \
    -g '*.agda' -g '*.md' -g '!Constructive/Analysis/PLAN.md'; then
  printf '%s\n' 'error: forbidden legacy Analysis path remains' >&2
  failed=1
fi

if rg -n '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+Classical([.]|$)' \
    "$analysis_root" -g '*.agda'; then
  printf '%s\n' 'error: constructive Analysis imports Classical' >&2
  failed=1
fi

if rg -n 'PowerSeries[.]Elementary[.]Logarithm' \
    Constructive/Analysis/Reals/PowerSeries/Elementary/Atanh -g '*.agda'; then
  printf '%s\n' 'error: Atanh depends back on Logarithm' >&2
  failed=1
fi

if rg -n 'PowerSeries[.]Differentiation' \
    Constructive/Analysis/Reals/PowerSeries/Recenter -g '*.agda'; then
  printf '%s\n' 'error: Recenter depends on differentiation implementation' >&2
  failed=1
fi

while IFS= read -r -d '' source_file; do
  case $source_file in
    */PowerSeries.agda|*/PowerSeries/Examples*|*/PowerSeries/Elementary*)
      continue
      ;;
  esac
  if rg -q 'PowerSeries[.](Examples|Elementary)' "$source_file"; then
    printf 'error: core power-series layer imports examples/elementary code: %s\n' \
      "$source_file" >&2
    failed=1
  fi
done < <(find Constructive/Analysis/Reals/PowerSeries -type f -name '*.agda' -print0)

approved_facades=$temporary_directory/approved-facades
cat > "$approved_facades" <<'EOF'
Constructive/Analysis/Completions.agda
Constructive/Analysis/Completions/CauchyCompletion.agda
Constructive/Analysis/Completions/CauchyCompletion/Closeness.agda
Constructive/Analysis/Completions/CauchyCompletion/Extension.agda
Constructive/Analysis/Completions/DedekindCompletion.agda
Constructive/Analysis/Completions/DedekindCompletion/Arithmetic.agda
Constructive/Analysis/FixedPoint.agda
Constructive/Analysis/GeometricDecay.agda
Constructive/Analysis/Metric.agda
Constructive/Analysis/Metric/Core.agda
Constructive/Analysis/Reals.agda
Constructive/Analysis/Reals/Calculus.agda
Constructive/Analysis/Reals/CauchyReals.agda
Constructive/Analysis/Reals/CauchyReals/Arithmetic.agda
Constructive/Analysis/Reals/CauchyReals/Arithmetic/Ordered.agda
Constructive/Analysis/Reals/CauchyReals/Arithmetic/Quantitative.agda
Constructive/Analysis/Reals/CauchyReals/Base.agda
Constructive/Analysis/Reals/CauchyReals/Order.agda
Constructive/Analysis/Reals/CauchyReals/Order/Bounds.agda
Constructive/Analysis/Reals/IVT.agda
Constructive/Analysis/Reals/Interval.agda
Constructive/Analysis/Reals/PowerSeries.agda
Constructive/Analysis/Reals/PowerSeries/Algebra.agda
Constructive/Analysis/Reals/PowerSeries/Analytic.agda
Constructive/Analysis/Reals/PowerSeries/Calculus.agda
Constructive/Analysis/Reals/PowerSeries/CauchyProduct.agda
Constructive/Analysis/Reals/PowerSeries/Core.agda
Constructive/Analysis/Reals/PowerSeries/Differentiation.agda
Constructive/Analysis/Reals/PowerSeries/Elementary.agda
Constructive/Analysis/Reals/PowerSeries/Elementary/Arctangent.agda
Constructive/Analysis/Reals/PowerSeries/Elementary/Atanh.agda
Constructive/Analysis/Reals/PowerSeries/Elementary/Exponential.agda
Constructive/Analysis/Reals/PowerSeries/Elementary/FactorialBounds.agda
Constructive/Analysis/Reals/PowerSeries/Elementary/Logarithm.agda
Constructive/Analysis/Reals/PowerSeries/Elementary/Logarithm/FunctionalEquation.agda
Constructive/Analysis/Reals/PowerSeries/Elementary/Trigonometric.agda
Constructive/Analysis/Reals/PowerSeries/Examples.agda
Constructive/Analysis/Reals/PowerSeries/Examples/Polynomial.agda
Constructive/Analysis/Reals/PowerSeries/Radius.agda
Constructive/Analysis/Reals/PowerSeries/Recenter.agda
Constructive/Analysis/Reals/Sequences.agda
Constructive/Analysis/Reals/Series.agda
Constructive/Analysis/Reals/Series/CauchyProduct.agda
EOF

while IFS= read -r -d '' source_file; do
  if ! rg -q '(^|[[:space:]])public([[:space:]]|$)' "$source_file"; then
    continue
  fi
  if rg -q '^[[:space:]]*(record|data|[A-Za-z_][A-Za-z0-9_ᶜ⁺⁻≤<>=→←∥Σℕℚℝ-]*)[[:space:]]*:' \
      "$source_file"; then
    continue
  fi
  if ! grep -Fqx "$source_file" "$approved_facades"; then
    printf 'error: unapproved public-import facade: %s\n' "$source_file" >&2
    failed=1
  fi
done < <(find "$analysis_root" -type f -name '*.agda' -print0)

if (( failed != 0 )); then
  exit 1
fi

printf 'architecture entries: %d (%d aggregate, %d direct)\n' \
  "$entry_count" "$aggregate_count" "$direct_count"
