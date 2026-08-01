#!/bin/sh
set -eu

project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)

reader_files="
$project_dir/README.md
$project_dir/STATUS.md
$project_dir/docs/ISABELLE_TERMINOLOGY.md
$project_dir/theories/goodman/README.md
$project_dir/theories/goodman/models/hol_zf/canonical/README.md
$project_dir/theories/goodman/models/hol_zf/extensions/README.md
$project_dir/theories/goodman/models/hol_zf/secondary/README.md
$project_dir/reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.tex
$project_dir/reports/GOODMAN_COMPLETE_VERIFICATION_MATRIX_2026-07-27.md
$project_dir/theories/goodman/cevplus/Bacon_PP_Fresh_Finite_Fragment.thy
"

discouraged='self-classifying stock|central-stock|repaired-central|exact[- ]stock|cone-natural|range[- ]classifier|tag homogeneity|semantic-stock|machine-referee|negative control|load-bearing|kind fibre|positive frontier|negative frontier'

matches=$(
  # The terminology map necessarily mentions former labels; check the other
  # reader-facing files for unexplained uses.
  printf '%s\n' "$reader_files" |
    sed '/ISABELLE_TERMINOLOGY.md/d' |
    xargs rg -n -i "$discouraged" || true
)

if [ -n "$matches" ]; then
  printf '%s\n' "Reader-facing documentation contains discouraged project terminology:" >&2
  printf '%s\n' "$matches" >&2
  printf '%s\n' "Translate it or define it in Bacon--Dorr--Goodman terms." >&2
  exit 1
fi

if rg -n --pcre2 '\\ne(?![A-Za-z])' \
    "$project_dir/reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.tex"
then
  printf '%s\n' "The Goodman report contains the forbidden LaTeX command \\\\ne." >&2
  exit 1
fi

printf '%s\n' "Goodman documentation vocabulary check passed."
