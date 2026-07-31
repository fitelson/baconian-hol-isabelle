#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"

python3 -m unittest pure_diagonal_search.test_pure_diagonal_search -v
python3 -m pure_diagonal_search.run_search \
  --max-builder-size 6 \
  --max-candidates 4 \
  --per-cell-cap 0 \
  --rounds 8 \
  --node-cap 20000 \
  --output pure_diagonal_search/runs/check
