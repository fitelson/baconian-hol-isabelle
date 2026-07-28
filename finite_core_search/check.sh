#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"

python3 -m unittest finite_core_search.test_finite_core_search -v
make -C finite_core_search/c_engine
python3 -m finite_core_search.c_input \
  --profile central_recombination \
  --type-depth 1 \
  --term-size 2 \
  --priority-extensions \
  --node-cap 2000000 \
  --output finite_core_search/runs/check_c/input.bin
finite_core_search/c_engine/finite_core_size4 \
  finite_core_search/runs/check_c/input.bin \
  2000000 \
  finite_core_search/runs/check_c/trace.txt
python3 -m finite_core_search.context_c_input \
  --profile central_recombination \
  --type-depth 1 \
  --term-size 2 \
  --priority-extensions \
  --output finite_core_search/runs/check_context_c/input.bin
finite_core_search/c_engine/finite_core_context1 \
  finite_core_search/runs/check_context_c/input.bin \
  5000000
isabelle build -j 1 -D .
python3 finite_core_search/audit_manifest.py \
  --profile central_recombination \
  --type-depth 1 \
  --type-budget 0 \
  --term-size 3 \
  --term-cell-cap 0 \
  --priority-extensions
