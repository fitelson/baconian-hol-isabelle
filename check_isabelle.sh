#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AUDIT_DIR="$ROOT_DIR/reports/audit_goodman_complete"

python3 "$ROOT_DIR/tools/check_exact_bacon_boundary.py"
"$ROOT_DIR/tools/check_goodman_documentation_vocabulary.sh"

exec isabelle build -j 1 \
  -D "$ROOT_DIR" \
  -D "$AUDIT_DIR"
