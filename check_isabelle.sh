#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AUDIT_DIR="$ROOT_DIR/reports/audit_goodman_complete"

exec isabelle build -j 1 \
  -D "$ROOT_DIR" \
  -D "$AUDIT_DIR"
