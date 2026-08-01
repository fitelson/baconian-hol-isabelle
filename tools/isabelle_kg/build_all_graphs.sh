#!/bin/sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

"$SCRIPT_DIR/build_bacon_graph.sh"
"$SCRIPT_DIR/build_zalta_graph.sh"
