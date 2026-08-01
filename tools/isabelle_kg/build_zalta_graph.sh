#!/bin/sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/../.." && pwd)
OUTPUT_DIR=${1:-"$PROJECT_ROOT/isabelle-kg/zalta"}
CLASSES_DIR="$OUTPUT_DIR/classes"
GRAPH_JSON="$OUTPUT_DIR/graph.json"
GRAPHML="$OUTPUT_DIR/graph.graphml"
SCALA_SOURCE="$SCRIPT_DIR/src/Isabelle_KG.scala"
ISABELLE_SCALA_JAR=$(isabelle getenv -b ISABELLE_SCALA_JAR)
ISABELLE_CLASSPATH=$(isabelle getenv -b ISABELLE_CLASSPATH)
TOOL_CLASSPATH="$ISABELLE_SCALA_JAR:$ISABELLE_CLASSPATH:$CLASSES_DIR"

mkdir -p "$CLASSES_DIR"

build_session() {
  isabelle build -j 1 \
    -d "$PROJECT_ROOT/theories/zalta" \
    -o export_theory=true \
    AOT
}

force_export_session() {
  isabelle build -j 1 -f \
    -d "$PROJECT_ROOT/theories/zalta" \
    -o export_theory=true \
    AOT
}

compile_extractor() {
  find "$CLASSES_DIR" -type f -delete
  isabelle scalac \
    -classpath "$ISABELLE_SCALA_JAR:$ISABELLE_CLASSPATH" \
    -d "$CLASSES_DIR" \
    "$SCALA_SOURCE"

  if [ ! -f "$CLASSES_DIR/isabelle/Isabelle_KG.class" ]; then
    echo "Scala compilation failed: Isabelle_KG.class was not produced." >&2
    exit 1
  fi
}

run_extractor() {
  isabelle java \
    -classpath "$TOOL_CLASSPATH" \
    isabelle.Isabelle_KG \
    "$PROJECT_ROOT" \
    "$GRAPH_JSON" \
    AOT
}

semantic_graph_present() {
  python3 - "$GRAPH_JSON" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    graph = json.load(stream)

counts = graph.get("stats", {}).get("edge_kinds", {})
if counts.get("DEPENDS_ON", 0) <= 0 or counts.get("USES_CONSTANT", 0) <= 0:
    raise SystemExit(1)

nodes = graph.get("nodes", [])
names = {node.get("short_name") for node in nodes}
required = {"AOT", "AOT_PLM", "AOT_TruthmakerSemantics"}
if not required <= names:
    raise SystemExit(f"Missing AOT graph nodes: {sorted(required - names)}")

if any(
    "theories/base/" in node.get("file", "")
    or "theories/classicism/" in node.get("file", "")
    or "theories/goodman/" in node.get("file", "")
    for node in nodes
):
    raise SystemExit("Bacon-family material leaked into the Zalta graph")
PY
}

build_session
compile_extractor
run_extractor

if ! semantic_graph_present; then
  echo "Theory bodies were absent; forcing one AOT export_theory rebuild." >&2
  force_export_session
  run_extractor
  if ! semantic_graph_present; then
    echo "AOT semantic extraction failed after the forced rebuild." >&2
    exit 1
  fi
fi

python3 "$SCRIPT_DIR/json_to_graphml.py" "$GRAPH_JSON" "$GRAPHML"
python3 "$SCRIPT_DIR/validate_graph.py" "$GRAPH_JSON" "$GRAPHML"
python3 "$SCRIPT_DIR/query_graph.py" --graph "$GRAPH_JSON" stats
