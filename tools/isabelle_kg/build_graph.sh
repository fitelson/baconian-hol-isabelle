#!/bin/sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/../.." && pwd)
OUTPUT_DIR=${1:-"$PROJECT_ROOT/isabelle-kg"}
CLASSES_DIR="$OUTPUT_DIR/classes"
GRAPH_JSON="$OUTPUT_DIR/graph.json"
GRAPHML="$OUTPUT_DIR/graph.graphml"
SCALA_SOURCE="$SCRIPT_DIR/src/Isabelle_KG.scala"
ISABELLE_SCALA_JAR=$(isabelle getenv -b ISABELLE_SCALA_JAR)
ISABELLE_CLASSPATH=$(isabelle getenv -b ISABELLE_CLASSPATH)
TOOL_CLASSPATH="$ISABELLE_SCALA_JAR:$ISABELLE_CLASSPATH:$CLASSES_DIR"

mkdir -p "$CLASSES_DIR"

build_sessions() {
  isabelle build -j 1 "$@" -D "$PROJECT_ROOT" \
    -D "$PROJECT_ROOT/reports/audit_modal_quantified" \
    -o export_theory=true
}

force_export_sessions() {
  isabelle build -j 1 -f -d "$PROJECT_ROOT" \
    -d "$PROJECT_ROOT/reports/audit_modal_quantified" \
    -o export_theory=true \
    Bacon_Base \
    Bacon_Classicism \
    Goodman_CEVplus \
    Higher_Order_Metaphysics_PP \
    Higher_Order_Metaphysics_PP_Frontier \
    Higher_Order_Metaphysics_PP_Models \
    Higher_Order_Metaphysics_PP_ZF_Model \
    Higher_Order_Metaphysics_PP_ZF_Truth_Functions \
    Higher_Order_Metaphysics_PP_ZF_Necessity \
    Higher_Order_Metaphysics_PP_ZF_Possibility \
    Higher_Order_Metaphysics_PP_ZF_Higher_Order_Quantified \
    Higher_Order_Metaphysics_PP_ZF_Fun_Prime \
    Higher_Order_Metaphysics_PP_ZF_T6_Diagonal \
    Higher_Order_Metaphysics_PP_ZF_Modal_Depth_Two \
    Goodman_CEVplus_Canonical \
    Goodman_CEVplus_ZF_Bridge \
    Goodman_CEVplus_Modal_Quantified_Bridge \
    Goodman_Modal_Quantified_Audit_2026_07_28
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
    Bacon_Base \
    Bacon_Classicism \
    Goodman_CEVplus \
    Higher_Order_Metaphysics_PP \
    Higher_Order_Metaphysics_PP_Frontier \
    Higher_Order_Metaphysics_PP_Models \
    Higher_Order_Metaphysics_PP_ZF_Model \
    Higher_Order_Metaphysics_PP_ZF_Truth_Functions \
    Higher_Order_Metaphysics_PP_ZF_Necessity \
    Higher_Order_Metaphysics_PP_ZF_Possibility \
    Higher_Order_Metaphysics_PP_ZF_Higher_Order_Quantified \
    Higher_Order_Metaphysics_PP_ZF_Fun_Prime \
    Higher_Order_Metaphysics_PP_ZF_T6_Diagonal \
    Higher_Order_Metaphysics_PP_ZF_Modal_Depth_Two \
    Goodman_CEVplus_Canonical \
    Goodman_CEVplus_ZF_Bridge \
    Goodman_CEVplus_Modal_Quantified_Bridge \
    Goodman_Modal_Quantified_Audit_2026_07_28
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

required_dependencies = {
    "theorem:Bacon_PP_ZF_Fresh_Constant_Builder_Fragment_Model."
    "pp_constant_builder_fragment_PP_axioms_consistent",
    "theorem:Bacon_PP_Fresh_ZF_Fragment_Bridge."
    "fresh_goodman_constant_builder_only_consistent",
    "theorem:Bacon_PP_ZF_Fresh_Binary_Truth_Functions_Fragment_Model."
    "pp_binary_truth_fragment_PP_axioms_consistent",
    "theorem:Bacon_PP_Fresh_ZF_Fragment_Bridge."
    "fresh_goodman_binary_truth_only_consistent",
    "theorem:Bacon_PP_ZF_Fresh_Necessity_Fragment_Model."
    "pp_necessity_fragment_PP_axioms_consistent",
    "theorem:Bacon_PP_ZF_Fresh_Possibility_Fragment_Model."
    "pp_possibility_fragment_PP_axioms_consistent",
    "theorem:Bacon_PP_ZF_Fresh_Higher_Order_Quantified_Fragment_Model."
    "pp_quantified_fragment_PP_axioms_consistent",
    "theorem:Bacon_PP_Fresh_ZF_Modal_Quantified_Bridge."
    "fresh_goodman_modal_quantified_only_consistent",
    "theorem:Bacon_PP_ZF_Fresh_Fun_Prime_Fragment_Model."
    "pp_t_fun_prime_stabilizes",
    "theorem:Bacon_PP_ZF_Fresh_T6_Diagonal_Fragment_Model."
    "pp_t_T6_diagonal_absorption_failure_iff",
    "theorem:Bacon_PP_ZF_Goodman_L2_Child_Xor."
    "pp_b_child_xor_refutes_exact_L2",
    "theorem:Bacon_PP_ZF_Goodman_L2_Child_Xor."
    "pp_b_child_xor_refutes_exact_strong_L2",
    "theorem:Bacon_PP_ZF_Goodman_M5_Full_Rebuilt_Model."
    "pp_t_M5_full_rebuilt_exotic_certificate",
    "theorem:Bacon_PP_ZF_Goodman_M5_Full_Rebuilt_Model."
    "pp_t_M5_full_rebuilt_model",
}
sources = {
    edge["source"]
    for edge in graph.get("edges", [])
    if edge.get("kind") == "DEPENDS_ON"
}
if not required_dependencies <= sources:
    raise SystemExit(1)
PY
}

build_sessions
compile_extractor
run_extractor

if ! semantic_graph_present; then
  echo "Theory bodies were absent; forcing one export_theory rebuild." >&2
  force_export_sessions
  run_extractor
  if ! semantic_graph_present; then
    echo "Semantic extraction failed after the forced rebuild." >&2
    exit 1
  fi
fi

python3 "$SCRIPT_DIR/json_to_graphml.py" "$GRAPH_JSON" "$GRAPHML"
python3 "$SCRIPT_DIR/validate_graph.py" "$GRAPH_JSON" "$GRAPHML"
python3 "$SCRIPT_DIR/query_graph.py" --graph "$GRAPH_JSON" stats
