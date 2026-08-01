#!/bin/sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/../.." && pwd)
OUTPUT_DIR=${1:-"$PROJECT_ROOT/isabelle-kg/bacon"}
CLASSES_DIR="$OUTPUT_DIR/classes"
GRAPH_JSON="$OUTPUT_DIR/graph.json"
GRAPHML="$OUTPUT_DIR/graph.graphml"
SCALA_SOURCE="$SCRIPT_DIR/src/Isabelle_KG.scala"
ISABELLE_SCALA_JAR=$(isabelle getenv -b ISABELLE_SCALA_JAR)
ISABELLE_CLASSPATH=$(isabelle getenv -b ISABELLE_CLASSPATH)
TOOL_CLASSPATH="$ISABELLE_SCALA_JAR:$ISABELLE_CLASSPATH:$CLASSES_DIR"

BACON_SESSIONS="
  Bacon_Base
  Bacon_Classicism
  Goodman_CEVplus
  Higher_Order_Metaphysics_PP
  Higher_Order_Metaphysics_PP_Frontier
  Higher_Order_Metaphysics_PP_Models
  Higher_Order_Metaphysics_PP_ZF_Model
  Higher_Order_Metaphysics_PP_ZF_Secondary
  Higher_Order_Metaphysics_PP_ZF_Truth_Functions
  Higher_Order_Metaphysics_PP_ZF_Necessity
  Higher_Order_Metaphysics_PP_ZF_Possibility
  Higher_Order_Metaphysics_PP_ZF_Higher_Order_Quantified
  Higher_Order_Metaphysics_PP_ZF_Fun_Prime
  Higher_Order_Metaphysics_PP_ZF_T6_Diagonal
  Goodman_CEVplus_Canonical
  Goodman_CEVplus_ZF_Bridge
  Goodman_CEVplus_Modal_Quantified_Bridge
  Goodman_CEVplus_Finite_Fragment_Model_Program
  Goodman_CEVplus_Finite_First_Cyclic_Model
  Higher_Order_Metaphysics_PP_ZF_Dual_Pair_Grafting
  Goodman_Modal_Quantified_Audit_2026_07_28
"

mkdir -p "$CLASSES_DIR"

build_sessions() {
  isabelle build -j 1 -d "$PROJECT_ROOT" \
    -d "$PROJECT_ROOT/reports/audit_modal_quantified" \
    -o export_theory=true \
    $BACON_SESSIONS
}

force_export_sessions() {
  isabelle build -j 1 -f -d "$PROJECT_ROOT" \
    -d "$PROJECT_ROOT/reports/audit_modal_quantified" \
    -o export_theory=true \
    $BACON_SESSIONS
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
    $BACON_SESSIONS
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

if any(
    node.get("name") == "AOT"
    or "theories/zalta/" in node.get("file", "")
    for node in graph.get("nodes", [])
):
    raise SystemExit("Zalta AOT material leaked into the Bacon-family graph")

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
    "theorem:Bacon_PP_Finite_Application_Graph."
    "pp_finite_acyclic_unary_values_independent_of_classifier",
    "theorem:Bacon_PP_Finite_Application_Graph."
    "pp_finite_component_condensation_acyclic",
    "theorem:Bacon_PP_Finite_Application_Graph."
    "pp_finite_first_classifier_component",
    "theorem:Bacon_PP_Finite_Fragment_Model_Program."
    "pp_finite_first_package_has_classifier_cycle",
    "theorem:Bacon_PP_ZF_Finite_First_Cyclic_Package."
    "pp_finite_first_cyclic_package_consistent",
    "theorem:Bacon_PP_ZF_Finite_First_Cyclic_Package."
    "pp_t_next_classifier_cycle_classification",
    "theorem:Bacon_PP_ZF_Finite_First_Cyclic_Package."
    "pp_t_symmetrized_probe_stabilizes_after_one_enlargement",
    "theorem:Bacon_PP_ZF_Finite_First_Cyclic_Package."
    "pp_t_symmetrized_seed_recombines_at_every_world",
    "theorem:Bacon_PP_ZF_Finite_First_Cyclic_Package."
    "pp_finite_next_cyclic_package_consistent",
    "theorem:Bacon_PP_ZF_Tree_Family_Probe_Absorption."
    "pp_t_family_probe_stabilizes_iff_collisions_absorbed",
    "theorem:Bacon_PP_ZF_Tree_Family_Probe_Absorption."
    "pp_t_diagonally_reflexive_family_probe_stabilizes",
    "theorem:Bacon_PP_ZF_Two_Component_Assembly."
    "pp_t_two_component_stock_assembly",
    "theorem:Bacon_PP_ZF_Two_Component_Assembly."
    "pp_t_finite_successor_rank_assembly",
    "theorem:Bacon_PP_ZF_Two_Component_Assembly."
    "pp_t_first_cyclic_two_component_checkpoint",
    "theorem:Bacon_PP_ZF_T6_Collision_Carrier."
    "pp_t_T6_every_finite_stage_satisfies_PP",
    "theorem:Bacon_PP_ZF_T6_Collision_Carrier."
    "pp_t_T6_every_finite_stage_equivariant",
    "theorem:Bacon_PP_ZF_T6_Collision_Carrier."
    "pp_t_T6_stage_stable_iff_global_collision",
    "theorem:Bacon_PP_ZF_T6_Collision_Carrier."
    "pp_t_T6_finite_stage_collision_candidates",
    "theorem:Bacon_PP_ZF_T6_Collision_Carrier."
    "pp_t_T6_finite_stage_stability_forces_square_failure",
    "theorem:Bacon_PP_ZF_T6_Collision_Carrier."
    "pp_t_necessary_falsity_square_iff_dense",
    "theorem:Bacon_PP_ZF_T6_Collision_Carrier."
    "pp_b_equivariance_does_not_guarantee_dense_separation",
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
