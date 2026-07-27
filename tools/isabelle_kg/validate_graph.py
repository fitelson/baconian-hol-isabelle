#!/usr/bin/env python3
"""Validate the structural invariants of an Isabelle knowledge-graph export."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import xml.etree.ElementTree as ET


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("graph_json", type=Path)
    parser.add_argument("graphml", type=Path)
    args = parser.parse_args()

    graph = json.loads(args.graph_json.read_text(encoding="utf-8"))
    if graph.get("schema") != "isabelle-kg-v1":
        raise SystemExit(f"Unexpected graph schema: {graph.get('schema')!r}")

    nodes = graph.get("nodes", [])
    edges = graph.get("edges", [])
    node_ids = [node["id"] for node in nodes]
    if len(node_ids) != len(set(node_ids)):
        raise SystemExit("Duplicate node identifiers")
    known = set(node_ids)

    dangling = [
        edge
        for edge in edges
        if edge.get("source") not in known or edge.get("target") not in known
    ]
    if dangling:
        raise SystemExit(f"Dangling edge endpoints: {len(dangling)}")

    local_entities = [
        node
        for node in nodes
        if not node.get("external") and node.get("kind") != "session"
    ]
    missing_source = [
        node["id"]
        for node in local_entities
        if not node.get("file") or not node.get("line")
    ]
    if missing_source:
        raise SystemExit(
            f"Project entities without file-and-line source positions: "
            f"{len(missing_source)}"
        )

    edge_kinds = graph.get("stats", {}).get("edge_kinds", {})
    for required in ("DEPENDS_ON", "USES_CONSTANT", "USES_TYPE"):
        if edge_kinds.get(required, 0) <= 0:
            raise SystemExit(f"Missing semantic edges of kind {required}")

    graphml_nodes = 0
    graphml_edges = 0
    for _, element in ET.iterparse(args.graphml, events=("end",)):
        if element.tag.endswith("node"):
            graphml_nodes += 1
        elif element.tag.endswith("edge"):
            graphml_edges += 1
        element.clear()
    if graphml_nodes != len(nodes) or graphml_edges != len(edges):
        raise SystemExit(
            "GraphML cardinalities do not match JSON: "
            f"{graphml_nodes}/{graphml_edges} versus {len(nodes)}/{len(edges)}"
        )

    print(
        "Validated Isabelle knowledge graph: "
        f"{len(nodes)} nodes, {len(edges)} edges, "
        f"{len(local_entities)} source-positioned project entities."
    )


if __name__ == "__main__":
    main()
