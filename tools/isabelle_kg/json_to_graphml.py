#!/usr/bin/env python3
"""Convert the Isabelle knowledge graph JSON to dependency-preserving GraphML."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import xml.etree.ElementTree as ET


GRAPHML = "http://graphml.graphdrawing.org/xmlns"
ET.register_namespace("", GRAPHML)


def qname(name: str) -> str:
    return f"{{{GRAPHML}}}{name}"


NODE_FIELDS = (
    "kind",
    "name",
    "short_name",
    "theory",
    "session",
    "file",
    "line",
    "statement",
    "type",
    "external",
)
EDGE_FIELDS = ("kind", "theory")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    graph = json.loads(args.input.read_text(encoding="utf-8"))
    root = ET.Element(qname("graphml"))

    for field in NODE_FIELDS:
        ET.SubElement(
            root,
            qname("key"),
            {
                "id": f"n_{field}",
                "for": "node",
                "attr.name": field,
                "attr.type": "boolean"
                if field in {"external"}
                else "int"
                if field in {"line"}
                else "string",
            },
        )
    for field in EDGE_FIELDS:
        ET.SubElement(
            root,
            qname("key"),
            {
                "id": f"e_{field}",
                "for": "edge",
                "attr.name": field,
                "attr.type": "string",
            },
        )

    graph_element = ET.SubElement(
        root, qname("graph"), {"id": "IsabelleKG", "edgedefault": "directed"}
    )
    for node in graph["nodes"]:
        element = ET.SubElement(graph_element, qname("node"), {"id": node["id"]})
        for field in NODE_FIELDS:
            value = node.get(field, "")
            data = ET.SubElement(element, qname("data"), {"key": f"n_{field}"})
            if isinstance(value, bool):
                data.text = str(value).lower()
            else:
                data.text = str(value)

    for index, edge in enumerate(graph["edges"]):
        element = ET.SubElement(
            graph_element,
            qname("edge"),
            {
                "id": f"e{index}",
                "source": edge["source"],
                "target": edge["target"],
            },
        )
        for field in EDGE_FIELDS:
            data = ET.SubElement(element, qname("data"), {"key": f"e_{field}"})
            data.text = str(edge.get(field, ""))

    args.output.parent.mkdir(parents=True, exist_ok=True)
    tree = ET.ElementTree(root)
    ET.indent(tree, space="  ")
    tree.write(args.output, encoding="utf-8", xml_declaration=True)


if __name__ == "__main__":
    main()
