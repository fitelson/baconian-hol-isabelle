# Project Instructions

## Isabelle knowledge graph

Use the project's exact Isabelle-native graph as the default source for
theory structure, theorem dependencies, imports, entity lookup, source
locations, and change-impact analysis:

```text
tools/isabelle_kg/query_graph.py stats
tools/isabelle_kg/query_graph.py search QUERY
tools/isabelle_kg/query_graph.py explain ENTITY
tools/isabelle_kg/query_graph.py deps ENTITY --depth N
tools/isabelle_kg/query_graph.py used-by ENTITY --depth N
tools/isabelle_kg/query_graph.py path SOURCE TARGET
```

The graph is `isabelle-kg/graph.json`. If it is missing or stale relative to
the active `.thy` files or `ROOT`, rebuild and validate it with
`tools/isabelle_kg/build_graph.sh`.

This hand-rolled graph replaces Graphify as the default for this project.
Do not run Graphify automatically. Use it only if explicitly requested or if
the Isabelle-native graph cannot represent the required non-Isabelle
relation, and explain the exception first.
