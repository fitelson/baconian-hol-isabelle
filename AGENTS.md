# Project Instructions

## Isabelle knowledge graph

For every question about Isabelle theories, theorem dependencies, imports,
entities, source locations, or change impact, use the project's
Isabelle-native knowledge graph before broad text search:

```text
tools/isabelle_kg/query_graph.py stats
tools/isabelle_kg/query_graph.py search QUERY
tools/isabelle_kg/query_graph.py explain ENTITY
tools/isabelle_kg/query_graph.py deps ENTITY --depth N
tools/isabelle_kg/query_graph.py used-by ENTITY --depth N
tools/isabelle_kg/query_graph.py path SOURCE TARGET
```

The graph is `isabelle-kg/graph.json`. If it is missing or older than the
active `.thy` files or `ROOT`, rebuild and validate it with:

```text
tools/isabelle_kg/build_graph.sh
```

This hand-rolled graph is the default project knowledge graph. Do not run
Graphify automatically in this project. Use Graphify only when the user
explicitly requests it or when the Isabelle-native graph cannot represent the
required non-Isabelle relation, and state that reason first.

## Isabelle build serialization

Run every actual Isabelle build, forced rebuild, export, or graph extraction
serially. Agents may inspect Isabelle sources in parallel, but no agent may
start `isabelle build` while another build or export is active. Before starting
a build, coordinate with the other agents and confirm that the shared Isabelle
session database is idle.
