# Project Instructions

## Start here

Before changing the development, read `README.md`, then `STATUS.md`, then
`docs/REPOSITORY_STRUCTURE.md`. For work on Goodman's question, additionally
read `theories/goodman/README.md` and
`reports/GOODMAN_COMPLETE_VERIFICATION_MATRIX_2026-07-27.md`. The primary
source PDFs used for fidelity checks are indexed in `sources/README.md`.

Goodman's central consistency question remains open. Treat
`theories/goodman/models/hol_zf/canonical/` as the official reconstruction of
Bacon's appendix model. Results confined to
`theories/goodman/models/hol_zf/secondary/` are comparison or experimental
results and must not be presented as results about Bacon's exact model.

The Isabelle sources and checked theorem objects determine formal status;
documentation summarizes them but does not strengthen their scope. Preserve
the distinction between derivability, conditional semantic results, and
exact-model instantiations.

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

Use `./check_isabelle.sh` for the complete maintained verification. Do not add
`sorry`, `oops`, `admit`, or `quick_and_dirty`.
