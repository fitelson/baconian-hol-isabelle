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

## Isabelle build serialization

Run every actual Isabelle build, forced rebuild, export, or graph extraction
serially. Confirm that the shared Isabelle session database is idle before
starting one. Use `./check_isabelle.sh` for the complete maintained
verification. Do not add `sorry`, `oops`, `admit`, or `quick_and_dirty`.
