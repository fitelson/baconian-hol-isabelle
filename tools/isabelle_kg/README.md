# Isabelle-native knowledge graph

These tools extract a graph from Isabelle's elaborated session database. They
do not parse `.thy` files heuristically. Isabelle supplies the theories,
entities, source positions, formal statements, constant and type occurrences,
locale dependencies, and direct theorem dependencies.

The generated graph is the default source for questions about theories,
theorems, imports, dependencies, and change impact in this project.

## Quick start

From the repository root:

```sh
tools/isabelle_kg/build_graph.sh
tools/isabelle_kg/query_graph.py stats
tools/isabelle_kg/query_graph.py search CEV_clean_canonical_valid_iff_proves
tools/isabelle_kg/query_graph.py explain CEV_clean_canonical_valid_iff_proves
```

The first command builds and validates the graph. The remaining commands query
the generated `isabelle-kg/graph.json`.

## Requirements and resource use

- A working Isabelle installation available as `isabelle` on `PATH`. The
  current development uses Isabelle2025-2.
- Python 3, using only the standard library.
- Enough time to rebuild the maintained Isabelle sessions serially with
  theory exports enabled. Do not run another Isabelle build concurrently.
- Roughly 1 GB of free disk space for the current JSON and GraphML outputs.
  The exact size changes with the development.
- Several GB of available memory for queries. `query_graph.py` loads the JSON
  graph into memory before answering a query.

The graph is generated output and is intentionally excluded by `.gitignore`.
A fresh clone therefore contains the builder and query tools, not the graph
itself.

## Building

Run from the repository root:

```sh
tools/isabelle_kg/build_graph.sh
```

The builder:

1. rebuilds the maintained sessions serially with `export_theory=true`;
2. compiles the Scala extractor against the installed Isabelle libraries;
3. writes `isabelle-kg/graph.json` and `isabelle-kg/graph.graphml`; and
4. validates node identifiers, edge endpoints, source positions, semantic
   dependencies, and JSON/GraphML cardinality agreement.

If Isabelle's stored theory bodies are unavailable, the script automatically
performs one forced export build and retries extraction.

An alternative output directory may be supplied:

```sh
tools/isabelle_kg/build_graph.sh /path/to/output
tools/isabelle_kg/query_graph.py \
  --graph /path/to/output/graph.json stats
```

Rebuild the graph after changing a `.thy` file or the session declarations in
`ROOT`. The query tool does not silently rebuild a missing or stale graph.

## Querying

Run queries from the repository root, or pass `--graph` explicitly.

### Summary and lookup

```sh
tools/isabelle_kg/query_graph.py stats
tools/isabelle_kg/query_graph.py search H_proves
tools/isabelle_kg/query_graph.py search pp_e_Bacon_10_1
```

`search` matches qualified names, short names, identifiers, and encoded formal
statements. It reports source files and line numbers. Use `--limit N` to change
the default limit of 30 results.

### Explain one entity

```sh
tools/isabelle_kg/query_graph.py explain \
  CEV_clean_canonical_valid_iff_proves
```

`explain` prints the entity's source location, encoded formal statement, and
all immediate incoming and outgoing edges.

### Proof dependencies and reverse impact

```sh
tools/isabelle_kg/query_graph.py deps pp_e_Bacon_10_1 --depth 2
tools/isabelle_kg/query_graph.py used-by \
  CEV_clean_canonical_valid_iff_proves --depth 2
```

`deps` follows outgoing `DEPENDS_ON` edges: what the selected theorem uses.
`used-by` follows those edges in reverse: what depends on the selected theorem.
Both default to depth 1.

Use `--kind` to follow another edge kind, repeating the option when necessary:

```sh
tools/isabelle_kg/query_graph.py deps Bacon_Finite_CEV_Model \
  --kind IMPORTS --depth 2
```

### Paths

```sh
tools/isabelle_kg/query_graph.py path \
  Bacon_Finite_CEV_Model \
  Bacon_Deduction --directed
```

`path` searches the graph without regard to edge direction by default. Add
`--directed` when the path must respect edge orientation.

If a query is ambiguous, first run `search`, then copy the complete qualified
identifier from its output into `explain`, `deps`, `used-by`, or `path`.

## Graph contents

Node kinds include sessions, theories, types, constants, axioms, theorems,
classes, locales, and specification rules. Edge kinds include:

- `CONTAINS_THEORY`
- `IMPORTS`
- `DECLARES`
- `DEPENDS_ON`
- `USES_CONSTANT`
- `USES_TYPE`
- `USES_CLASS`
- `DEFINED_BY`
- `LOCALE_DEPENDS_ON`
- datatype and representation edges.

Formal dependencies outside the project are retained as external boundary
nodes. This supports impact analysis without copying the full Isabelle/HOL and
HOL-ZF library graphs into the project.

The JSON file is the input used by `query_graph.py`. The directed GraphML file
is available for external graph tools such as Gephi or yEd, although the full
project graph is large.

## Troubleshooting

- If `graph.json` is missing, run `tools/isabelle_kg/build_graph.sh` from the
  repository root.
- If `isabelle` is not found, add the Isabelle installation's `bin` directory
  to `PATH` and confirm that `isabelle version` succeeds.
- If a query reports several matches, use the fully qualified identifier
  printed by `search`.
- If the sources or `ROOT` are newer than the generated graph, rebuild before
  relying on dependency or source-location results.
- To see every available subcommand and option, run:

  ```sh
  tools/isabelle_kg/query_graph.py --help
  ```
