# Isabelle-native knowledge graphs

These tools extract exact graphs from Isabelle's elaborated session database.
They do not parse `.thy` files heuristically. Isabelle supplies the theories,
entities, source positions, formal statements, constant and type occurrences,
locale dependencies, and direct theorem dependencies.

The repository has two mathematically independent graphs:

- `isabelle-kg/bacon/graph.json` contains the base theory \(H\), Classicism,
  CEV, and Goodman's extensions;
- `isabelle-kg/zalta/graph.json` contains only Zalta's `AOT` session.

The builders validate this boundary and fail if one family leaks into the
other graph. No cross-family edges are inferred or stored.

## Quick start

From the repository root, build both graphs serially:

```sh
tools/isabelle_kg/build_all_graphs.sh
```

Or build only one family:

```sh
tools/isabelle_kg/build_bacon_graph.sh
tools/isabelle_kg/build_zalta_graph.sh
```

Query one family at a time:

```sh
tools/isabelle_kg/query_graph.py --family bacon stats
tools/isabelle_kg/query_graph.py --family bacon search pp_e_Bacon_10_1
tools/isabelle_kg/query_graph.py --family zalta stats
tools/isabelle_kg/query_graph.py --family zalta search AOT_PLM
```

The default family is `bacon` for backward compatibility, but agents should
pass `--family` explicitly. An explicit `--graph PATH` overrides `--family`.

## Requirements and resource use

- Isabelle2025-2 available as `isabelle` on `PATH`;
- Python 3, using only the standard library;
- enough time to rebuild the selected sessions serially with theory exports;
- roughly 1 GB of free disk space for the larger Bacon-family graph, plus
  space for the smaller Zalta graph; and
- several GB of memory for large Bacon-family queries.

The generated `isabelle-kg/` directory is intentionally ignored by Git. A
fresh clone contains the builders and query tools, not the graph files.

## Building

Each family builder:

1. builds only that family's sessions with `export_theory=true` and `-j 1`;
2. compiles the Scala extractor against the installed Isabelle libraries;
3. writes `graph.json` and `graph.graphml` beneath that family's output
   directory; and
4. validates identifiers, endpoints, source positions, semantic dependencies,
   JSON/GraphML cardinality agreement, and the cross-family boundary.

If stored theory bodies are unavailable, the builder performs one forced
export build and retries. Do not run either builder concurrently with another
Isabelle build or graph extraction.

An alternative output directory may be supplied to an individual builder:

```sh
tools/isabelle_kg/build_bacon_graph.sh /path/to/bacon-output
tools/isabelle_kg/build_zalta_graph.sh /path/to/zalta-output
tools/isabelle_kg/query_graph.py \
  --graph /path/to/zalta-output/graph.json stats
```

Rebuild only the affected family after changing one of its `.thy` files or
session declarations. The query tool never rebuilds a missing or stale graph.

## Querying

### Summary and lookup

```sh
tools/isabelle_kg/query_graph.py --family bacon search H_proves
tools/isabelle_kg/query_graph.py --family zalta search AOT_TruthmakerSemantics
```

`search` matches qualified names, short names, identifiers, and encoded formal
statements. It reports source files and line numbers. Use `--limit N` to change
the default limit of 30 results.

### Explain one entity

```sh
tools/isabelle_kg/query_graph.py --family bacon explain \
  CEV_clean_canonical_valid_iff_proves
```

`explain` prints the entity's source location, encoded statement, and immediate
incoming and outgoing edges.

### Proof dependencies and reverse impact

```sh
tools/isabelle_kg/query_graph.py --family bacon \
  deps pp_e_Bacon_10_1 --depth 2
tools/isabelle_kg/query_graph.py --family zalta \
  used-by AOT_PLM --depth 2 --kind IMPORTS
```

`deps` follows outgoing `DEPENDS_ON` edges; `used-by` follows them in reverse.
Both default to depth 1. Use repeatable `--kind` options to follow other edge
kinds.

### Paths

```sh
tools/isabelle_kg/query_graph.py --family bacon path \
  Bacon_Finite_CEV_Model Bacon_Deduction --directed
```

`path` ignores edge direction by default. Add `--directed` when orientation
matters. If a query is ambiguous, run `search` and use the resulting fully
qualified identifier.

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

Formal dependencies outside the selected family remain as external boundary
nodes. Each family has its own directed GraphML file for tools such as Gephi
or yEd.

## Troubleshooting

- If one graph is missing, run its family builder; use
  `build_all_graphs.sh` only when both need refreshing.
- If `isabelle` is not found, add Isabelle's `bin` directory to `PATH` and
  confirm that `isabelle version` succeeds.
- If a query reports several matches, use the qualified identifier printed by
  `search`.
- If a family's sources or `ROOT` are newer than its graph, rebuild that
  family before relying on the graph.
- Run `tools/isabelle_kg/query_graph.py --help` for every option.
