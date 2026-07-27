# Isabelle-native knowledge graph

This tool extracts the project graph from Isabelle's elaborated session
database.  It does not parse `.thy` files heuristically.  Isabelle supplies
the theories, entities, source positions, formal statements, constant/type
occurrences, locale dependencies, and direct theorem dependencies.

This is the default knowledge graph for the Higher Order Metaphysics project.
Project agents should query it before broad text search. Graphify is an
explicit fallback, not the default.

## Build

From the project root:

```text
tools/isabelle_kg/build_graph.sh
```

The command rebuilds the active sessions with `export_theory=true`, compiles
the small Scala extractor against the installed Isabelle libraries, and
writes:

- `isabelle-kg/graph.json` — the queryable exact graph;
- `isabelle-kg/graph.graphml` — a directed GraphML export for Gephi or yEd.

The graph includes the foundational, PP, frontier, finite-model, HOL-ZF, and
independent `Goodman_Fresh_Attack` sessions.

Generated output and compiled classes are intentionally git-ignored.  The
graph is reproducible from the checked theories.  The build validates unique
node identifiers, all edge endpoints, source positions for every project
entity, the presence of semantic dependency edges, and JSON/GraphML
cardinality agreement.

## Schema

Node kinds include sessions, theories, types, constants, axioms, theorems,
classes, locales, and specification rules.  Edges include:

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
nodes.  This makes the graph useful for impact analysis without copying the
entire Isabelle/HOL and HOL-ZF libraries into the project graph.

## Query

```text
tools/isabelle_kg/query_graph.py stats
tools/isabelle_kg/query_graph.py search range_complete
tools/isabelle_kg/query_graph.py explain pp_t_term_basis_range_complete_iff_fixed_point
tools/isabelle_kg/query_graph.py deps pp_t_term_basis_range_complete_iff_fixed_point --depth 2
tools/isabelle_kg/query_graph.py used-by pp_t_root_eqv_iff_eq --depth 2
tools/isabelle_kg/query_graph.py path \
  pp_t_term_basis_range_complete_iff_fixed_point \
  Bacon_PP_ZF_Tree_Seeded_Stock.pp_t_stock_basis.pp_t_basis_recombination_PP_gvalid_iff_root
```

Queries match exact qualified names first and otherwise search names,
identifiers, and formal statement encodings.  `deps` and `used-by` default to
kernel-recorded direct theorem dependencies; `--kind` can select other edge
types.
