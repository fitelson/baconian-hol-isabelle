# Pure-diagonal search

This directory searches systematically for closed logical builders

\[
B:((\mathrm{Prop}\to\mathrm{Prop})\to\mathrm{Prop})
  \to(\mathrm{Prop}\to\mathrm{Prop})
\]

and forms the unary operator \(D=B(\mathrm{Pure})\). Since \(B\) is closed and
contains only logical vocabulary, logical purity makes \(B\) pure; PP makes
`Pure` pure; and application closure therefore makes \(D\) pure. Isabelle
checks this argument for every emitted candidate.

The first generated tranche has exactly one occurrence of the classifier and
no quantifier whose scope contains that occurrence. Named priority candidates
include the basic negative diagonal, the positive diagonal, and Goodman's T6
builder even when they lie outside the displayed generated bound.

## Reused infrastructure

The search imports the typed term language and exact-size enumerator from
`finite_core_search/terms.py`. It uses the same axiom profiles, reference
saturator, support minimizer, and contradiction replay. A contradiction is
never reported as certified until the existing Isabelle replay builds.

The generated `purity_audit/` session is separate: it checks that each builder
is well typed and constant-free and instantiates the verified generic theorem
`finite_core_pure_logical_builder_application`.

## Running a small tranche

From the repository root:

```sh
python3 -m pure_diagonal_search.run_search \
  --max-builder-size 7 \
  --classifier-occurrences 1 \
  --maximum-classifier-quantifier-depth 0 \
  --max-candidates 100 \
  --build-purity-audit
```

The aggregate purity audit is optional because
`finite_core_pure_logical_builder_application` already proves the uniform
result. Ordinary search runs check the candidates' types and vocabularies,
screen directly for contradiction, and invoke Isabelle only for a
contradiction replay. Use `--emit-purity-audit` or `--build-purity-audit` only
when a concrete per-candidate audit is wanted.

Run the unit tests with:

```sh
python3 -m unittest pure_diagonal_search.test_pure_diagonal_search -v
```

To admit classifier occurrences below quantifiers, use
`--maximum-classifier-quantifier-depth -1`. To admit any positive number of
classifier occurrences, use `--classifier-occurrences 0`.
Use equal `--min-builder-size` and `--max-builder-size` bounds for one exact
raw-syntax size.

Large external screens can use `--workers N`. This parallelizes only the
Python reference saturator. Candidate generation remains single-source, and
every Isabelle replay is still run serially.

## Interpretation of a negative run

`bounded_no_refutation` says only that the displayed candidates did not yield
falsity under the reference saturator's finite witness set and proof rules. It
is not a consistency result. The present reference engine does not yet perform
existential elimination on the unique-fundamentality axiom, so a later tranche
must add a replayable fundamental-witness context before the search can test
all closure patterns involving an existentially given fundamental
proposition.
