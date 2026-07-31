We need a hard-nosed post-repair fidelity audit of the
Higher_Order_Metaphysics Isabelle project. Claude must use Claude Opus 5 at
high effort; Codex uses its configured high-effort model. Do not delegate to
other models or start a recursive debate.

Question: After the repairs prompted by the preceding audit, is the maintained
Isabelle development, together with the Goodman report and verification
matrix, now correct, complete at its stated scope, and source-faithful to
Bacon, Dorr, and Goodman? In particular, are the four promised exact-model
tasks genuinely complete, and is every PER-based construction confined to an
explicitly secondary role?

The four exact-model tasks are:

1. Bacon's Theorem 10.1 over the exact recursively restricted carriers, at
   precisely the scope whose construction the appendix develops.
2. Exact H, Classicist, CE, and CEV soundness, including Bacon--Dorr's
   individual Existence instance and vector Equivalence.
3. Bacon's enumeration and model-gluing construction after Theorem 10.1.
4. The resulting exact semantic frame-theory representation theorem, with no
   claim of proof-theoretic completeness of H.

The previous audit found two points requiring repair:

- the formal derivability relation represented H-minus rather than full H
  because individual Existence was absent;
- the report described Theorem 10.1 too broadly and gave the wrong reason for
  its restriction.

The current code adds exactly the Bacon--Dorr individual Existence instance,
propagates it through syntactic transformations and all relevant soundness
proofs, narrows Theorem 10.1 to the proposition-generated construction actually
developed in Bacon's appendix, and explicitly distinguishes semantic
frame-theory representation from proof-theoretic completeness. Verify these
repairs from theorem statements and proofs rather than trusting this summary.

Materials and required checks:

- Goodman's original notes: `../PP_project_notes copy.pdf`, with extracted
  text in `../tmp/pdfs/PP_project_notes.txt`.
- Bacon and Dorr: `../Bacon_Dorr_Classicism.pdf`, with extracted text in
  `../tmp/pdfs/bacon_dorr_classicism.txt`.
- Bacon's appendix/model paper: `../tmp/pdfs/Bacon_Logical_Combinatorialism.pdf`,
  with extracted text in
  `../tmp/pdfs/Bacon_Logical_Combinatorialism_full_layout.txt`.
- Inspect the actual Isabelle sources in `theories/base/`,
  `theories/classicism/`, `theories/goodman/core/`,
  `theories/goodman/notes/`,
  `theories/goodman/models/hol_zf/canonical/`, and
  `theories/goodman/models/hol_zf/extensions/`.
- Treat `theories/goodman/models/hol_zf/secondary/` only as a quarantined
  comparison area. Do not count any theorem proved only there as a theorem
  about Bacon's exact appendix model.
- Inspect `ROOT`, `tools/check_exact_bacon_boundary.py`,
  `check_isabelle.sh`, and `reports/audit_goodman_complete/`.
- Audit `reports/GOODMAN_VERIFICATION_AND_PROGRESS_REPORT_2026-07-27.tex`,
  its compiled PDF, and
  `reports/GOODMAN_COMPLETE_VERIFICATION_MATRIX_2026-07-27.md`.
- Confirm that the dedicated audit really contains 158 targets and that its
  exact-model targets are the canonical theorem objects.
- Check the exact L2 chain on Bacon's finite-natural-word action, including
  the all-immediate-successor variation operator and the claim that it belongs
  to the exact closed-logical stock. Confirm that no obsolete two-child result
  or theorem about arbitrary enlarged pure stocks is presented as exact.
- Check the complete transitive import closure of `canonical/` and
  `extensions/` for PER machinery, terminology, or hidden import paths. PER
  code may remain in `secondary/` and may be mentioned only to identify its
  secondary, historical status.
- Check theorem statements and proof dependencies, not merely names or
  successful builds. Distinguish derivability, conditional semantic theorems,
  exact-model instantiations, and the semantic representation theorem.
- Look aggressively for vacuity, strengthened assumptions, weakened
  conclusions, equality/type mistakes, action-orientation errors, hidden
  axioms, unjustified source attributions, and overbroad completeness claims.
- Isabelle builds must be serial. Do not edit project files during the audit,
  except for the required progress file.

For every material finding, give severity, exact file and theorem or report
passage, the source passage checked, the mathematical reason, and the smallest
correct repair. End with separate verdicts for exact Bacon model fidelity;
Theorem 10.1; H/Classicist/CE/CEV and vector-Equivalence soundness;
enumeration/gluing and completeness; exact Goodman extensions and L2; report
and matrix; PER quarantine; and whether the four-task goal is complete.

Claude checkpoint protocol: create or reset
`reports/CLAUDE_OPUS5_POSTFIX_FIDELITY_AUDIT_PROGRESS_2026-07-31.md` at the
start. Append a cumulative checkpoint at least every five minutes, recording
elapsed time, tentative verdict, genuinely new results, current obstruction,
next bounded step, and token/cost figures when available. Each invocation is a
bounded tranche and must return its cumulative micro-report by five minutes.
Two consecutive missed checkpoints or two consecutive checkpoints with no
substantive progress require stopping with the durable partial report intact.

Claude and Codex must challenge each other directly and concede only when the
argument is correct. Each returned report must be a compressed report of at
most 40,000 output tokens preserving decisive arguments, proof steps,
counterexamples, qualifications, and verdict. If more detail is needed, write
it to a project file and return a compact summary with the path.
