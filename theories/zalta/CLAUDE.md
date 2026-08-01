# AOT project instructions

Read the repository-root `AGENTS.md`, `README.md`, and `STATUS.md` first, then
read this directory's `README.md` and `ROOT`.

This directory formalizes Edward Zalta's Abstract Object Theory. It is an
independent Isabelle theory family over `HOL-Cardinals`; it has no dependency
on the Bacon--Dorr--Goodman sessions. Do not introduce imports between those
families without an explicit mathematical bridge and project decision.

Build the complete AOT session serially from the repository root:

```sh
isabelle build -j 1 -D theories/zalta AOT
```

The maintained version is Isabelle2025-2. The custom `AOT_*` commands embed
the AOT object logic in Isabelle/HOL. Keep object-language axioms distinct
from Isabelle metatheorems, and do not describe a theorem as unconditional
when it depends on an AOT axiom or a local extension such as `hype:3`.

Do not add `sorry`, `oops`, `admit`, or `quick_and_dirty`. Generated HTML,
the separate Lean port, local experiments, and the local copy of *Principia
Logico-Metaphysica* are excluded by this directory's `.gitignore`.
