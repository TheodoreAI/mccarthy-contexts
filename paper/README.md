# Paper sources

Two papers describe the results in this repository.

`paper.tex` — *Harmless and Pointless: Consistency, rigidity, and the
indeterminacy of context transfer in McCarthy's formalization of context.* The
consistency of the tower, the cost of every repair to it, and the
information-theoretic measurement of context transfer.

`uniformity.tex` — *Uniformity and Transcendence: a trichotomy for lifting
schemas in the logic of context.* Why a lifting schema that treats propositions
alike cannot deliver novelty: the monotone dichotomy, the trichotomy, rigidity,
and the audit property the trichotomy's design principle amounts to.

Build either with any TeX Live installation:

```bash
pdflatex paper.tex && pdflatex paper.tex   # twice, for cross-references
```

Both use only standard packages (`amsmath`, `amssymb`, `amsthm`, `geometry`,
`microtype`, and for `paper.tex` also `booktabs`, `enumitem`, `hyperref`) and
need no bibliography processor — references are a `thebibliography`
environment. `tectonic -X compile <file>.tex` also works and needs no system
TeX installation.

Each theorem in `paper.tex` carries the Lean identifier of the corresponding
result, so a claim in the text can be traced to the module that proves it.
`uniformity.tex` names its modules in the subsection on the machine-checked
development rather than per theorem.

## Citing `uniformity.tex`

Its numbered results share a single counter, so **inserting a remark renumbers
everything after it**. Four Prove2Me nodes cite theorem numbers from this file
in their `source` fields, and those citations went stale once when a section was
added. They now name the result as well as its number — `Theorem 15 (Monotone
dichotomy), Section 3` — so a later renumbering degrades a citation rather than
silently invalidating it.

Keep that convention, and re-check the published `source` fields after any edit
that adds or removes a numbered environment:

```bash
tectonic -X compile --keep-intermediates uniformity.tex
grep -E 'newlabel\{(thm:mono|thm:trichotomy|thm:rigidity|def:aut)\}' uniformity.aux
```
