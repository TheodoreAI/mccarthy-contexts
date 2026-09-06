# Paper source

`paper.tex` is the LaTeX source of *Harmless and Pointless: Consistency,
rigidity, and the indeterminacy of context transfer in McCarthy's formalization
of context*, which describes the results in this repository.

Build with any TeX Live installation:

```bash
pdflatex paper.tex && pdflatex paper.tex   # twice, for cross-references
```

It uses only standard packages (`amsmath`, `amssymb`, `amsthm`, `geometry`,
`microtype`, `booktabs`, `enumitem`, `hyperref`) and needs no bibliography
processor — references are a `thebibliography` environment.

Each theorem in the paper carries the Lean identifier of the corresponding
result, so a claim in the text can be traced to the module that proves it.
