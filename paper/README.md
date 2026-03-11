# paper

LaTeX sources for the arXiv preprint on executable Hermite normal form in Lean 4.

Build steps:

```sh
latexmk -pdf main.tex
```

Quick visual check:

```sh
pdftoppm -png main.pdf preview
```

Figure workflow:

- The paper now uses TikZ figure sources under `figures/`.
- `latexmk -pdf main.tex` compiles those figures directly into `main.pdf`.
- `scripts/generate_figures.py` is retained only as a legacy asset and is no longer
  part of the build path.

Scope notes:

- The manuscript still centers on the completed HNF layer.
- `NormalForms.Matrix.Smith.Basic` is no longer just a frozen placeholder API:
  it already contains a real public Smith specification, invariant-factor
  reader, certificate/result packaging helpers, internal recursive
  scaffolding, and a verified same-size lead-reduction foundation, even though
  the executable kernel and uniqueness layer are still future work.
- `NormalForms.Bridge.MathlibPID.Basic` remains future work rather than a
  completed comparison-theorem layer.
- If the manuscript scope expands before submission, the Smith discussion should
  describe the current public packaging boundary and same-size lead-reduction
  foundation separately from the still-missing nondivisible pivot-improvement
  and outer recursive kernel layers, since the repository deliberately avoids
  aggressive public `simp` lemmas through `Fintype.equivFin` for elaboration
  stability.
