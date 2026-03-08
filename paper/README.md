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

- The manuscript covers only the completed HNF layer.
- `NormalForms.Matrix.Smith.Basic` and `NormalForms.Bridge.MathlibPID.Basic` are described only as future work and frozen API boundaries.
