# Exact integer LLL research paper

Build research version 0.1.0 with:

```sh
latexmk -pdf -interaction=nonstopmode main.tex
```

The manuscript covers the fixed row-vector convention, exact reducedness
predicate, terminating verified dense backend, explicit inverse trace, total
rank-deficient wrapper, transpose-only column adapter, four-layer profiled
evidence, benchmark, and trust boundary. It states explicitly that the
profile-dependent reference budget is not an input-only polynomial LLL
complexity theorem and excludes the HNF rank-decomposition cost.
