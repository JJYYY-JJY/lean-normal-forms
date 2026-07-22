# Core paper

Working title:

> Certified Executable Hermite and Smith Normal Forms in Lean 4:
> Canonicality, Explicit Inverses, and a Mathlib PID Bridge

Build:

```sh
latexmk -pdf main.tex
```

Quick visual check:

```sh
pdftoppm -png main.pdf preview
```

Version 1.0.0 is the unified core manuscript. It covers the explicit-inverse,
indexing-semantics,
constructive-execution, strict external-certificate, intrinsic Smith, and
presentation layers:
strong `Fin` results, caller-controlled enumeration, fixed-index HNF
uniqueness, canonical Smith invariance under reindexing, direct `Int` and
`Polynomial Rat` execution, pivot-measure termination, pure certificate
checking, chunked kernel import, and a pinned untrusted FLINT generator.
The process and FFI adapters now share one C implementation; fixed-seed
differential regressions and a seven-stage raw benchmark profile keep run
reports distinct from kernel theorems. Determinantal ideals recover Smith rank
and associate factors, the PID bridge compares canonical data at three levels,
and finite-free presentations fix columns as relations and derive cokernel
decompositions.

Exact type tests freeze terminology and public interfaces; the evaluation
section records the benchmark table, trust boundary, and reproducibility
profile.
The completed rational-canonical application has its independent v1.1 paper
under [`rational-canonical`](rational-canonical/README.md), and the completed
homology line has its v1.2.2 paper under
[`homology`](homology/README.md). The binary primitive cost model has an
independent research 0.1.0 paper under
[`bit-cost`](bit-cost/README.md). The completed nonsingular-square
Kannan--Bachem research line has its independent 0.1.0 manuscript under
[`kannan-bachem`](kannan-bachem/README.md). The completed modular-HNF research
line has its independent 0.1.0 manuscript under
[`modular-hnf`](modular-hnf/README.md). The completed exact-integer LLL profile
has its independent 0.1.0 manuscript under [`lll`](lll/README.md).
