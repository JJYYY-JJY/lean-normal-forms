# Rational canonical paper

Title:

> Certified Executable Rational Canonical Form in Lean 4 via Strong
> Polynomial Smith Normal Form

Build:

```sh
latexmk -pdf main.tex
```

Version 1.1.0 is an independent application paper. It uses the frozen 1.0
HNF/SNF core but does not alter the core manuscript or facade. The paper
covers executable `XI - A`, the standard `Matrix.charmatrix` bridge, strong
polynomial Smith data, the `Module.AEval'` cyclic decomposition,
characteristic and minimal polynomials, explicit companion-block similarity,
basis independence, the native Rat benchmark, and the application trust
boundary.
