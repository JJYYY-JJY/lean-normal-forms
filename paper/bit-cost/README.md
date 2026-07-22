# Binary bit-cost reference-model paper

Build the independent research version 0.1.0 paper with:

```sh
latexmk -pdf -interaction=nonstopmode main.tex
```

The paper separates semantic correctness, abstract operation counts,
coefficient-width bounds, and concrete bit complexity. It covers the binary
sign-magnitude representation, mirrored primitive counters, signed Euclidean
long division, the costed extended-gcd recurrence, the trust boundary, and
the reproducible 13-case native profile.
