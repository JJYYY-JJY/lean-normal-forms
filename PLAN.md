# Maintenance plan

## Current state

Version 1.2.2 is complete on Lean and mathlib 4.32.0. The repository has:

- a frozen `NormalForms` core facade and exact core constructor freeze;
- verified HNF/SNF execution over `Int` and `Polynomial Rat`;
- explicit transformation inverses and certificate kernel re-import;
- separate rational-canonical and homology application facades;
- separate bit-cost, Kannan--Bachem, modular-HNF, and LLL research facades;
- independent axiom policies for every trust tier;
- deterministic native cases and committed benchmark baselines;
- optional FLINT CLI, FFI, relinking, and differential verification.

The default build, test driver, lint driver, code verifier, and benchmark
runner are the maintained software entry points. There are no open
correctness or verification blockers in the current scope.

## Stable boundaries

Maintenance changes must preserve:

- theorem statements, definition semantics, normal-form conventions, matrix
  orientation, and indexing semantics;
- `NormalForms` facade declarations and its public import closure;
- the `normalforms.cert/v1` schema and explicit inverse fields;
- `decide_cbv` on strict certificate reconstruction paths;
- core, certificate, application, and research API snapshots;
- separate declaration roots and axiom allowlists for every audit tier;
- historical benchmark baselines and their deterministic payloads;
- the separation between the pure core and optional FLINT linkage.

Changes to any boundary require a versioned API or schema decision. Tooling
must not infer or rewrite a new snapshot from the current environment.

## Non-goals

Routine maintenance does not:

- add algorithms, theorem families, application domains, or research claims;
- upgrade Lean, mathlib, HexLLLMathlib, FLINT, GMP, or MPFR;
- replace explicit inverses with determinant, choice, or `Matrix.inv` paths;
- add native or compiler trust to audited declarations;
- move application or research modules into the core facade;
- make FLINT part of default build or test;
- introduce another task runner or generated-output hierarchy;
- combine publication workflows with software verification.

## Follow-up work

Three maintenance triggers remain:

1. Test dependency compatibility on a separate branch before any deliberate
   toolchain update.
2. Add a new benchmark baseline after an intentional implementation or
   fixed-environment change; retain the historical files.
3. Revisit public imports as part of a versioned facade change. Private
   import narrowing may proceed when `lake shake`, build, tests, API freezes,
   and axiom audits all agree.
