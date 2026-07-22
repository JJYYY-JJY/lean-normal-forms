# `normalforms.cert/v1`

This document fixes the version 1 external-certificate format. Producers may
change provenance metadata, but the mathematical payload and checker semantics
below remain stable throughout the 1.x release line.

## Encoding

A certificate is one JSON object with these common fields:

```json
{
  "schema": "normalforms.cert/v1",
  "kind": "hnf",
  "input": {
    "rows": 2,
    "cols": 3,
    "entries": ["2", "4", "6", "0", "8", "10"]
  }
}
```

Every matrix has nonnegative JSON-number dimensions and a row-major `entries`
array. An entry is a JSON string in the grammar:

```text
0 | -?[1-9][0-9]*
```

Leading zeros, a leading plus sign, `-0`, whitespace, exponent notation, and
JSON numeric values are rejected.

An HNF payload contains:

```text
input, U, UInverse, H
```

An SNF payload contains:

```text
input, U, UInverse, S, V, VInverse
```

The optional `metadata` object may contain string-valued `generator`,
`flintVersion`, `build`, and `hash` fields. Metadata never contributes to a
theorem.

## Caller binding

The checker receives the expected matrix separately:

```lean
checkHNF expected raw
checkSNF expected raw
```

It compares the certificate's `input` with `expected`. A mathematically valid
certificate for another matrix is rejected.

The checker distinguishes:

- matrix dimensions and entry counts;
- input mismatch;
- transformation equation failure;
- left- and right-inverse failure for each transformation matrix;
- normal-form failure.

`CheckedHNFData` and `CheckedSNFData` are typed values, not proof objects.
Only `checkHNF_sound` and `checkSNF_sound`, applied to an equality proving
checker success, construct strong results with explicit inverse certificates.

## Kernel import

`normalforms-check emit-lean` binds a certificate to a named matrix imported
from a caller-selected module. Generated modules split dimensions, input,
transformation, inverse, and normal-form checks into separate `decide_cbv`
obligations. The final result is obtained only through the corresponding
soundness theorem.

Strict imports do not use `native_decide`, `decide +native`,
`Lean.ofReduceBool`, or `Lean.ofReduceNat`. FLINT process and FFI adapters are
untrusted producers of the same raw schema; their output must pass the pure
checker, and a generated module must still compile before it yields a theorem.

## Compatibility

Version 1 readers reject an unknown `schema` value. Any future incompatible
payload change uses a new schema identifier. Compatible producer changes are
limited to metadata values and JSON object key order; matrix dimensions,
row-major order, integer grammar, mathematical fields, and caller-binding
semantics do not change within `normalforms.cert/v1`.
