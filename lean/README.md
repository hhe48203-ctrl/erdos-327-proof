# Lean formalization of Erdős Problem 327

This directory contains a complete Lean 4 / Mathlib formalization of both
asymptotic conclusions of Erdős Problem 327.

The public theorems are:

```lean
Erdos327.Analytic.erdos327Conclusion_unconditional :
  Erdos327.Erdos327Conclusion

Erdos327.Analytic.erdos327SecondConclusion_unconditional :
  Erdos327.Erdos327SecondConclusion

Erdos327.Analytic.erdos327FullConclusion_unconditional :
  Erdos327.Erdos327FullConclusion
```

Here `Erdos327Conclusion` states that, for some `ε > 0` and all sufficiently
large `N`, there is `A ⊆ {1, ..., N}` with

```text
a + b ∤ a * b  for distinct a, b ∈ A
|A| ≥ (1/2 + ε) N.
```

`Erdos327SecondConclusion` is the positive-density analogue for
`a + b ∤ 2 * a * b`, first proved by Will Sawin.

## Trust boundary

The project has no `sorry`, `admit`, project-local `axiom`, `opaque` theorem
interface, or `unsafe` declaration. The three public theorems have the
following axiom report:

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean/Mathlib's standard logical axioms. No analytic estimate is
assumed at the final interface: the centered anatomy bounds, Mertens-type
estimates, specialized three-form sieve, dyadic summations, residual
boundaries, and final parameter selection are proved in this project.

The toolchain and dependencies are pinned by `lean-toolchain` and
`lake-manifest.json`.

## Reproduction

```bash
cd lean
lake build Erdos327
```

The full build currently checks 8,757 jobs under Lean `4.33.0-rc1`.

To reproduce the public axiom audit:

```bash
printf '%s\n' \
  'import Erdos327' \
  '#print axioms Erdos327.Analytic.erdos327FullConclusion_unconditional' \
  '#print axioms Erdos327.Analytic.erdos327Conclusion_unconditional' \
  '#print axioms Erdos327.Analytic.erdos327SecondConclusion_unconditional' \
  | lake env lean /dev/stdin
```

See `FORMALIZATION_STATUS.md` for the proof-layer inventory.
