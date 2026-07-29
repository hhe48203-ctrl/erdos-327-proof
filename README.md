# A positive-density improvement in Erdős Problem 327

This repository contains Donald Della Pietra's proof claim for the first
question in [Erdős Problem 327](https://www.erdosproblems.com/327), together
with reproducibility materials and a complete Lean 4 formalization of both
conclusions of the problem.

The new result states that there is an absolute `ε > 0` such that, for every
sufficiently large `N`, some `A ⊆ {1, ..., N}` satisfies

```text
a + b ∤ a * b  for all distinct a, b ∈ A,
|A| ≥ (1/2 + ε) N.
```

The repository also independently formalizes Will Sawin's positive-density
result for the stronger condition `a + b ∤ 2 * a * b`.

This is an unrefereed preprint and proof claim.

## Contents

- [Human-readable manuscript](erdos-327-positive-density-della-pietra.pdf)
- [`paper/`](paper/) — LaTeX source and numerical supplement
- [`lean/`](lean/) — complete Lean 4 / Mathlib formalization
- [`paper/supplement/verify_certificate.py`](paper/supplement/verify_certificate.py)
  — standalone numerical certificate verifier
- [`paper/supplement/certificate-output.txt`](paper/supplement/certificate-output.txt)
  — recorded verifier output

The combined public Lean theorem is:

```lean
Erdos327.Analytic.erdos327FullConclusion_unconditional :
  Erdos327.Erdos327FullConclusion
```

The two conclusions are also exported separately as
`erdos327Conclusion_unconditional` and
`erdos327SecondConclusion_unconditional`.

The formal development has no project-local axioms, `sorry`, `admit`,
`opaque` theorem interfaces, or `unsafe` declarations. `#print axioms` for
all three public theorems reports only `propext`, `Classical.choice`, and
`Quot.sound`. Compiler and dependency revisions are pinned in
`lean/lean-toolchain` and `lean/lake-manifest.json`.

## Reproduction

Build the manuscript:

```bash
cd paper
make pdf
```

Run the standalone numerical verifier:

```bash
python3 paper/supplement/verify_certificate.py
```

Build the Lean formalization:

```bash
cd lean
lake build Erdos327
```

## Prior-work status

A dated search on 2026-07-29 found the first question still listed as open
and located no prior public proof claim beating density `1/2`. A separate
search found no prior public Lean formalization of Problem 327 or Sawin's
result. These are qualified search reports, not categorical priority claims.

## AI-use disclosure

AI systems provided substantial assistance with proof auditing, reference
search, calculations, formalization, and exposition. Donald Della Pietra is
responsible for the mathematical claims and their verification.
