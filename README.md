# Erdős Problem 327: a positive-density improvement, and the k ≥ 2 variants

This repository contains two of Donald Della Pietra's proof claims about
[Erdős Problem 327](https://www.erdosproblems.com/327), together with
reproducibility materials and a Lean 4 formalization of the main result.

For `k ≥ 1` call a set `A` **k-admissible** if

```text
a + b ∤ k * a * b   for all distinct a, b ∈ A,
```

and let `f_k(N)` be the largest size of a k-admissible subset of `{1, ..., N}`.
Problem 327 asks about `k = 1` (its first question) and `k = 2` (its second).
In unit-fraction language, `a + b | ab` says `1/a + 1/b` is a unit fraction,
and `a + b | 2ab` says the average of `1/a` and `1/b` is one.

Both manuscripts are unrefereed preprints and proof claims.

## 1. Main manuscript — the first question of Problem 327

[`paper/`](paper/) · [PDF](erdos-327-positive-density-della-pietra.pdf)

There is an absolute `ε > 0` such that, for every sufficiently large `N`, some
`A ⊆ {1, ..., N}` satisfies

```text
a + b ∤ a * b  for all distinct a, b ∈ A,
|A| ≥ (1/2 + ε) N.
```

This answers the first question of Problem 327 positively: a 1-admissible set
can be denser than the odd numbers. The construction follows Sawin's
orientation by the total number of prime factors, and adds a centering of the
prime-factor anatomy at a fixed roughness cutoff with distinct centered
budgets at both ends of every odd–even conflict. The manuscript also
independently reproves Sawin's positive-density result for `a + b ∤ 2ab`.

**Corrections.** Version 1 stated the dyadic block lower bound `X ≫ L`
without adequate justification; this is now proved. A later revision
unnecessarily weakened an exact anatomy identity to an inequality. Since
`x = 2u + w > w`, the identity is exact and has been restored. Neither
correction changes any theorem, exponent, or certified margin — see the
"Corrections relative to released versions" section of the manuscript. The
Lean development is unaffected.

## 2. Companion manuscript — the multipliers k ≥ 2

[`variants/`](variants/) · [PDF](variants/erdos-327-variants-della-pietra.pdf)

- **Theorem 1.1 (periodic benchmark).** A union of residue classes to a
  common modulus is k-admissible **iff** every one of its classes consists of
  odd numbers and `k` is odd. So the benchmark density is `1/2` for odd `k`,
  attained by the odd numbers, and `0` for even `k` — for even `k` there is no
  nonempty periodic k-admissible set at all.
- **Theorem 1.2 (odd multipliers).** For every odd `k` there is an absolute
  `ε_k > 0` with `f_k(N) ≥ (1/2 + ε_k) N` for large `N`.
- **Theorem 1.3 (all multipliers).** For every `k` there is an absolute
  `c_k > 0` with `f_k(N) ≥ c_k N`. This is trivial for odd `k`; its content is
  for **even** `k`, and for even `k ≥ 4` it is, to our knowledge, the first
  lower bound of any kind.

The companion does **not** prove `f_2(N) ≥ (1/2 + o(1))N`, the question raised
in the Problem 327 discussion thread, nor any even-`k` bound beyond positive
density; Section 7 of the companion isolates the obstruction.

**Dependence and gaps.** Theorem 1.2 depends on the main manuscript above: if
its Theorem 1.1 is wrong, Theorem 1.2 is wrong for every odd `k`. Theorem 1.3
depends only on the source estimate, and Theorem 1.1 is independent of both.
Section 8 of the companion is a ten-item list of everything imported, altered,
or unverified, including the ineffectivity of `ε_k` and `c_k`, the two quoted
mean-value theorems, the dilation error found by audit, and the fact that the
companion has **no** Lean formalization.

## 3. Formalization

[`lean/`](lean/) — a complete Lean 4 / Mathlib development for the **main**
manuscript only. The combined public theorem is

```lean
Erdos327.Analytic.erdos327FullConclusion_unconditional :
  Erdos327.Erdos327FullConclusion
```

with `erdos327Conclusion_unconditional` and
`erdos327SecondConclusion_unconditional` exported separately. The development
has no project-local axioms, `sorry`, `admit`, `opaque` theorem interfaces, or
`unsafe` declarations; `#print axioms` for all three public theorems reports
only `propext`, `Classical.choice`, and `Quot.sound`. Compiler and dependency
revisions are pinned in `lean/lean-toolchain` and `lean/lake-manifest.json`.

There is **no** Lean development for the companion manuscript. Formalization
of the companion is planned and has not been done.

## Reproduction

All commands are run from the repository root.

```bash
# main manuscript
cd paper && make pdf && cd ..
python3 paper/supplement/verify_certificate.py

# companion manuscript
cd variants/paper && make pdf && cd ../..
python3 variants/paper/supplement/verify_certificate.py

# Lean formalization (main manuscript only)
cd lean && lake build Erdos327
```

Both verifiers are standard-library Python using exact integer and rational
arithmetic, with no load-bearing floating-point comparison and no
dependencies; each runs in a few seconds. Recorded transcripts are in
`paper/supplement/certificate-output.txt` and
`variants/paper/supplement/certificate-output.txt`.

The verifiers certify arithmetic, local densities and the numerical parameter
windows. They are **not** evidence for the two analytic mean-value inputs
(Tenenbaum, and de la Bretèche–Tenenbaum), which enter only through the cited
theorems.

## Prior-work status

A dated search on **2026-07-29** found the first question of Problem 327 still
listed as open, with no prior public proof claim beating density `1/2`, and no
prior public Lean formalization of Problem 327 or of Sawin's result. The same
search found Sawin's paper (arXiv:2607.15419) treating `k = 2` only,
leon2k2k2k's upper bounds `f_1 ≤ 0.7769N`, `f_2 ≤ 0.7630N`, `f_3 ≤ 0.6089N`,
and **no lower bound for `f_k` with `k ≥ 3`** other than the odd numbers for
odd `k` — in particular none at all for even `k ≥ 4`. Full details are in the
companion's [README](variants/README.md) and Section 9. These are qualified,
dated search reports, not categorical priority claims.

## AI-use disclosure

This disclosure covers both manuscripts, the verifiers, and the
formalization.

AI systems provided substantial assistance with proof auditing, reference
search, symbolic and numerical exploration, independent reconstruction of
intermediate estimates, formalization, and exposition. AI audits found the
missing dyadic justification in the main manuscript, identified and corrected
a later unnecessary weakening of the exact anatomy identity, and found and
forced the repair of a fatal error in a draft of the companion. The
mathematical strategy, parameter choices, and the judgement of what to claim
are the author's. Donald Della Pietra is responsible for the mathematical
claims and their verification.
