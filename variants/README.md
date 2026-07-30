# Admissibility variants of Erdős Problem 327: the multipliers k ≥ 2

This directory holds the companion manuscript to the main result of this
repository. The main manuscript, in [`../paper/`](../paper/), proves
`f_1(N) ≥ (1/2 + ε)N` for [Erdős Problem 327](https://www.erdosproblems.com/327).
This companion treats the general multiplier variants `k ≥ 2`.

It is not a separate project: it depends on the main manuscript (see
"Dependence" below) and shares its repository, its reproduction conventions
and its AI-use disclosure.

For `k ≥ 1` call a set `A` **k-admissible** if

```text
a + b ∤ k * a * b   for all distinct a, b ∈ A,
```

and let `f_k(N)` be the largest size of a k-admissible subset of
`{1, ..., N}`. Problem 327 asks about `k = 1` (first question) and `k = 2`
(second question).

## What is claimed

**Theorem 1.1 (periodic benchmark; proved here in full, elementary).**
A union of residue classes to a common modulus is k-admissible if and only if
every one of its classes consists of odd numbers and `k` is odd. Hence:

- for **odd** `k` the odd numbers are k-admissible and are the densest
  periodic k-admissible set, so the benchmark density is `1/2`;
- for **even** `k` the *only* periodic k-admissible set is the empty set, so
  the benchmark density is `0`.

An explicit conflicting pair is given in closed form for every class that is
not of the surviving type.

**Theorem 1.2 (odd multipliers).** For every odd `k ≥ 1` there is an absolute
`ε_k > 0` with

```text
f_k(N) ≥ (1/2 + ε_k) N   for all sufficiently large N.
```

At `k = 1` this is the companion manuscript's theorem and is not new here.
For `k > 1` the construction must dilate the sparse layer by
`λ(k) = least power of two ≥ k`, **not** by 2: with the dilation 2 the
construction fails outright whenever `3 | k` or `5 | k`, since `{n, 2n}` and
`{2n, 3n}` are then never k-admissible. See Remark 5.1 and flagged item 6.

**Theorem 1.3 (all multipliers).** For every `k ≥ 1` there is an absolute
`c_k > 0` with `f_k(N) ≥ c_k N` for all sufficiently large N. For odd `k`
this is trivial (the odd numbers already have density `1/2`); its content is
for **even** `k`, where by Theorem 1.1 no such trivial set exists. At `k = 2`
it reproves Sawin's theorem; for **even `k ≥ 4` it is, to our knowledge, the
first lower bound of any kind**.

**Not claimed.** We do *not* prove `f_2(N) ≥ (1/2 + o(1)) N`, the question
raised in the discussion thread, nor any bound for even `k` beyond positive
density, nor an explicit value for `ε_k` or `c_k`. Section 8 of the
manuscript ("Flagged items") lists every step that is imported, altered, or
unverified.

This is an unrefereed preprint and proof claim.

## Contents

- [Human-readable manuscript](erdos-327-variants-della-pietra.pdf)
- [`paper/`](paper/) — LaTeX source and numerical supplement
- [`paper/supplement/verify_certificate.py`](paper/supplement/verify_certificate.py)
  — standalone exact verifier (standard library only)
- [`paper/supplement/certificate-output.txt`](paper/supplement/certificate-output.txt)
  — recorded verifier output

## Reproduction

All paths below are relative to the repository root.

Build the companion manuscript:

```bash
cd variants/paper
make pdf
```

Run its verifier (a few seconds, standard library only, no dependencies):

```bash
python3 variants/paper/supplement/verify_certificate.py
```

The main manuscript and its own verifier are built with `cd paper && make pdf`
and `python3 paper/supplement/verify_certificate.py`; see the root
[`README.md`](../README.md).

## Dependence on the main manuscript

Theorem 1.2 depends on the main manuscript of this repository, which is an
unrefereed proof claim: if its Theorem 1.1 is wrong, Theorem 1.2 here is wrong
for every odd `k`, including `k = 1`. Theorem 1.3 depends only on the source
estimate, whose method is Sawin's published one. Theorem 1.1 and the
structural results of Section 7 are independent of both and are proved here in
full. Section 8 of the companion manuscript lists all ten flagged items.

It certifies, with exact integer and rational arithmetic and no load-bearing
floating-point comparison: the universal periodic witness and the resulting
benchmark densities; the conflict criterion `a+b | kab ⟺ x/(x,k) | g`; the
two-adic restriction and the mod-4 splitting at `k = 2`; the generalised
source coordinates for an arbitrary modulus; the two-endpoint mixed
coordinates for odd `k` and their converse, plus the exclusion of the small-u families and a **negative
control** recording why the dilation 2 is fatal; the root counts `3p−2` for both
linear-form triples; the complete small- and large-prime Euler factors,
including the modified factors at primes dividing the multiplier; the five
strict window inequalities with rational logarithm intervals of width below
`10^-80`; the symbolic cancellation of the `log L` exponents in both dyadic
assemblies; the largest-prime-factor fibration with its contraction
constant; and that the assembled two-layer set really is k-admissible in a
finite box for `k = 1, 3, 5, 7, 9`.

The last item confirms the combinatorics of the assembly, not the density
gain: the gain is asymptotic and requires `L` and `N` chosen in the legal
order, so no finite computation can establish it.

## Audit

An adversarial audit of the first draft found a **fatal error**: the draft
copied the companion's dilation `2`, which makes Theorem 1.2 false for every
odd `k` divisible by 3 or 5. The repair (the dilation `λ(k)`) is described in
Remark 5.1 and flagged item 6, and the verifier now carries a negative control
that would catch a regression. The audit also corrected a factual claim about
the class `7 mod 10` and a novelty overclaim for Theorem 1.3; both are fixed.
Theorem statements are unchanged by the repair.

These checks certify arithmetic, local densities and the numerical window.
They are not evidence for the two analytic mean-value inputs, which enter
only through the cited theorems of Tenenbaum and of de la Bretèche and
Tenenbaum.

## Formalization status

**Planned, not done.** There is no Lean development for this companion. The
repository's Lean formalization, in [`../lean/`](../lean/), covers `k = 1` and
`k = 2` only and certifies no statement made here.

## Prior-work status

A search completed on **2026-07-29** covering arXiv, the Problem 327 page,
its 11-comment discussion thread, and general web search found:

- Sawin, *Sets of unit fractions without two members whose average is a unit
  fraction* (arXiv:2607.15419), which proves `f_2(N) > cN` and treats `k = 2`
  only;
- leon2k2k2k's upper bounds `f_1 ≤ 0.7769N`, `f_2 ≤ 0.7630N`,
  `f_3 ≤ 0.6089N` (thread, 13 May 2026; checked by Nat Sothanaphan), with the
  in-thread question of whether `f_2(N) ≥ (1/2 + o(1))N`;
- Sawin's thread comment giving the greedy lower bound
  `N/(log N)^(0.3588...+o(1))` for `k = 2`;
- Wouter van Doorn's `25/28` upper bound for `k = 1`;
- StijnC's largest-prime-factor observation, whose equal-largest-prime case is
  left open there and is completed in the manuscript;
- **no lower bound for `f_k` with `k ≥ 3`** other than the odd numbers for
  odd `k` — in particular none at all for even `k ≥ 4` — and no prior
  treatment of the periodic benchmark.

These are qualified, dated search reports, not categorical priority claims.

## AI-use disclosure

AI systems provided substantial assistance with literature search, symbolic
and numerical exploration, adversarial auditing of the generalisation,
independent reconstruction of intermediate estimates, and drafting. The
identification of the periodic benchmark, the judgement of what does and does
not transfer from the `k = 1` argument, and the decision to report the
theorems above rather than a stronger claim are the author's. Donald Della
Pietra is responsible for the mathematical claims and their verification.
This matches the disclosure in the root [`README.md`](../README.md), which
covers the repository as a whole.
