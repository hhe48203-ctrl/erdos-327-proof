# Goal: Substantially improve the certified density lower bound for Erdős Problem 327

Working repository and authoritative baseline:

`/Users/aa/Desktop/erdos-327-proof`

The baseline is the current local checkout and worktree at the start of the
task, including its checked-out branch, local commits, and pre-existing
uncommitted or untracked files. Inspect and preserve that state. Do not
replace it with a fresh clone, reset it to a remote branch, or assume that a
GitHub copy is newer or authoritative.

Upstream provenance only, not the working baseline:

`https://github.com/donalddellapietra/erdos-327-proof`

## Mission

Starting from the repository's existing Level-1 certificate, autonomously
search for and formally certify a substantially larger explicit constant

\[
\boxed{\varepsilon_{\mathrm{new}}>0}
\]

such that, for some finite threshold \(N_0\), every \(N\geq N_0\) admits a
set \(A\subseteq\{1,\ldots,N\}\) satisfying

\[
a+b\nmid ab\qquad(a,b\in A,\ a\ne b)
\]

and

\[
|A|\geq\left(\frac12+\varepsilon_{\mathrm{new}}\right)N.
\]

This is a long-horizon optimization and mathematical research task. Do not
stop after writing a plan, locating a bottleneck, finding a floating-point
candidate, obtaining a tiny constant-factor improvement, or completing only
one promising line of attack. Work in repeated conjecture–test–certify
cycles, retain reproducible checkpoints, and switch methods when evidence
shows that another route has better leverage.

No existing construction, parameterization, or proof architecture has
protected status. Improving the current certificate is the natural first
move, but a different proof or construction is welcome if it proves the same
unconditional theorem.

---

## Authoritative baseline

The current audit-only Lean certificate is

```lean
Erdos327.EffectiveAudit.Analytic.erdos327Conclusion_explicit
```

in `audit/EffectiveEpsilon.lean`. It proves the required conclusion with an
existential finite \(N_0\) and

\[
\begin{aligned}
K_b&=400000000,\\
J_0&=2^{2\cdot10^{30}},\\
L_0&=8\cdot2^{J_0}+1,\\
\varepsilon_0
&=\frac{1}{839808\,(J_0+4)}
 =\frac{1}{839808\,(2^{2\cdot10^{30}}+4)}.
\end{aligned}
\]

The exact Lean factor chain is

\[
\operatorname{roughDensity}(L)
\longrightarrow \frac{\operatorname{roughDensity}(L)}{32}
\longrightarrow \frac{\operatorname{roughDensity}(L)}{128}.
\]

The final comparison uses

\[
\operatorname{roughDensity}(L)
\geq \frac{1}{6561\log L}
\geq \frac{1}{6561(J+4)}.
\]

`EFFECTIVE_EPSILON_REPORT.md` is the baseline report. Read the actual Lean
dependency path before changing anything; when prose and Lean differ, Lean is
authoritative.

The ambient threshold \(N_0\) is still existential. The unresolved limits are
the source terminal profile, source small-residual range, mixed terminal
convolution, mixed positive-residual boundary, absorption of the additive
mixed `+1`, and final endpoint rescaling.

The companion manuscript also proves that a union of residue classes modulo
a fixed common modulus cannot beat density \(1/2\) for \(k=1\). Therefore a
purely periodic alternative is not a viable final construction; any new
construction beating \(1/2\) must be genuinely nonperiodic, depend on \(N\),
or use periodic pieces in a nonperiodic way.

Preserve the baseline certificate as a regression test. Put experimental and
improved certificates in new files until they are independently verified.

---

## What “meaningful” means

A larger exact rational is necessary, but the present denominator is so large
that ordinary multiplicative comparisons hide the real progress. For an
exact rational \(\varepsilon>0\), define its binary difficulty by

\[
B(\varepsilon)
=\min\{b\in\mathbb N:2^{-b}\leq\varepsilon\}.
\]

This can be checked with integer arithmetic: for \(\varepsilon=p/q\), test
\(q\leq p2^b\). Smaller \(B\) is better. The current certificate has exactly

\[
B(\varepsilon_0)=2\cdot10^{30}+20.
\]

Use the following milestones:

| Level | Certified target | Interpretation |
|---|---:|---|
| Progress | \(\varepsilon_{\mathrm{new}}>\varepsilon_0\) | Record it, but do not stop here |
| M1 | \(B(\varepsilon_{\mathrm{new}})\leq10^{15}\) | Minimum meaningful certificate improvement |
| M2 | \(B(\varepsilon_{\mathrm{new}})\leq10^{10}\) | Removes nearly all deliberately inflated scale |
| M3 | \(\varepsilon_{\mathrm{new}}\geq10^{-100}\) | Human-interpretable asymptotic gain |
| M4 | \(\varepsilon_{\mathrm{new}}\geq10^{-6}\) | Practically visible density gain |

M1 is a checkpoint, not a reason to abandon a credible path toward M2–M4.
Constant-factor improvements to `1/6561`, `1/128`, or similar terminal
bookkeeping are useful, but by themselves they are not a meaningful final
answer while \(J\) remains on the current scale.

Maintain a Pareto frontier rather than a single headline number. For every
certified candidate record:

- the exact \(\varepsilon\);
- \(B(\varepsilon)\);
- whether \(N_0\) is existential or explicit;
- the size or symbolic form of an explicit \(N_0\), if available;
- the mathematical assumptions and Lean axiom closure;
- proof and verification cost.

Do not improve \(\varepsilon\) by silently weakening “for every sufficiently
large \(N\),” changing the conflict relation, allowing \(\varepsilon\) to
depend on \(N\), or proving only a limsup or infinitely-many-\(N\) statement.

---

## Primary objectives

### Objective A — Remove artificial slack in the existing certificate

The first target is the deliberately crude common reserve

```lean
explicitScale = 10^26
explicitLogExponent = 20000 * explicitScale
```

which dominates the current value of \(J\). Replace one global reserve by
separate sharp-enough thresholds for the estimates that actually need them.

For every inequality currently discharged from `explicitScale`, determine:

1. its exact constant and exponent;
2. the smallest or a near-smallest convenient certified threshold;
3. whether monotonicity lets later estimates reuse that threshold;
4. its individual effect on \(J\), \(L\), and \(B(\varepsilon)\).

Do not merely replace \(10^{26}\) with another guessed round number. Build an
exact checker that accepts proposed parameters and identifies the first
failed inequality.

### Objective B — Jointly optimize the current mathematical parameters

The present parameters were chosen to establish strict feasibility, not to
maximize the explicit density gain:

\[
\begin{aligned}
A_b&=1.000001,&q_b&=2.48933,\\
A_o&=1.16312,&q_o&=1.34288,\\
z_o&=1.34305,&c&=3.3912.
\end{aligned}
\]

The current certificate also uses the deliberately generous
\(K_b=400000000\), and constants such as `sourceBudgetConstant K` then grow
like \(4^K\). Treat the parameter system as a coupled optimization problem,
not as a list of independent decimals.

Search rigorously over rational candidates for:

- source anatomy slope and source-tail base;
- odd anatomy slope and odd-tail base;
- source and odd mixed weights;
- odd-budget slope;
- source-tail intercept \(K_b\);
- error-budget allocations and schedule exponents;
- the cutoff relation between \(J\) and \(L\).

Track all strict feasibility constraints, including the source exponent,
both centered-tail gaps, odd-deletion exponent, mixed bulk exponent, and
mixed terminal exponent. Optimize the final certified \(B(\varepsilon)\),
not a surrogate margin in isolation.

Floating-point or nonlinear optimization may generate candidates. Every
accepted candidate must be converted to rationals and rechecked by exact
integer/rational inequalities or rigorously directed intervals before Lean
formalization.

### Objective C — Make the ambient threshold effective

In parallel with improving \(\varepsilon\), effectivize the six remaining
limits in \(N\). Produce an explicit evaluable `optimizedN0` when feasible.
An expression such as a tower of powers, a factorial, or a finite maximum is
acceptable only when every leaf of the expression is explicit and
independently evaluable.

This objective is secondary to increasing \(\varepsilon\), but it determines
whether the lower bound applies at any concrete \(N\). Do not claim a
“practical” bound while its \(N_0\) remains existential or vastly beyond the
range being discussed.

### Objective D — Seek structural improvements and new constructions

If tuning the current proof encounters a hard floor, change the mathematics.
Promising examples include, but are not limited to:

- decoupling the source cutoff, sieve schedule, and mixed-edge cutoff;
- treating early dyadic blocks exactly and using asymptotics only for the
  tail;
- nonuniform or block-dependent anatomy budgets;
- sharper centered-tail and factorial-tail estimates;
- retaining exact Euler products instead of replacing them by uniform
  powers of two;
- direct evaluation of `roughDensity L` at a genuinely manageable cutoff;
- optimizing the allocation of the `/8`, `/16`, and `/64` deletion budgets;
- improving the rank orientation or replacing the “keep at least half” step
  with a weighted independent-set argument;
- deleting mixed conflicts by degree, matching, or weighted vertex-cover
  information instead of charging one deletion per edge;
- using several rough source layers or several even layers;
- randomized selection, alteration, entropy, or local-lemma arguments on the
  conflict graph;
- a different nonperiodic base set in place of “almost all odds plus doubled
  rough sources”;
- stronger but fully proved local sieve weights or linear-form estimates.

Finite computation, SAT/ILP, graph experiments, and random search are welcome
for discovering patterns or falsifying conjectures. They do not count as an
asymptotic proof until a uniform construction and rigorous estimates are
supplied.

Do not reject an approach merely because it does not fit the existing Lean
modules. First decide whether it could materially improve the mathematical
bound; then design the smallest trustworthy formal interface it needs.

---

## Research workstreams

Keep several conceptually distinct workstreams in the ledger. At minimum,
investigate the following before declaring that the current architecture has
been exhausted.

### Workstream 1 — Certificate compression

- Replace `explicitScale` by per-lemma thresholds.
- Remove unused powers-of-two slack.
- Use exact logarithmic intervals only where necessary.
- Compute the best \(J\) supported by the current fixed parameters.
- Quantify how much of \(B(\varepsilon)\) is pure certification slack.

### Workstream 2 — Parameter optimization

- Build a fast exploratory optimizer for the strict parameter window.
- Validate candidates with exact rational arithmetic.
- Optimize \(K_b\) together with \(A_b\) and the source-tail base.
- Rebalance mixed bulk and terminal margins rather than maximizing either
  alone.
- Produce sensitivity data and a rigorous neighborhood around the best
  candidate, so the result does not depend on a numerically fragile point.

### Workstream 3 — Proof-constant sharpening

- Locate each exponential dependence on \(K_b\).
- Distinguish genuine combinatorial loss from a proof convenience.
- Sharpen the Mertens constant only after the dominant \(J\)-scale losses are
  controlled.
- Revisit the final `roughDensity/128` assembly factor and endpoint rounding.
- Compare the manuscript's bookkeeping with the exact Lean bookkeeping and
  explain every discrepancy.

### Workstream 4 — Alternative construction

- Model the divisibility relation as a conflict graph and inspect degree and
  codegree structure.
- Test nonperiodic, multiscale, weighted, and probabilistic constructions.
- Use finite optimizers to identify stable structure across increasing \(N\),
  not to overfit one range.
- Turn a discovered pattern into a parameterized family and prove a uniform
  positive-density theorem.

### Workstream 5 — Explicit \(N_0\)

- Replace each `Filter.Eventually` on the final dependency path by a concrete
  threshold theorem.
- Keep the best \((\varepsilon,N_0)\) pairs on a Pareto frontier.
- Separate a mathematically large \(N_0\) from one inflated only by formal
  convenience.

These workstreams need not be executed in this order. Use cheap experiments
to decide where rigorous effort has the highest expected payoff, and revisit
earlier workstreams when a new estimate changes the optimization landscape.

---

## Autonomous operating protocol

### 1. Establish a trustworthy baseline

Run the existing exact checker and targeted Lean certificate before editing.
Record the current commit, toolchain, outputs, and baseline \(B\). Do not spend
hours on an unnecessary clean rebuild at every iteration; reserve full builds
for promoted candidates and final verification.

### 2. Build a loss ledger

Create a table with one row for every loss that affects \(\varepsilon\),
\(J\), or \(N_0\):

| Loss or threshold | Exact source | Current bound | Dependency | Effect on final score | Candidate remedy |
|---|---|---:|---|---:|---|
| ... | ... | ... | ... | ... | ... |

Update this ledger whenever an apparent bottleneck is removed; the next
bottleneck may be qualitatively different.

### 3. Use hypothesis-driven cycles

For each research cycle, write down:

1. the proposed mechanism;
2. the expected change in \(B(\varepsilon)\) or \(N_0\);
3. the cheapest decisive experiment;
4. the exact proof obligations if the experiment succeeds;
5. the observed result and next action.

Prefer experiments that can kill a weak idea quickly. Promote successful
ideas through these gates:

```text
exploratory computation
→ exact standalone certificate
→ parametric mathematical lemma
→ Lean theorem
→ axiom audit and regression build
```

Do not formalize a large new branch before checking that its projected gain
is material.

### 4. Pivot instead of looping

After repeated failures for the same reason, formulate the obstruction
precisely and move to a different workstream. Return only if a new lemma,
parameter window, or construction changes the obstruction. Preserve negative
results in the report so they are not rediscovered.

### 5. Make routine decisions autonomously

Do not pause for user confirmation about ordinary reversible choices such as
file organization, exploratory parameter ranges, proof decomposition, or
which promising workstream to test next. Ask only when permissions, external
authority, or a genuinely outcome-changing ambiguity requires it.

### 6. Keep the repository recoverable

- Preserve unrelated user changes.
- Keep the known-good baseline runnable.
- Separate generated data from load-bearing certificates.
- Make small, reviewable changes.
- Never hide a failed check or loosen a theorem to make a build pass.

### 7. Continue beyond the first win

Once a better certified \(\varepsilon\) is found, recompute the loss ledger
and continue while another route has credible leverage. A first strict
improvement is evidence that the pipeline works, not completion of this goal.

---

## Rigor and trust requirements

Every final lower bound must satisfy all of the following:

- exact integers, rationals, or rigorously directed real intervals decide all
  load-bearing numerical inequalities;
- floating point is used only for discovery;
- the theorem has the same quantifier order and conflict predicate as
  `Erdos327Conclusion`;
- no `sorry`, `admit`, project-local axiom, `unsafe` escape, or unchecked
  certificate is introduced;
- any new analytic input is proved in Lean or its trust status is explicitly
  separated from the unconditional result;
- `#print axioms` shows no foundations beyond those already used by the
  baseline theorem (`propext`, `Classical.choice`, and `Quot.sound`);
- a small independent exact checker reproduces the numerical certificate;
- the baseline and improved certificates both still compile;
- the final claim is not based on solver-reported optimality without a
  separately checkable certificate.

When using recent literature or a stronger external theorem, consult and cite
primary sources, record the exact version and hypotheses, and distinguish a
proved dependency from an informal suggestion. Do not make priority claims
from an undated or incomplete search.

---

## Required deliverables

Create or update, as appropriate:

```text
LOWER_BOUND_OPTIMIZATION_REPORT.md
audit/OptimizedLowerBound.lean
audit/optimized_lower_bound.py
```

Additional exploratory files are allowed when they have a clear purpose.
Do not overwrite `audit/EffectiveEpsilon.lean`; it is the certified baseline.

The improved Lean file should expose definitions and theorems analogous to:

```lean
def optimizedEpsilon : ℝ := ...

theorem optimizedEpsilon_pos :
    0 < optimizedEpsilon := ...

theorem baseline_lt_optimizedEpsilon :
    explicitEpsilon < optimizedEpsilon := ...

theorem erdos327Conclusion_optimized :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ A : Finset ℕ,
        A ⊆ Erdos327.upto N ∧
        Erdos327.OneAdmissible A ∧
        (1 / 2 + optimizedEpsilon) * (N : ℝ) ≤ (A.card : ℝ) := ...
```

If \(N_0\) is effectivized, prefer the stronger form:

```lean
def optimizedN0 : ℕ := ...

theorem erdos327Conclusion_optimized_effective :
    ∀ N ≥ optimizedN0, ... := ...
```

Names may change to fit the final architecture, but the report must identify
the exact public declarations.

---

## Report format

`LOWER_BOUND_OPTIMIZATION_REPORT.md` must begin with:

```text
MEANINGFUL LOWER-BOUND IMPROVEMENT: YES/NO
BEST LEVEL: Progress/M1/M2/M3/M4
LEAN CERTIFIED: YES/NO
EXPLICIT N0: YES/NO
```

It must then contain:

## 1. Baseline and best result

Give exact formulas for \(\varepsilon_0\), \(\varepsilon_{\mathrm{best}}\),
their binary difficulties, and the exact comparison proof.

## 2. Theorem statement

Write out the final Lean declaration and its ordinary mathematical meaning.

## 3. Method

Explain the mathematical or certification changes that produced the gain.

## 4. Loss ledger

Show the initial and final bottlenecks and their effect on the score.

## 5. Exact certificate

List all parameters, strict margins, checker commands, and outputs.

## 6. Lean verification and axiom audit

Give targeted-check and full-build commands plus exact `#print axioms`
output.

## 7. Ambient threshold

State whether \(N_0\) is existential or explicit. If explicit, give its exact
evaluable definition and an order-of-magnitude description.

## 8. Pareto frontier

List the best certified tradeoffs between \(\varepsilon\), \(N_0\), proof
strength, and proof complexity.

## 9. Failed and abandoned approaches

Record what was tried, the decisive obstruction, and whether the obstruction
is proved or empirical.

## 10. Remaining opportunities

Rank the next approaches by expected mathematical leverage, not by ease of
implementation.

---

## Verification commands

At minimum, the final result should be reproducible with commands equivalent
to:

```bash
python3 audit/effective_epsilon.py
python3 audit/optimized_lower_bound.py

cd lean
lake env lean ../audit/EffectiveEpsilon.lean
lake env lean ../audit/OptimizedLowerBound.lean
lake build Erdos327
```

Record toolchain versions and exact outputs. A full clean dependency rebuild
is necessary for final release-level verification, not for every research
cycle.

---

## Completion criteria

Do not mark this goal complete unless all of the following hold:

1. an exact rational \(\varepsilon_{\mathrm{new}}>\varepsilon_0\) is proved;
2. the result reaches at least M1, so it is more than a cosmetic
   constant-factor change;
3. the unchanged Erdős 327 conclusion is kernel-checked in Lean;
4. an independent exact checker reproduces the numerical certificate;
5. the baseline remains valid and the project build passes;
6. the axiom closure is unchanged;
7. the optimization report gives the exact comparison, bottlenecks, failed
   approaches, and status of \(N_0\).

After reaching M1, continue toward M2 or beyond while a concrete method has a
credible path. If the work ultimately cannot reach M1, do not relabel a small
improvement as meaningful. Report the strongest certified progress, identify
the exact blocker, and document why at least three structurally different
approaches failed before declaring the goal blocked.

The north star is not a prettier expression for an imperceptible constant.
It is the strongest trustworthy, reproducible, and mathematically informative
lower bound that sustained exploration can extract or prove.
