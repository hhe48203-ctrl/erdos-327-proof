# Goal: Extract an explicit certified ε from the Lean proof of Erdős Problem 327

Repository:

`https://github.com/donalddellapietra/erdos-327-proof`

Audit context:

The existing audit concluded that the Lean development proves the first question of Erdős Problem 327 and that the final density gain can be traced symbolically to

\[
\varepsilon=\frac{\operatorname{roughDensity}(L)}{128}>0,
\]

where the proof fixes

\[
L=\operatorname{sourceCoupledCutoff}(J)=8\cdot 2^J+1
\]

for a sufficiently large but currently non-explicit `J`.

The current proof is therefore mathematically effective in structure but ineffective in its final parameter selection: several `Filter.Eventually`, existence, and asymptotic threshold arguments do not produce a concrete numeral for `J`, `L`, `N₀`, or `ε`.

The purpose of this task is to make the existing proof quantitatively explicit.

---

# Primary objective

Extract at least one completely explicit certified constant

\[
\boxed{\varepsilon_0>0}
\]

such that the existing argument proves

\[
\forall N\ge N_0,\quad
\exists A\subseteq\{1,\ldots,N\}
\]

with

\[
a+b\nmid ab
\qquad
\text{for all distinct }a,b\in A,
\]

and

\[
|A|\ge \left(\frac12+\varepsilon_0\right)N
\]

for some explicit finite integer `N₀`.

The first successful explicit value is more important than obtaining a good value.

Do not optimize prematurely.

A valid result such as

\[
\varepsilon_0=10^{-10^{100}}
\]

is acceptable if it is rigorously certified by the current proof architecture.

---

# Important distinction

There are two separate goals:

## Phase A — Effectivization

Find a concrete `J`, hence a concrete

```text
L = 8 * 2^J + 1
```

for which every eventual/asymptotic condition used by

```lean
Erdos327.Analytic.erdos327FullConclusion_unconditional
```

is simultaneously satisfied.

Then calculate a rigorous lower bound for

```text
roughDensity L / 128
```

and obtain an explicit `ε₀`.

This phase must preserve the mathematics of the existing proof.

## Phase B — Optimization

Only after Phase A succeeds, investigate whether smaller parameters or sharper bookkeeping substantially improve `ε₀`.

Phase B is optional.

Do not mix optimization changes into the first proof of effectivity.

---

# Required deliverables

Create:

```text
EFFECTIVE_EPSILON_REPORT.md
```

and, as appropriate,

```text
audit/effective_epsilon.py
audit/EffectiveEpsilon.lean
```

The final report must state prominently:

```text
EXPLICIT EPSILON FOUND: YES/NO
```

If YES, give:

```text
J  = ...
L  = ...
ε₀ = ...
N₀ = ...
```

where exact integers/rationals are preferred over decimal approximations.

If `N₀` is too enormous to print in decimal conveniently, an exact symbolic integer expression is acceptable, provided it is finite and independently evaluable.

---

# 1. Start from the actual final Lean proof

Inspect:

```lean
Erdos327.Analytic.erdos327FullConclusion_unconditional
```

and trace every choice involved in producing its final fixed cutoff.

The current proof structure is approximately:

```text
choose K
choose sufficiently large J
set L = sourceCoupledCutoff J
establish source estimate
establish mixed estimate
establish odd-tail estimate
define N₀
apply canonical reduction
obtain ε = roughDensity(L) / 128
```

Confirm this independently from the source.

Do not rely on the audit report's summary if the source differs.

---

# 2. Recover the exact final ε formula

Trace the following chain precisely:

```text
roughDensity L
→ canonical deletion budgets
→ EvenEndpointConclusion
→ erdos327Conclusion_of_evenEndpoint
→ Erdos327Conclusion
```

Determine the exact witness that the current Lean proof effectively constructs.

The audit suggests:

\[
\rho=\frac{\operatorname{roughDensity}(L)}2,
\]

then an even-endpoint gain

\[
\eta=\frac{\rho}{16}
=
\frac{\operatorname{roughDensity}(L)}{32},
\]

followed by endpoint rescaling

\[
\varepsilon=\frac{\eta}{4}
=
\frac{\operatorname{roughDensity}(L)}{128}.
\]

Verify every factor `2`, `16`, and `4` directly in Lean source.

If the true formula differs, use the Lean source as authoritative.

---

# 3. Inventory every ineffective step

Produce a table containing every use on the dependency path of constructs such as:

```lean
Filter.Eventually
Tendsto
eventually_atTop
.exists
Classical.choose
exists_*
IsBigO
IsLittleO
asymptotic
```

that participates in selecting the final fixed `J`, `L`, or `N₀`.

For each, record:

| Declaration | Variable | Current statement | Needed explicit form |
|---|---|---|---|
| `...` | `J` | eventually ... | `∀ J ≥ J₀, ...` |
| `...` | `L` | eventually ... | explicit `L₀` |
| `...` | `N` | eventually ... | explicit `N₀(L)` |

Classify each threshold as:

- already explicit but hidden;
- easy algebraic effectivization;
- requires explicit log/power comparison;
- requires explicit factorial-tail bound;
- requires explicit Mertens bound;
- genuinely nonconstructive;
- unknown.

The purpose of this inventory is to identify the actual bottleneck before modifying code.

---

# 4. Trace the three eventual conditions used to choose J

The final proof appears to intersect at least three eventual conditions:

1. source/rank-bad budget;
2. mixed-edge scheduled budget;
3. odd-host centered-tail budget.

Locate the exact declarations.

For each one, convert the statement conceptually from:

```lean
∀ᶠ J in atTop, P J
```

into an explicit theorem of the form:

```lean
∃ J₀, ∀ J ≥ J₀, P J
```

and then ideally:

```lean
theorem P_explicit :
  ∀ J ≥ NUMERAL, P J
```

or an executable Boolean/rational certificate that Lean can verify.

Determine which of these three produces the dominant threshold.

---

# 5. Effectivize all asymptotic comparisons

Pay special attention to inequalities of the general forms

\[
C(\log L)^a L^{-b}\le c,
\]

\[
C(\log L)^a 2^{-bJ}\le c,
\]

\[
\frac{C(\log\log L)^a}{(\log L)^b}\le c,
\]

\[
\frac{C^R}{R!}\le c,
\]

or similar polynomial, exponential, logarithmic, and factorial tails.

For every such comparison:

1. identify exact constants;
2. replace qualitative convergence with an explicit sufficient threshold;
3. prefer crude monotone inequalities to delicate numerical approximations;
4. prove or computationally certify the inequality using exact arithmetic.

A terrible explicit bound is acceptable.

A hidden `eventually` is not.

---

# 6. Preserve exact arithmetic

Do not use floating point as part of the correctness argument.

Use:

- integers;
- rationals;
- exact powers;
- certified rational bounds for logarithms if needed;
- Lean's exact arithmetic;
- Python `fractions.Fraction` for exploratory/verifier code.

Floating point may be used only to guess parameter sizes.

Every final accepted inequality must be independently reproducible using exact or rigorously directed arithmetic.

---

# 7. Handle logarithms rigorously

If explicit evaluation of `Real.log` becomes the main obstacle, do not silently replace it with floating-point values.

Use one of the following approaches:

1. derive rational upper/lower bounds from elementary inequalities already available in Lean;
2. prove crude inequalities such as
   \[
   \log x \le x^\delta
   \]
   beyond an explicit threshold;
3. compare powers after exponentiation;
4. use a small formally verified rational interval for the required logarithm;
5. avoid numerical evaluation entirely by choosing absurdly large power-of-two thresholds for which symbolic inequalities become easy.

Prefer proof simplicity over numerical quality.

---

# 8. Determine an explicit J

The central milestone is a concrete theorem or certified calculation establishing:

```text
J = J*
```

such that all final preconditions hold simultaneously for

```text
L = 8 * 2^J* + 1.
```

Do not choose `J*` based solely on numerical experimentation.

First find a candidate numerically if useful; then prove/certify all conditions exactly.

Produce a checklist:

```text
source condition: PASS
mixed condition: PASS
odd-tail condition: PASS
rough-count prerequisites: PASS
cutoff prerequisites: PASS
all remaining final-theorem hypotheses: PASS
```

---

# 9. Compute roughDensity(L)

Locate the exact definition of:

```lean
Erdos327.roughDensity L
```

Determine whether it is the finite Euler product

\[
\prod_{p<L}\left(1-\frac1p\right)
\]

or another precise cutoff convention.

Do not assume the endpoint convention.

For the final concrete `L`, obtain an exact certified positive lower bound.

There are two acceptable routes.

## Route A — direct finite product

If computationally feasible, calculate

\[
r_L=\operatorname{roughDensity}(L)
\]

exactly as a rational number.

Then take

\[
\varepsilon_0=\frac{r_L}{128}.
\]

## Route B — explicit Mertens lower bound

Use the already formalized inequality of the form

\[
\operatorname{roughDensity}(L)
\ge
\frac{C_{\mathrm M}}{\log L}
\]

with an explicit certified lower bound for the constant.

Then define a rational

\[
0<\varepsilon_0
\le
\frac{C_{\mathrm M}}{128\log L}.
\]

Route B may be much more practical for enormous `L`.

---

# 10. Obtain an exact ε₀

The final result should preferably use an exact rational constant:

\[
\varepsilon_0=\frac pq
\]

with integers `p,q>0`.

If the natural expression involves logs, choose a simpler rational below it.

For example, prove:

\[
\frac1{10^M}
\le
\frac{\operatorname{roughDensity}(L)}{128}
\]

and then use

\[
\boxed{\varepsilon_0=10^{-M}}.
\]

There is no requirement that this rational be close to optimal.

---

# 11. Extract an explicit N₀

Once `L` is fixed, trace the final definition:

```lean
N₀ = max Ns (max Nm (max L (4 * roughPrimeModulus L)))
```

or its actual current equivalent.

The remaining source and mixed estimates may themselves contain eventual `N` thresholds.

Effectivize those as well.

The target is a finite exact threshold satisfying:

```lean
∀ N ≥ N₀, ...
```

If the exact decimal expansion of `N₀` is absurdly large, an expression such as

```text
N₀ = max(...)
```

is not sufficient unless every component is itself explicit.

Expressions such as

```text
2^(2^12345)
```

are acceptable.

---

# 12. Strong preferred deliverable: an explicit Lean theorem

If feasible, add an audit-only theorem without modifying the original proof:

```lean
theorem erdos327Conclusion_explicit :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ A : Finset ℕ,
        A ⊆ Erdos327.upto N ∧
        Erdos327.OneAdmissible A ∧
        (1 / 2 + EXPLICIT_EPSILON) * (N : ℝ)
          ≤ (A.card : ℝ)
```

where `EXPLICIT_EPSILON` contains no existentially chosen parameters.

Even better:

```lean
def explicitEpsilon : ℚ := ...
def explicitN0 : ℕ := ...

theorem explicitEpsilon_pos :
    0 < explicitEpsilon := ...

theorem erdos327Conclusion_explicit :
    ∀ N ≥ explicitN0, ...
```

The audit theorem may import the existing project.

Do not introduce new axioms or `sorry`.

Run:

```lean
#print axioms erdos327Conclusion_explicit
```

and require only the same standard foundations as the original theorem.

---

# 13. If full N₀ extraction is too difficult

There are useful intermediate levels of success.

Report the strongest achieved level:

### Level 0
Only symbolic:

\[
\varepsilon=\operatorname{roughDensity}(L)/128.
\]

Already known; not a new result.

### Level 1
Concrete `J` and `L`, hence an explicit positive `ε₀`, but `N₀` remains existential.

This is already a meaningful success.

### Level 2
Explicit `ε₀` and explicit symbolic/evaluable `N₀`.

This achieves the main objective.

### Level 3
A Lean theorem containing explicit `ε₀` and `N₀`.

This is the preferred result.

### Level 4
Optimized explicit constants.

Optional.

Do not report failure merely because Level 3 cannot be reached.

---

# 14. Search for unnecessary sources of ineffectivity

Once the first explicit value is obtained, inspect whether the enormous threshold comes mostly from:

- coarse Mertens constants;
- centered-tail estimates;
- factorial truncation;
- source schedule;
- mixed schedule;
- boundary blocks;
- repeated generic `eventually` lemmas;
- converting even-endpoint density to the original interval.

Rank the losses.

Produce a table:

| Source of loss | Effect on J/L | Effect on ε | Easy to improve? |
|---|---:|---:|---|
| ... | ... | ... | ... |

This will determine whether optimizing `ε` is an interesting mathematical project or mostly proof engineering.

---

# 15. Do not change the mathematical strategy in Phase A

For the first explicit constant:

- do not introduce a new construction;
- do not alter sieve weights;
- do not improve the orientation;
- do not weaken any theorem;
- do not assume stronger external analytic estimates;
- do not replace formal estimates with numerical conjectures.

The question is:

> What explicit ε is already latent in the currently verified proof?

Only after answering that question should optimization begin.

---

# 16. Verification requirements

For every final numeric or symbolic bound:

- give the exact originating theorem;
- give exact input parameters;
- show the complete inequality chain;
- include a reproducible checker;
- avoid solver optimality assumptions;
- avoid floating-point truth decisions.

If Python generates a candidate certificate, Lean or a small exact verifier should decide validity independently.

---

# 17. Final report format

`EFFECTIVE_EPSILON_REPORT.md` must contain:

## 1. Result

```text
EXPLICIT EPSILON FOUND: YES/NO
LEVEL ACHIEVED: 0/1/2/3/4
```

## 2. Explicit constants

```text
J  = ...
L  = ...
ε₀ = ...
N₀ = ...
```

Also give decimal/scientific-notation approximations when useful.

## 3. Exact ε derivation

Show why the existing proof gives:

\[
\varepsilon\ge\varepsilon_0.
\]

## 4. Threshold inventory

List every formerly ineffective threshold and how it was made explicit.

## 5. Dominant bottleneck

Identify which estimate forces the largest `J` or `N₀`.

## 6. Exact verification

Give commands and outputs for all checkers/Lean builds.

## 7. Axiom audit

If a new Lean theorem was produced, include its exact:

```lean
#print axioms
```

output.

## 8. Remaining ineffectivity

State precisely what remains existential, if anything.

## 9. Optimization opportunities

Rank the most promising ways to enlarge `ε₀`.

---

# Success criterion

The main task succeeds as soon as there is a rigorously certified explicit rational number

\[
\boxed{\varepsilon_0>0}
\]

which is provably no larger than the density gain already supplied by the existing Della Pietra Lean proof.

Numerical quality is secondary.

Correctness and reproducibility are primary.