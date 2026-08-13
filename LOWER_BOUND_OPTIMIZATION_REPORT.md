MEANINGFUL LOWER-BOUND IMPROVEMENT: YES
BEST LEVEL: M2
LEAN CERTIFIED: YES
EXPLICIT N0: NO

# 1. Baseline and best result

The preserved baseline certificate uses

\[
E_0=2\cdot 10^{30},\qquad J_0=2^{E_0},\qquad
\varepsilon_0=\frac1{839808(2^{E_0}+4)}.
\]

Its exact binary difficulty is

\[
B(\varepsilon_0)=2\cdot10^{30}+20.
\]

The optimized certificate uses

\[
\begin{aligned}
E_1&=8\,810\,200\,000,\\
J_1&=2^{E_1},\\
L_1&=8\cdot2^{J_1}+1,\\
\varepsilon_1
  &=\frac1{839808(J_1+4)}
    =\frac1{839808(2^{8\,810\,200\,000}+4)}.
\end{aligned}
\]

Its exact binary difficulty is

\[
\boxed{B(\varepsilon_1)=8\,810\,200\,020\le 10^{10}},
\]

so the result reaches M2.  To check the last equality, put
\(C=839808=128\cdot6561\).  Exact integer arithmetic gives
\(2^{19}<C<2^{20}\), and, since \(E_1\ge5\),

\[
2^{E_1+19}<C(2^{E_1}+4)\le2^{E_1+20}.
\]

The exact comparison is monotonic: \(E_1<E_0\), hence
\(J_1<J_0\), and reciprocation of the positive denominators gives
\(\varepsilon_0<\varepsilon_1\).  Lean proves this as
`baseline_lt_optimizedEpsilon`; no floating-point comparison is used.

# 2. Theorem statement

The main public declaration is

```lean
Erdos327.Tuned.Analytic.OptimizedAudit.erdos327Conclusion_optimized :
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∃ A : Finset ℕ,
      A ⊆ Erdos327.upto N ∧
      Erdos327.OneAdmissible A ∧
      (1 / 2 + optimizedEpsilon) * (N : ℝ) ≤ (A.card : ℝ)
```

Here

```lean
def optimizedEpsilon : ℝ := epsilonAt explicitJ
```

is exactly the rational \(\varepsilon_1\) above, and Lean also exposes

```lean
optimizedEpsilon_pos
baseline_lt_optimizedEpsilon
erdos327Conclusion_with_optimizedEpsilon : Erdos327.Erdos327Conclusion
```

In ordinary language: there is one fixed positive rational gain
\(\varepsilon_1\) and one finite threshold \(N_0\) such that every
\(N\ge N_0\) has a subset of \(\{1,\ldots,N\}\) of size at least
\((1/2+\varepsilon_1)N\), with \(a+b\nmid ab\) for every two distinct
members.  The quantifier order and conflict predicate are unchanged.

# 3. Method

The final improvement combines two changes while leaving the baseline audit
untouched.

First, the source anatomy slope and source-tail base were jointly changed
from \(1.000001\) to the exact rational

\[
A_b=z_b=\frac{10003}{10000}.
\]

This enlarges the centered-tail gap enough to replace the baseline source
intercept \(K_b=400000000\) by \(K_b=440000\).  Since the dominant source
constants contain \(4^{K_b+2}=2^{2K_b+4}\), this removes essentially all of
the original deliberately inflated scale.

Second, the cutoff proof no longer routes every `1/10000` logarithmic
absorption through \(\sqrt J\le\log L\).  For
\(L=8\cdot2^J+1\), the stronger elementary bound

\[
J/2\le J\log2=\log(2^J)\le\log L
\]

allows the master exponent to be

\[
E_1=10000(\texttt{explicitScale}+1)
\]

instead of \(20000\cdot\texttt{explicitScale}\).  The selected scale
`881019` is the first convenient value that both meets the dominant source
transition reserve and makes \(E_1\) divisible by `100000` for the smallest
logarithmic absorption.

The tuned summation stack is isolated in `Erdos327.Tuned.Analytic`.  It is
mechanically regenerated from the existing modules by
`audit/generate_tuned_stack.py`; the production modules and
`audit/EffectiveEpsilon.lean` are not edited.

# 4. Loss ledger

| Loss or threshold | Exact source | Baseline | Optimized | Effect on final score / remedy |
|---|---|---:|---:|---|
| Source slope/base | Tail instantiation | \(1000001/10^6\) | \(10003/10000\) | Creates a usable centered-tail gap while preserving all mixed and source exponent inequalities. |
| Source centered-tail inverse | Geometric tail ratio | at most \(3000000000001\) | at most \(22225557\) | Makes a much smaller certified source intercept possible. |
| Source intercept \(K_b\) | Tail budget | \(400000000\) | \(440000\) | Changes the core budget factor from \(2^{800000004}\) to \(2^{880004}\). |
| Scheduled source error | `sourceErrorTailConstant` | reserve dominated by global scale | exponent \(2K_b+12=880012\) | Below the final scale; not binding. |
| Source transition with final coefficient | Transition asymptotic constant and \(64\cdot6561\) | exponent \(2K_b+1019\) | exponent \(881019\) | Dominant final fixed-constant threshold. |
| Mixed moving main | Main constant times moving tail | exponent \(2K_b+360\) | \(880360\) | Fits below `scale-26 = 880993`; no longer dominant. |
| Mixed bulk/transition errors | Fixed mixed constants | up to \(2K_b+200\) | at most \(880200\) | Fits below the same fixed-capacity threshold. |
| Logarithmic cutoff conversion | `log L` lower bound | \(E=20000\,\text{scale}\) | \(E=10000(\text{scale}+1)\) | The direct \(J/2\) bound halves the remaining master exponent. |
| Final density factors | \(1/6561\) and `/128` | \(C=839808\) | unchanged | Costs exactly 20 binary-difficulty bits; negligible beside \(E\). |
| Ambient threshold | Six eventual limits | existential | existential | Does not affect \(\varepsilon\), but prevents a concrete applicability range. |

After the intercept reduction, the source transition reserve is the active
scale constraint.  Reducing the scale to the next lower value compatible
with the divisibility convention (`881009`) fails exactly at
`2K+1019 = 881019 > 881010`.

# 5. Exact certificate

The load-bearing parameters are exact terminating rationals:

| Parameter | Exact value |
|---|---:|
| Source anatomy slope \(A_b\) | \(10003/10000\) |
| Source tail base \(z_b\) | \(10003/10000\) |
| Odd anatomy slope \(A_o\) | \(116312/100000\) |
| Odd tail base \(z_o\) | \(134305/100000\) |
| Mixed source weight \(q_b\) | \(248933/100000\) |
| Mixed odd weight \(q_o\) | \(134288/100000\) |
| Odd-budget slope | \(33912/10000\) |
| Source intercept \(K_b\) | \(440000\) |
| `explicitScale` | \(881019\) |
| `explicitLogExponent` | \(8810200000\) |

The independent checker uses only Python integers and `fractions.Fraction`.
Its directed rational margins are:

| Obligation | Certified margin/lower bound |
|---|---:|
| Source exponent margin using \(\log4<7/5\) | \(4979/50000\) |
| Source centered exponent gap \(d\) | \(9/200030000\) |
| Source centered ratio gap | \(9/200030009\ge1/22225557\) |
| Odd deletion margin | \(13198523/62500000000\) |
| Mixed bulk margin | \(14755977/125000000000\) |
| Mixed error margin | \(3648022116849/10^{14}\) |
| Mixed cross-tail margin | \(90412821635684463/2611618336250000000000\ge1/30000\) |
| Mixed terminal absorption | \(351574655260684463/5223236672500000000000\ge1/25000\) |

For the source tail, the exact chain is

\[
d\ge\frac9{200030000},\qquad
1-e^{-d}\ge\frac9{200030009}\ge\frac1{22225557},
\]

so the centered-tail constant is at most
\(3^{98}\cdot22225557\).  Bernoulli and integer powers give

\[
z_b^{100}\ge\frac{103}{100},\qquad
z_b^{10000}\ge19,
\]

and the final integer check is

\[
19^{44}\ge8\cdot3^{98}\cdot22225557.
\]

The checker command and exact output are:

```text
$ python3 audit/optimized_lower_bound.py
OPTIMIZED EXACT PARAMETER CHECKS: PASS
source budget K = 440000
scale = 881019
explicitLogExponent = 8810200000
J = 2^8810200000
L = 8*2^J+1
epsilon = 1/(839808*(2^8810200000+4))
binary difficulty B = 8810200020
source exponent margin lower bound = 4979/50000
source centered d lower bound = 9/200030000
source centered ratio-gap lower bound = 9/200030009
odd deletion margin lower bound = 13198523/62500000000
mixed bulk margin lower bound = 14755977/125000000000
mixed error margin lower bound = 3648022116849/100000000000000
mixed cross-tail margin lower bound = 90412821635684463/2611618336250000000000
mixed terminal absorption = 351574655260684463/5223236672500000000000
best milestone = M2
```

It also reports the first failed inequality for rejected inputs.  For
example:

```text
$ python3 audit/optimized_lower_bound.py --scale 881009
FIRST FAILED INEQUALITY: source transition reserve
2K+1019 = 881019 > E/10000 = 881010
```

# 6. Lean verification and axiom audit

Verification was performed at commit
`2d014f6b514d3bd3736ed235439e81a9b25e0990` on branch `main`, preserving the
pre-existing worktree.  At task start the branch was four commits ahead of
`origin/main` and the only worktree entries were three untracked goal
documents; all were preserved.  The tools were Python 3.13.11, Lake
`5.0.0-src+62eed1d`, and Lean `4.33.0-rc1` for
`arm64-apple-darwin24.6.0` (Lean commit
`62eed1db4d67327ec8120be05f1a1b0847d74561`).

The reproducibility commands are:

```bash
python3 audit/effective_epsilon.py
python3 audit/optimized_lower_bound.py

cd lean
python3 ../audit/generate_tuned_stack.py
lake clean
lake build Erdos327
lake build Erdos327.Tuned
lake env lean ../audit/EffectiveEpsilon.lean
lake env lean ../audit/OptimizedLowerBound.lean
```

Both exact checkers print their respective `PASS` line.  Both targeted Lean
audits exit successfully.  A clean rebuild (after deleting only generated
`.lake/build` artifacts) also exits successfully; existing linter warnings
are non-fatal and do not include proof holes.

The optimized audit prints exactly:

```text
'Erdos327.Tuned.Analytic.OptimizedAudit.erdos327Conclusion_optimized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Erdos327.Tuned.Analytic.OptimizedAudit.erdos327Conclusion_with_optimizedEpsilon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

This is identical to the baseline foundation closure.  The new checker,
generator, tuned module, and optimized audit contain no `sorry`, `admit`,
project-local axiom, or `unsafe` declaration.

# 7. Ambient threshold

The ambient \(N_0\) remains existential.  The optimized proof constructs a
finite maximum after obtaining source and mixed thresholds, but those inputs
still depend on the same six non-effectivized limits as the baseline:

1. source terminal profile;
2. source small-residual range;
3. mixed terminal convolution;
4. mixed positive-residual boundary;
5. absorption of the additive mixed `+1`;
6. final endpoint rescaling.

Thus this report makes no numerical applicability claim for a concrete
\(N\).  The cutoff \(J_1\), roughness level \(L_1\), and gain are explicit;
the final ambient threshold is not.

# 8. Pareto frontier

| Candidate | Exact gain | Binary difficulty | \(N_0\) | Assumptions / axioms | Verification cost | Frontier status |
|---|---|---:|---|---|---|---|
| Preserved baseline | \(1/[839808(2^{2\cdot10^{30}}+4)]\) | \(2\cdot10^{30}+20\) | existential | unconditional; `propext`, `Classical.choice`, `Quot.sound` | Existing 5.5k-line audit plus exact checker | Dominated, retained as regression |
| Optimized M2 | \(1/[839808(2^{8810200000}+4)]\) | \(8810200020\) | existential | same theorem and same axiom closure | Generated isolated 11,058-line tuned stack, 5.5k-line audit, exact checker | Best certified point |

Because both points have the same theorem strength and existential status,
the optimized point strictly dominates the baseline.  No explicit-\(N_0\)
candidate was certified, so there is not yet an epsilon-versus-threshold
tradeoff branch.

# 9. Failed and abandoned approaches

1. **Scale compression with the old source base.**  Removing only the
   `10^26` reserve reached a transient M1-scale candidate, but the
   \(1.000001\) centered-tail gap still forced an intercept on the order of
   \(10^8\).  Since constants grow as \(4^{K_b}\), that route had no credible
   path to M2.  The decisive obstruction is exact arithmetic, not numerical
   optimizer behavior.

2. **Sharpening only terminal constants.**  Replacing `1/6561`, `/128`, or
   their nearby bookkeeping factors can recover only about 20 bits while the
   master exponent was between \(10^{12}\) and \(10^{30}\).  This is a proved
   scale mismatch, so such changes were deferred until the exponent was
   compressed.

3. **Keeping the square-root cutoff conversion.**  Even after source tuning,
   the route \(\sqrt J\le\log L\) costs a factor of two in the master
   exponent.  The direct \(J/2\le\log L\) lemma superseded it.

4. **Pure periodic replacement.**  The repository's companion manuscript
   proves that a union of residue classes modulo one fixed modulus cannot
   beat density \(1/2\) for \(k=1\).  This is a proved obstruction, so a
   purely periodic alternative was not experimentally pursued.

5. **Immediate explicit-\(N_0\) work.**  Effectivizing just one terminal
   limit would not produce a usable threshold because five independent
   existential limits would remain.  This branch was postponed in favor of
   the successful M2 epsilon compression; its obstruction is architectural,
   not a claim of impossibility.

# 10. Remaining opportunities

Ranked by expected mathematical leverage:

1. **Remove the exponential \(4^{K_b}\) budget loss.**  Retain exact Euler
   products, use nonuniform anatomy budgets, or handle early blocks exactly.
   M3 requires reducing binary difficulty from \(8.8\cdot10^9\) to roughly
   333, so another round of constant tuning cannot suffice.

2. **Re-optimize the coupled mixed window.**  The current source slope is
   limited by a relatively narrow mixed cross-tail margin.  Joint movement
   of \(A_b,A_o,q_b,q_o\), and the odd-budget slope may permit a larger source
   tail base and smaller \(K_b\), but this remains within the M2 regime unless
   the exponential budget is also changed.

3. **Improve mixed-conflict deletion structurally.**  Degree-sensitive
   vertex cover, matching, or weighted independent-set information could
   replace the one-deletion-per-edge accounting.  This is more promising
   than shaving the final `/128`, though it must interact with cutoff control
   to change a milestone.

4. **Effectivize the six ambient limits as one dependency chain.**  This will
   add an explicit-\(N_0\) branch to the Pareto frontier and reveal whether
   the proof applies at any remotely interpretable scale.

5. **Only then sharpen the Mertens and terminal allocation constants.**
   These are trustworthy small improvements, but their impact is measured in
   tens of bits rather than billions.
