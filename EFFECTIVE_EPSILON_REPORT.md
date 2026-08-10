# Effective epsilon certificate for Erdős Problem 327

## 1. Result

```text
EXPLICIT EPSILON FOUND: YES
LEVEL ACHIEVED: 1
```

The existing construction certifies a completely explicit positive rational
density gain.  The final ambient threshold is proved finite but remains
existential.

The audit theorem is
`Erdos327.EffectiveAudit.Analytic.erdos327Conclusion_explicit` in
`audit/EffectiveEpsilon.lean`:

```lean
∃ N₀ : ℕ, ∀ N ≥ N₀,
  ∃ A : Finset ℕ,
    A ⊆ Erdos327.upto N ∧
    Erdos327.OneAdmissible A ∧
    (1 / 2 + explicitEpsilon) * (N : ℝ) ≤ (A.card : ℝ)
```

Thus the first question in Erdős Problem 327 holds with the explicit epsilon
below, subject only to an existential finite `N₀`.

## 2. Explicit constants

```text
source budget K = 400000000
scale           = 10^26
log exponent    = 20000 * 10^26 = 2 * 10^30
J               = 2^(2 * 10^30)
L               = 8 * 2^J + 1
                = 8 * 2^(2^(2 * 10^30)) + 1
ε₀              = 1 / (128 * 6561 * (J + 4))
                = 1 / (839808 * (2^(2 * 10^30) + 4))
N₀              = finite existential; not explicit
```

All divisions in `explicitEpsilon` are divisions in `ℝ` by natural-number
casts, so this displayed value is an exact rational real number.  No decimal
or floating-point approximation is used in the certificate.

## 3. Exact epsilon derivation

The factor chain in the existing proof is exactly:

1. Set `ρ = roughDensity L / 2` in the canonical deletion argument.
2. `assembly_density_bound` gives an even-endpoint gain
   `η = ρ / 16 = roughDensity L / 32`.
3. The endpoint rescaling loses a factor `4`, giving
   `η / 4 = roughDensity L / 128`.

This chain is reconstructed by
`erdos327_fixed_gain_of_canonical_estimates`, rather than assumed from the
previous audit.

For the explicit cutoff, `one_div_6561_le_mertensLowerConstant` proves

```text
1 / 6561 ≤ mertensLowerConstant.
```

The existing explicit Mertens theorem and the elementary cutoff estimate give

```text
roughDensity L
  ≥ mertensLowerConstant / log L
  ≥ 1 / (6561 * log L)
  ≥ 1 / (6561 * (J + 4)).
```

The last inequality uses

```text
L = 8 * 2^J + 1,
log L ≤ (J + 4) * log 2 ≤ J + 4.
```

Therefore

```text
ε₀ = 1 / (128 * 6561 * (J + 4))
   ≤ roughDensity L / 128.
```

This is the theorem `explicitEpsilon_le_final_gain`; positivity is
`explicitEpsilon_pos`.

## 4. Threshold inventory

| Dependency-path choice | Original ineffective step | Certified replacement or status |
|---|---|---|
| Source regularity intercept | `exists_sourceTailBudget` | `explicitSourceBudget = 400000000`; `explicitSourceBudget_spec` proves the full tail inequality |
| Common dyadic start | intersections of eventual log/power and schedule conditions | `explicitJ = 2^(2*10^30)` with exact power comparisons |
| Source sieve schedule | eventual domination of sieve radius and factorial tail | `explicit_sieveSchedule_dominates`, `explicit_scheduledFactorialTail_le`, and the explicit block bounds |
| Source scheduled error | eventual error-tail budget | `explicit_sourceScheduledErrorTail_le_roughDensity` |
| Source bulk main range | eventual power/log summability | `explicit_sum_sourceEulerMain_bulk_le_roughDensity` |
| Source transition range | eventual cutoff comparison | `explicit_sum_sourceEulerMain_transition_le_roughDensity` |
| Source terminal range in `N` | `tendsto_sourceTerminalLogProfile` | `J` is explicit; the resulting `N` threshold `Nt` remains existential |
| Source small-residual range in `N` | `eventually_sum_sourceEulerMain_smallResidual_le` | `J,L` are explicit; the resulting `N` threshold `Ns` remains existential |
| Final source/rank-bad estimate | `eventually_exists_forall_card_rankBad_le_roughDensity` | `explicit_exists_forall_card_rankBad_le_roughDensity`; only its combined `N` threshold remains existential |
| Odd-host tail | `eventually_oddBudget_meets_tail` | `explicit_oddBudget_meets_tail` at the concrete `L` |
| Mixed moving start | eventual growth of `mixedBulkMovingStart` | exact identity `mixedBulkMovingStart explicitL = explicitJ - 1` |
| Mixed bulk main | eventual log-power absorption | `explicit_sum_mixedCanonicalBulkMain_le_roughDensity` |
| Mixed good-sieve error | eventual scheduled error comparison | `explicit_sum_mixedCanonicalGoodSieveError_le_roughDensity` |
| Mixed terminal convolution in `N` | `tendsto_mixedTerminalConvolutionPower_zero` | cutoff parameters are explicit; threshold `Nt` remains existential |
| Mixed transition boundary | eventual cutoff/log comparison | `explicit_sum_mixedTransitionBoundary_le` at the concrete cutoff |
| Mixed positive-residual boundary in `N` | `eventually_sum_mixedPositiveResidualBoundary_le` | threshold `Nb` remains existential |
| Additive mixed `+1` | Archimedean existence lemma | threshold `No` remains existential |
| Final rough interval count | lower bound requires `4 * roughPrimeModulus L ≤ N` | modulus is the explicit function evaluated at `explicitL`; included in the combined lower bound for `N` |
| Endpoint rescaling | `exists_nat_ge (4 * (1 + η) / η)` | finite threshold `K` remains existential |

The concrete cutoff therefore removes every final choice of `J`, `L`, and
`ε`; only limits in the ambient variable `N` remain ineffective.

Checklist:

```text
source cutoff and schedule conditions: PASS
mixed cutoff and schedule conditions:  PASS
odd-tail condition:                    PASS
rough-count prerequisites:             PASS for all sufficiently large N
canonical deletion budgets:            PASS
final explicit-epsilon theorem:         PASS
```

## 5. Dominant bottleneck

The enormous value of `J` comes from a deliberately crude common reserve,
not from numerical optimization.  `explicitScale = 10^26` simultaneously
absorbs all fixed source and mixed constants; for comparison, the largest
displayed mixed fixed-constant reserve is bounded by `2^800000360`.

The tight qualitative margin is the mixed outer coefficient.  From the
certified upper bound for `log(1.34288)`, exact arithmetic gives

```text
1 - 3.3912 * 0.29481657 - 1/10000
  = 14755977 / 125000000000
  > 1/10000.
```

An attempted `1/5000` lower bound would be false.  The checked proof uses
`1/10000`, so this is not an error in the existing theorem or paper statement.

## 6. Exact verification

Run the independent exact-arithmetic checker:

```sh
python3 audit/effective_epsilon.py
```

Expected output begins:

```text
EXACT PARAMETER CHECKS: PASS
explicitLogExponent = 2000000000000000000000000000000
J = 2^(2*10^30)
L = 8*2^J+1
epsilon = 1/(839808*(J+4))
```

The checker uses only Python integers and `fractions.Fraction`.

Check the formal certificate:

```sh
cd lean
lake env lean ../audit/EffectiveEpsilon.lean
lake build
```

Both commands complete successfully.  Lean emits only linter warnings for the
audit file.  The pull-request workflow also checks the audit certificate
directly.

## 7. Axiom audit

The file ends with reproducible `#print axioms` commands.  Lean reports:

```text
'Erdos327.EffectiveAudit.Analytic.erdos327Conclusion_explicit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Erdos327.EffectiveAudit.Analytic.erdos327Conclusion_with_explicitEpsilon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

These are the same standard foundations reported for the repository's
original unconditional conclusion.  The certificate introduces no axiom,
`sorry`, or `admit`.

## 8. Remaining ineffectivity

This is Level 1, not Level 2 or 3, because `N₀` is not an explicit evaluable
integer.  The unresolved components are:

- the source terminal-profile limit;
- the source small-residual eventual bound;
- the mixed terminal-convolution limit;
- the mixed positive-residual boundary limit;
- absorption of the additive mixed `+1`;
- the final endpoint-rescaling Archimedean threshold.

They prove that a finite `N₀` exists, and the final Lean theorem quantifies it,
but the present certificate does not give a numeral or fully explicit symbolic
expression for it.

## 9. Optimization opportunities

| Rank | Source of loss | Effect | Likely improvement |
|---:|---|---|---|
| 1 | Common reserve `explicitScale = 10^26` | Dominates `J`, hence dominates the size of `ε₀` | Replace the uniform reserve by per-estimate exponents |
| 2 | Source budget `400000000` and its exponential constants | Forces bounds around `2^800000004` | Sharpen the centered-tail constant and Bernoulli estimate |
| 3 | Mixed coefficient margin near `1.18e-4` | Restricts log absorption to `1/10000` | Improve certified parameter/log bounds or retune weights |
| 4 | Mertens lower constant `1/6561` | Direct factor in `ε₀` | Certify a sharper elementary lower bound |
| 5 | Structural factor `1/128` | Direct factor in final gain | Requires sharper deletion/rescaling bookkeeping |
| 6 | Remaining `N` limits | Prevents Level 2 | Effectivize the six limits listed above |

No optimization is mixed into this first certificate.
