# Goal: Independently audit the claimed Lean proof of Erdős Problem 327

Repository:

`https://github.com/donalddellapietra/erdos-327-proof`

## Objective

Perform an adversarial, reproducible review of the repository's claim that it gives a complete Lean 4 formalization of the first question of Erdős Problem 327.

The central claim to verify is:

> There exists a fixed real number `ε > 0` such that for all sufficiently large `N`, there exists a set  
> `A ⊆ {1, ..., N}` with
>
> `a + b ∤ a * b`
>
> for all distinct `a, b ∈ A`, and
>
> `|A| ≥ (1/2 + ε) N`.

Do not assume the README, manuscript, comments, theorem names, or author claims are correct. Treat the repository as an untrusted proof artifact and independently determine what has actually been kernel-checked.

The review should distinguish carefully between:

1. the mathematical statement encoded in Lean;
2. the theorem actually proved by Lean;
3. the logical trust boundary of that theorem;
4. reproducibility of the build;
5. agreement between the Lean theorem and Erdős Problem 327;
6. agreement between the Lean development and the accompanying manuscript;
7. any remaining reasons not to regard the result as a completed proof.

---

## Primary deliverable

Produce a report named:

`AUDIT_REPORT.md`

The report must begin with exactly one of these conclusions:

- `VERDICT: VERIFIED`
- `VERDICT: VERIFIED WITH CAVEATS`
- `VERDICT: NOT VERIFIED`
- `VERDICT: REFUTED`

Do not use `VERIFIED` merely because `lake build` succeeds.

A `VERIFIED` verdict should require, at minimum:

- the final theorem exactly implies the claimed `1/2 + ε` result;
- the relevant source files compile from a fresh checkout;
- the final theorem has no `sorryAx`, project-local axioms, or equivalent unchecked assumptions;
- no load-bearing theorem is introduced through an unsafe or opaque shortcut that escapes kernel checking;
- all dependencies used by the final proof are included in the axiom audit;
- the pinned dependency graph is reproducible;
- no mismatch is found between the formal definition and the original Erdős problem.

---

# Audit tasks

## 1. Establish the exact repository state

Record:

- current commit SHA;
- branch;
- Lean version;
- Lake version;
- Mathlib repository and exact revision;
- all direct dependencies.

Do not silently update any dependency.

Preserve the exact pinned environment first.

Include all hashes in `AUDIT_REPORT.md`.

---

## 2. Fresh-build reproduction

From a clean checkout, reproduce the project build.

At minimum run the repository-equivalent of:

```bash
cd lean
lake build Erdos327
```

Record:

- whether dependency resolution succeeds;
- whether the full target succeeds;
- number of jobs/modules if reported;
- warnings;
- any generated files or cached artifacts required for success.

Then perform a genuinely clean rebuild with locally generated build artifacts removed.

Do not rely only on an existing `.lake` cache.

If feasible, perform a second build in a clean temporary directory.

Report exact commands and results.

---

## 3. Verify the formal statement independently

Inspect the definitions of:

- `ConflictOne`
- `OneAdmissible`
- `Erdos327Conclusion`
- `Erdos327FullConclusion`

Write out, in ordinary mathematical notation, exactly what Lean says.

Check specifically:

### Domain

Verify that the set is really contained in:

`{1, ..., N}`

and not, for example:

- `{0, ..., N}`;
- `{1, ..., 2N}`;
- an asymptotically equivalent interval;
- a multiset;
- a set with duplicated elements.

### Conflict condition

Verify that for every distinct `a, b ∈ A`, Lean proves:

`¬ (a + b ∣ a * b)`.

Check that:

- divisibility is over natural numbers;
- the condition is symmetric as required;
- there is no hidden parity restriction;
- there is no omitted exceptional subset;
- no condition is weakened to “almost all pairs”.

### Density conclusion

Verify that Lean proves existence of one fixed:

`ε : ℝ`

with:

`0 < ε`

and then:

`∃ N₀, ∀ N ≥ N₀, ...`.

In particular, rule out weaker statements such as:

- `ε` depending on `N`;
- infinitely many `N` only;
- positive limsup only;
- `1/2 + o(1)` with no fixed positive gain;
- a statement for `{1, ..., 2N}` that is incorrectly translated to density in `{1, ..., N}`.

Explicitly prove or explain the equivalence between the encoded Lean statement and the first question of Erdős Problem 327.

---

## 4. Audit the final theorem

Locate the public theorem:

```lean
Erdos327.Analytic.erdos327Conclusion_unconditional
```

and the theorem from which it is derived.

Determine the complete dependency path from this theorem down to the foundational lemmas.

Confirm that the final theorem has no explicit hypotheses.

Record the exact declaration.

---

## 5. Perform an axiom audit

Run:

```lean
#print axioms Erdos327.Analytic.erdos327Conclusion_unconditional
#print axioms Erdos327.Analytic.erdos327SecondConclusion_unconditional
#print axioms Erdos327.Analytic.erdos327FullConclusion_unconditional
```

Record the exact output.

If the only reported axioms are expected Lean foundations such as:

- `propext`
- `Classical.choice`
- `Quot.sound`

state that explicitly.

If any of the following appear, treat them as potentially fatal until explained:

- `sorryAx`
- project-local axioms;
- custom theorem axioms;
- nonstandard analytic assumptions;
- imported assumptions standing in for the hard number theory.

Do not merely grep the repository for the string `axiom`; rely on `#print axioms` for the transitive theorem dependency, while also doing source-level searches.

---

## 6. Search for proof escape hatches

Search the full project for at least:

```text
sorry
admit
axiom
unsafe
opaque
implemented_by
extern
ofReduceBool
native_decide
```

Also inspect uses of:

- `by native_decide`;
- generated `.olean` files;
- FFI;
- external executable results;
- custom elaborators or tactics capable of synthesizing proof terms;
- code generation;
- environment manipulation.

The purpose is not to forbid these constructs automatically, but to determine whether any load-bearing mathematical claim enters Lean without kernel verification.

For every suspicious construct found, state whether it affects the final theorem.

---

## 7. Audit the Mathlib trust boundary

The project currently pins a Mathlib fork/revision rather than simply tracking an arbitrary current official release.

Investigate the exact pinned Mathlib commit.

Determine:

1. whether the pinned commit exists in the official `leanprover-community/mathlib4` history;
2. if not, exactly what differs from official Mathlib at the nearest common ancestor;
3. whether those differences contain any:
   - axioms;
   - `sorry`;
   - unsafe theorem interfaces;
   - modifications to Lean's logic;
   - modifications to foundational definitions;
   - load-bearing number-theoretic lemmas.

Pay special attention to Mertens-related material.

If the project depends on an unmerged Mathlib PR, inspect the actual formal theorem and its axiom closure rather than treating “not merged upstream” as evidence of incorrectness.

Where possible, independently run `#print axioms` on the load-bearing imported theorems.

Report the dependency trust boundary precisely.

---

## 8. Identify the load-bearing analytic ingredients

Construct a dependency map for the proof.

At minimum inspect the modules corresponding to:

- Mertens estimates;
- rough-number counting;
- centered prime-factor tail bounds;
- three-linear-form / sieve estimates;
- source summation;
- mixed odd-even conflict summation;
- boundary estimates;
- final parameter selection.

For each major ingredient, record:

- theorem name;
- formal statement;
- whether it is proved locally or imported;
- its axiom closure;
- where it is used in the final proof.

Do not review thousands of lines uniformly. Prioritize lemmas where a wrong inequality direction, missing uniformity condition, quantifier-order error, or endpoint error could invalidate the argument.

---

## 9. Check quantifier order and uniformity

This is a high-priority adversarial task.

Search specifically for places where the proof moves between parameters such as:

- `N`;
- a roughness cutoff `L`;
- a dyadic scale;
- a source cutoff;
- prime-factor budgets;
- auxiliary constants.

Check whether a parameter that must be fixed independently of `N` is accidentally allowed to depend on `N`.

In particular verify the final logical pattern is genuinely:

```text
∃ ε > 0,
∃ N₀,
∀ N ≥ N₀,
∃ A, ...
```

and not obtained from something weaker such as:

```text
∀ N,
∃ ε_N > 0,
∃ A, ...
```

or a choice of cutoff depending on `N` that destroys a fixed density gain.

Document this check carefully.

---

## 10. Audit the conversion from edge bounds to density gain

Trace the construction of the admissible set.

Identify:

- the host set;
- which elements are discarded;
- the graph/orientation/conflict structure;
- how many vertices or edges are removed;
- the exact source of the positive density surplus over `1/2`.

Derive independently, from the formal inequalities, why the construction yields:

`1/2 + ε`

for some fixed positive `ε`.

If the repository exposes a concrete margin such as `1/64` at an intermediate stage, determine precisely how that translates to the final `ε`.

If the final theorem is ineffective and does not expose a numerical `ε`, explain why positivity nevertheless follows formally.

Try to extract an explicit lower bound for `ε` if this can be done without changing the mathematics.

---

## 11. Look for vacuity or inconsistent hypotheses

For important intermediate lemmas, check that hypotheses are satisfiable.

Pay special attention to statements of the form:

```lean
h : complicated_condition
⊢ desired_bound
```

that could be trivially true because `complicated_condition` is impossible.

For crucial parameter-existence theorems, verify Lean actually proves existence of parameters satisfying all required inequalities simultaneously.

Check that no contradiction is introduced in a local context and then used via explosion.

---

## 12. Review the known errata

The repository states that version 1 had at least two issues:

- an unjustified dyadic lower bound;
- an anatomy identity that should have been an inequality.

Locate the repaired mathematical statements.

Determine:

- whether the Lean proof ever depended on the erroneous versions;
- whether the formal proof contains the corrected form;
- whether any nearby argument still implicitly uses the stronger false statement.

Do not accept “Lean was unaffected” solely because the README says so.

---

## 13. Compare Lean with the manuscript

Read the main manuscript only after establishing what Lean proves.

Construct a correspondence table:

| Manuscript result | Lean theorem/module | Status |
|---|---|---|
| main construction | ... | formalized / not found |
| source estimate | ... | ... |
| mixed estimate | ... | ... |
| final density theorem | ... | ... |

Identify:

- manuscript lemmas absent from Lean;
- Lean lemmas absent from the manuscript;
- proof strategy divergences;
- imported analytic statements in one version but internally proved in the other.

The Lean proof is allowed to differ from the manuscript, but the report must say so explicitly.

---

## 14. Attempt independent falsification

Before accepting the theorem, actively try to break it.

Examples:

- construct small counterexamples to intermediate combinatorial parametrizations;
- brute-force the conflict-coordinate identities for small integers;
- test parity and gcd reductions;
- verify formulas relating:
  `a + b ∣ ab`
  to the chosen coordinates;
- test boundary cases such as `u = 1`, smallest rough numbers, and transition blocks;
- compare exact finite computations with claimed inequalities when possible.

Add small independent scripts under:

`audit/`

Do not modify the original proof files unless necessary.

Use Python or Lean for finite verification.

---

## 15. Check repository integrity and provenance

Record:

- initial publication date;
- relevant commits;
- whether the Lean files changed after manuscript errata;
- whether the successful CI run corresponds to the exact commit audited.

Check whether GitHub Actions actually builds the current proof files rather than a different target.

Check whether any required file is excluded from version control.

---

# Required output structure

`AUDIT_REPORT.md` should contain:

## 1. Verdict

One of the four required verdict strings.

Then a concise explanation.

## 2. Exact theorem proved

Write the formal claim in mathematical notation.

## 3. Statement equivalence

Explain whether it is exactly Erdős Problem 327's first question.

## 4. Reproduction

Include commit hashes, toolchain versions, commands, and build results.

## 5. Axiom and trust audit

Include exact `#print axioms` results.

## 6. Dependency audit

Explain the Mathlib fork and any unmerged dependencies.

## 7. Proof architecture

Give a dependency diagram or structured outline of the main proof.

## 8. Adversarial checks

List all attempted failure modes and their outcomes.

## 9. Manuscript comparison

Explain whether the paper and Lean proof correspond.

## 10. Issues found

Classify each issue as:

- fatal;
- serious;
- minor;
- expository;
- no issue.

## 11. Remaining uncertainty

State exactly what has not been checked.

## 12. Final assessment

Answer these separately:

```text
Does Lean compile the claimed theorem? YES/NO
Does the theorem match Erdős 327 first question? YES/NO
Does #print axioms reveal nonstandard assumptions? YES/NO
Was the build independently reproduced? YES/NO
Were the key dependency modifications audited? YES/NO
Is there a known logical gap remaining? YES/NO
Would you currently treat the first question as proved? YES/NO
```

Give justification for every `NO` or qualified `YES`.

---

# Review principles

- Be adversarial, not deferential.
- Do not infer correctness from the author's reputation.
- Do not infer incorrectness from AI assistance.
- Do not infer correctness merely from a large Lean codebase.
- Do not infer correctness merely from successful CI.
- Prefer direct inspection and reproducible commands over README claims.
- Treat exact Lean theorem statements and kernel-checked proof terms as primary evidence.
- Separate mathematical correctness from publication status and community acceptance.
- Report uncertainty explicitly.
- Never silently repair a theorem or assumption and then audit the repaired version instead.
- If you find a possible fatal flaw, try to reproduce it with the smallest concrete example or Lean snippet possible.

---

# Optional high-value extension

If the main proof survives the audit, attempt to determine an explicit value or certified lower bound for the `ε` in:

```text
|A| ≥ (1/2 + ε) N.
```

Explain whether the formal development merely proves existential positivity or contains enough explicit constants to extract a numerical value.

This is secondary to correctness and should only be attempted after the core audit is complete.