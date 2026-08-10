VERDICT: VERIFIED WITH CAVEATS

# Independent audit of the claimed Lean proof of Erdős Problem 327

Audit date: 2026-08-09–10 (Asia/Shanghai).  Audited repository: [donalddellapietra/erdos-327-proof](https://github.com/donalddellapietra/erdos-327-proof), commit `a7201442f71af90a8e7b930f993c8eec69f685cf`.  I treated the repository, its prose, and its auxiliary certificates as untrusted.  The evidence below comes from the checked-out source, Lean's transitive axiom reporting, clean builds, an exact diff of the Mathlib fork, and independent finite tests.

**Post-audit effectivization.** A separate audit-only certificate subsequently
fixed `J = 2^(2 * 10^30)` and `L = 8 * 2^J + 1`, and proved the explicit gain
`ε₀ = 1 / (839808 * (J + 4))`; see
[`EFFECTIVE_EPSILON_REPORT.md`](EFFECTIVE_EPSILON_REPORT.md). Its ambient
threshold `N₀` remains existential. Statements below about the absence of a
numeric epsilon describe the original audited commit, not this follow-up
certificate.

## 1. Verdict

The public declaration `Erdos327.Analytic.erdos327Conclusion_unconditional` is an unconditional, kernel-checked proof of the stated fixed-positive-density conclusion.  Its definition has the correct domain, conflict relation, and quantifier order.  I found no `sorryAx`, project-local axiom, inconsistent load-bearing hypothesis, unchecked executable certificate, or proof escape hatch in its transitive trust boundary.  The hard one-variable and three-linear-form estimates are proof-producing Lean declarations rather than imported prose assumptions.

The caveats do not presently amount to a logical gap:

- the project pins a snapshot of an open, unmerged Mertens Mathlib contribution rather than an official Mathlib release;
- this is a new 30,683-line development without mature independent community review, and this audit prioritised load-bearing interfaces rather than manually rereading every tactic step;
- the proof establishes an ineffective existential constant.  Its bookkeeping identifies a symbolic witness `roughDensity L / 128`, but its chosen cutoff `L` is not numerically evaluated;
- one explanation in the revised manuscript is unnecessarily weak and in fact false as an explanation (details in sections 9 and 10), although the Lean identity is stronger and correct.

On the ordinary trust assumptions for Lean 4 and the pinned source dependencies, I would currently treat the first question as proved.

## 2. Exact theorem proved

The public declaration is exactly:

```lean
theorem Erdos327.Analytic.erdos327Conclusion_unconditional :
    Erdos327.Erdos327Conclusion :=
  Erdos327.Analytic.erdos327FullConclusion_unconditional.1
```

It has no explicit or typeclass hypotheses.  The theorem it projects from is:

```lean
theorem Erdos327.Analytic.erdos327FullConclusion_unconditional :
    Erdos327.Erdos327FullConclusion
```

Unfolding the relevant definitions gives the following mathematical statement:

\[
\exists\varepsilon\in\mathbb R,\quad 0<\varepsilon\quad\land\quad
\exists N_0\in\mathbb N,\quad
\forall N\in\mathbb N,\ N_0\le N\Longrightarrow
\exists A\in\operatorname{Finset}(\mathbb N),
\]

\[
A\subseteq\{n\in\mathbb N:1\le n\le N\},\qquad
\forall a,b\in A,\ a\ne b\Longrightarrow (a+b)\nmid ab,
\]

\[
\left(\frac12+\varepsilon\right)N\le |A|.
\]

More literally:

- `upto N = Finset.Icc 1 N`;
- `ConflictOne a b = (a + b ∣ a * b)`, using natural-number addition, multiplication, and divisibility;
- `OneAdmissible A = ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ ConflictOne a b`;
- `Erdos327FullConclusion = Erdos327Conclusion ∧ Erdos327SecondConclusion`.

Thus `A` is a genuine finite set (not a list or multiset), contains no zero or duplicate entries, has no parity restriction in the conclusion, and has no exceptional collection of pairs.  The predicate is stated for every ordered pair of distinct members; the underlying divisibility condition is symmetric, so this is exactly the required unordered-pair condition.

## 3. Statement equivalence

The [Erdős Problems page for Problem 327](https://www.erdosproblems.com/327) asks for a subset of `1,…,N` in which `a+b` does not divide `ab` for distinct members and asks whether one can take substantially more than the odd numbers.  Its source statement is also available in [LaTeX form](https://www.erdosproblems.com/latex/327).  In the central claim under audit, "substantially more" is the standard fixed-proportion assertion `|A| ≥ (1/2+ε)N` for some `ε>0` and all sufficiently large `N`.

The Lean definition is exactly that assertion:

- the interval is `Icc 1 N`, not `0,…,N`, `1,…,2N`, or an asymptotic substitute;
- `Nat` divisibility gives precisely `a+b ∣ ab`;
- the same real `ε` is chosen before `N₀` and before the universal `N`;
- the conclusion holds for every `N≥N₀`, not merely infinitely many `N` or a limsup;
- coercions of `N` and `A.card` to `ℝ` are exact.

The proof does temporarily construct a set in `1,…,2N`.  This is explicitly represented by `EvenEndpointConclusion` and then converted by `erdos327Conclusion_of_evenEndpoint`.  That theorem applies the construction at `⌊X/2⌋`, proves the resulting set lies in `1,…,X`, and absorbs the one-point rounding loss by replacing its gain `η` with `η/4`.  There is no illicit identification of density on `1,…,2N` with density on `1,…,N`.

## 4. Reproduction

### Repository and toolchain

| Item | Exact audited value |
|---|---|
| Repository commit | `a7201442f71af90a8e7b930f993c8eec69f685cf` |
| Branch | `main` |
| Remote | `https://github.com/donalddellapietra/erdos-327-proof.git` |
| Lean toolchain pin | `leanprover/lean4:v4.33.0-rc1` |
| Lean executable | `Lean (version 4.33.0-rc1, arm64-apple-darwin24.6.0, commit 62eed1db4d67327ec8120be05f1a1b0847d74561, Release)` |
| Lake | `Lake version 5.0.0-src+62eed1d (Lean version 4.33.0-rc1)` |
| Host | Apple arm64, Darwin kernel 25.5.0 |
| Direct dependency | `https://github.com/teorth/mathlib4.git` at `da1f94df976c7cd38117281c57d6ee3046c8d104` |

The inherited dependency revisions in the committed `lake-manifest.json` are:

| Package | Revision |
|---|---|
| `plausible` | `b1c4a69a7e247ab7df20460212001673d74f08c0` |
| `LeanSearchClient` | `0498c7c070c143a3bf7379f4d99a2c63bb9d9715` |
| `importGraph` | `18a90119a5d316358fde6c86e0ca24e59212e32c` |
| `proofwidgets` | `b1436dc749e722c9920036b52cdc43b3451d0b69` |
| `aesop` | `57d3325be72a842920813bcb40f96a6f7393c185` |
| `Qq` | `ee41917ae11d38479fb8fb24745f7ca4bf0a784d` |
| `batteries` | `45337c634fbcb2bb22fb45c9847faaa10d4d1b67` |
| `Cli` | `da07ca808b6718cb2aed14dba154e5a08b8f8ecf` |

No dependency was silently updated.  Every package checkout resolved to the committed manifest revision and was clean.

### Build experiments

I performed three complementary source builds; all returned exit status 0.

~~~console
cd /Users/aa/Desktop/erdos-327-proof/lean
/usr/bin/time -p lake build Erdos327
lake clean erdos327
/usr/bin/time -p lake build Erdos327

git clone --no-checkout https://github.com/donalddellapietra/erdos-327-proof.git /tmp/erdos327-audit-a720144.Kmfpyz
git -C /tmp/erdos327-audit-a720144.Kmfpyz checkout --detach a7201442f71af90a8e7b930f993c8eec69f685cf
mkdir -p /tmp/erdos327-audit-a720144.Kmfpyz/lean/.lake
ln -s /Users/aa/Desktop/erdos-327-proof/lean/.lake/packages /tmp/erdos327-audit-a720144.Kmfpyz/lean/.lake/packages
cd /tmp/erdos327-audit-a720144.Kmfpyz/lean
/usr/bin/time -p lake build Erdos327
~~~

1. **End-to-end cache-free build.**  Immediately before the test, `lean/.lake` did not exist and the pinned elan toolchain was not installed.  Running `lake build Erdos327` therefore fetched the exact toolchain and manifest revisions and compiled the dependency graph and project from source.  Lake reported `Build completed successfully (8764 jobs)`; `/usr/bin/time -p` reported `real 6587.01`, `user 35541.87`, `sys 7080.02` seconds (1 h 49 min 47 s elapsed).  No source or manifest changed.
2. **Root-package clean rebuild.**  `lake clean erdos327` removed the 736 files in the 477 MB root build directory while a read-only check confirmed that the Mathlib build cache remained present.  Rebuilding the 92 project modules reported `Build completed successfully (8757 jobs)`; timings were `real 340.66`, `user 440.08`, `sys 375.95` seconds.
3. **Fresh remote checkout.**  I cloned the GitHub remote into a new temporary directory, detached at exactly `a7201442f71af90a8e7b930f993c8eec69f685cf`, verified a clean worktree and manifest SHA-256 `c27e1d56afb5555a556357b2b3256df883e148c6eab025e7c9588d1496a78739`, and confirmed that its root `.lake/build` was absent.  I then symlinked only the already verified `.lake/packages` dependency directory—not any root-project artifact—and ran the same target.  It reported `Build completed successfully (8757 jobs)`; timings were `real 361.85`, `user 464.96`, `sys 426.07` seconds.  The top-level `Erdos327.olean` was newly produced and the checkout remained clean.

The first experiment supplies the no-cache dependency build; the third independently verifies that the exact tracked source, rather than an accidental working-tree state, builds with the pinned dependencies.  The project build emitted 28 linter warnings: 14 unnecessary `<;>` focus warnings, 6 unused simp arguments, 5 unused variables/bindings, one unnecessary `simpa`, one deprecated `push_neg`, and one no-op `push_cast`.  There were no errors and no warning indicating an incomplete proof or trust escape.

The repository's own GitHub Actions run [`30502645598`](https://github.com/donalddellapietra/erdos-327-proof/actions/runs/30502645598) also corresponds exactly to `a7201442f71af90a8e7b930f993c8eec69f685cf`.  The workflow checks out the current commit and invokes `leanprover/lean-action@v1` (resolved there to `38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9`) with `lake-package-directory: lean` and `build: true`; `Erdos327` is the Lake default target.  Its build step reported `Build completed successfully (8757 jobs)`.  It restored a GitHub cache, so I treated that run only as provenance evidence, not as the independent clean-build test.

The tracked repository contains no `.olean`, object file, shared library, generated executable, or symlink.  `.gitignore` excludes `lean/.lake`; the source build regenerates it.  `git fsck --full` and `git diff --check` succeeded.  The 92 tracked Lean files total 30,683 lines; all were already present in the initial proof publication commit.  Hashing their `git ls-tree` records with `git ls-tree -r --full-tree HEAD lean | awk '$4 ~ /\.lean$/' | shasum -a 256` gives `a210f202d1e21290108f575ac6bcfcc530cba1a3fc95e8c3a367872c2b715b7b`.

## 5. Axiom and trust audit

I imported the built top-level library in [`audit/AxiomAudit.lean`](audit/AxiomAudit.lean) and asked Lean for transitive axiom closures, rather than inferring them from a text search.

The probe completed with exit status 0 in 6.54 seconds.  The exact output for the three public conclusions was:

~~~text
Erdos327.Analytic.erdos327Conclusion_unconditional : Erdos327.Erdos327Conclusion
Erdos327.Analytic.erdos327SecondConclusion_unconditional : Erdos327.Erdos327SecondConclusion
Erdos327.Analytic.erdos327FullConclusion_unconditional : Erdos327.Erdos327FullConclusion
'Erdos327.Analytic.erdos327Conclusion_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos327.Analytic.erdos327SecondConclusion_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos327.Analytic.erdos327FullConclusion_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
~~~

Every additional load-bearing declaration queried—35 declarations in all, spanning the forked Mertens results, finite sieve, coordinate reductions, scheduled summations, boundary terms, tail budgets, assembly, and endpoint rescaling—reported exactly the same three-element axiom set.  The complete unabridged transcript is in [`audit/axiom-audit-output.txt`](audit/axiom-audit-output.txt).

The probe includes not only the three public conclusions but representative load-bearing declarations from every analytic layer and all Mertens declarations used from the fork.  This matters because a clean closure for a wrapper alone would already be transitive, but the expanded list also detects mistaken theorem selection and documents the trust boundary.

The project source was separately searched, with token boundaries and case-insensitive variants where appropriate, for:

```text
sorry admit axiom unsafe opaque implemented_by extern
ofReduceBool native_decide run_tac elab macro syntax include_str
```

The sole word-level match was English prose containing "admit" in a doc comment in `SourceFinalSummation.lean`; it is not syntax.  There is no `#eval`, `#reduce`, project `set_option`, FFI, external-result import, environment mutation, custom command/elaborator, or native-code proof shortcut in the original Lean source.  The uses of `noncomputable` and `Classical.choice` construct ordinary kernel-checked terms.  The Python certificates under `controls/` and `paper/supplement/` are not imported by Lean and play no role in the theorem.

The remaining trust base is the normal one: the Lean kernel and compiler/runtime used to check the generated terms, plus the exact source of Lean, Mathlib, and inherited packages listed above.  `propext`, `Classical.choice`, and `Quot.sound` are standard Lean foundational axioms/principles; none asserts any number theory.

## 6. Dependency audit

### Exact Mathlib fork delta

The direct dependency is Terence Tao's `teorth/mathlib4` commit `da1f94df976c7cd38117281c57d6ee3046c8d104` (2026-07-17).  It is fetchable by exact hash and the checked-out package was clean.  For comparison only, I fetched official `master` into a separate remote-tracking ref without checking it out or changing the manifest.  The pin is not an ancestor of the official Mathlib `master` inspected on 2026-08-09 (`639923353ff2a58e9976a254e0d40f4bebae36bc`).  Their nearest common ancestor is:

```text
7d6261f2dc0fd8902626c60e8970bf7c5826afe0
```

The complete fork-side diff from that common ancestor is five files, 1,495 insertions and 8 deletions:

| File | Delta | Audit result |
|---|---:|---|
| `Mathlib.lean` | +1 | imports the new Mertens module |
| `Analysis/SpecialFunctions/Gamma/Deriv.lean` | +75/−7 | analytic derivative lemmas; no foundational change or escape hatch |
| `NumberTheory/Harmonic/GammaDeriv.lean` | +11/−1 | supporting analytic lemmas; no foundational change or escape hatch |
| `NumberTheory/Mertens.lean` | +1,378 | load-bearing new proof-producing Mertens results |
| `NumberTheory/SumPrimeReciprocals.lean` | +30 | supporting prime-reciprocal estimates |

I inspected this exact diff, not the present branch tip.  It contains no `axiom`, `sorry`, unsafe theorem interface, native decision shortcut, logic modification, or foundational-definition modification.  `git diff --check` was clean.  The load-bearing additions are ordinary theorem proofs whose axiom closures are included in section 5.

The work corresponds to the still-open official Mathlib PR [#41394, `feat(NumberTheory/Mertens): the Mertens theorems`](https://github.com/leanprover-community/mathlib4/pull/41394).  The PR had advanced to a later head (`a4221cb335eff1c78bc873d60b1291abf605f873`) and had green CI but no recorded review decision when inspected.  Being unmerged is a review/reproducibility caveat, not an unchecked premise: the project pins a fetchable earlier source snapshot and Lean checks its terms.

### Load-bearing ingredients

The following table gives the formal content at the level used downstream.  All local rows are proved in this repository; the imported rows are proved in the exact Mathlib fork.  The axiom column refers to the recorded section-5 probe.

| Ingredient | Declaration/module | Formal content and downstream use | Origin / axiom closure |
|---|---|---|---|
| Mertens reciprocal sum | `Mertens.sum_prime_inv_sub_sub_bound_nat` | explicit error bound for the prime reciprocal sum; feeds the local Mertens envelopes and Euler products | pinned fork / standard foundations only |
| Mertens product identity | `Mertens.prod_prime_one_minus_inv_eq_nat` | identifies the finite prime product with `exp(-γ+E₃(N))/log N` | pinned fork / standard foundations only |
| Mertens error | `Mertens.E₃_bound` | explicit bound on `E₃`; gives `mertensLowerConstant/log L ≤ roughDensity L` | pinned fork / standard foundations only |
| Rough-number count | `roughSourceInterval_card_lower`, `RoughCount.lean` | if `4D(L)≤N`, then `N/4 · φ(D)/D ≤ #([N/2,N]∩L‑rough)` | local / standard foundations only |
| One-variable mean value | `factorWeight_partialSum_le_eulerProduct_uniform`, `WeightedMangoldtUniform.lean` | uniform finite Euler-product Halberstam–Richert bound for admissible local weights | local / standard foundations only |
| Rough residual moment | `roughResidualSubinterval_le_mertens`, `ResidualMeanBridge.lean` | explicit Mertens bound for an `L`-rough weighted moment on every positive subinterval | local / standard foundations only |
| Centered tails | `card_irregularRoughSource_le_explicit`, `CenteredTailBounds.lean` | bounds irregular rough-source vertices by `C(A,z) N roughDensity(L) z^{-K}`; analogous unrestricted odd-host bound is in the same module | local / standard foundations only |
| Finite sieve core | `finiteWeightBoxSum_le_primeInvSum_add_truncated_boundary`, `WeightedLinearSieveBoundarySharp.lean` | CRT/Bonferroni box sum ≤ Euler main term + factorial tail + explicit polynomial boundary | local / standard foundations only |
| Three-linear-form boxes | `source_threeFormBoxSum_le_sharp`, `mixed_threeFormBoxSum_le_sharp`, `ThreeFormBoxSharp.lean` | specializes the finite sieve to `u,v,u+v` and `u,w,2u+w`, with local bad-residue count `3p−2` and explicit errors | local / standard foundations only |
| Source coordinates | `card_rankBad_le_sourceCoordinateSet`, `CoordinateCounting.lean` | injects each score-oriented bad source vertex into a reconstructing coordinate triple | local / standard foundations only |
| Mixed coordinates | `card_mixedEdges_le_mixedMainCoordinateSet_add_one`, `MixedMainReduction.lean` | injects main mixed edges into reconstructing triples and proves at most one exceptional endpoint edge | local / standard foundations only |
| Scheduled source sum | `card_rankBad_le_exactRefinedScheduled_sum`, `SourceScheduledSummation.lean` | sums dyadic source-coordinate blocks using the explicit sieve schedule | local / standard foundations only |
| Scheduled mixed sum | `card_mixedEdges_le_refinedScheduled_sum_add_one`, `MixedSmallBlocks.lean` | sums mixed-coordinate blocks and retains the single exceptional-edge cost | local / standard foundations only |
| Source boundary/final | boundary theorems in `SourceBoundarySummation.lean`; `eventually_exists_forall_card_rankBad_le_roughDensity` | bulk, terminal, transition, small residual, and error tails total at most `N roughDensity(L)/16` along the coupled cutoffs | local / standard foundations only |
| Mixed boundary/final | `eventually_sum_mixedCanonicalBoundaryBlock_le_roughDensity`; `eventually_exists_forall_sum_mixedRefined_add_one_le_roughDensity` | five scheduled pieces, each allocated `1/512`, imply the mixed `1/64` budget for all large `N` at each large fixed `L` | local / standard foundations only |
| Parameter selection | `exists_sourceTailBudget`, `eventually_oddBudget_meets_tail`, `tendsto_sourceCoupledCutoff_atTop` | selects a fixed source budget, shows `oddBudget(L)=3.3912 log log L` beats its tail, and sends `L=8·2^J+1` to infinity | local / standard foundations only |
| Final reduction | `erdos327FullConclusion_of_canonical_estimates`, `CanonicalReduction.lean` | four explicit deletion bounds imply both Erdős 327 conclusions | local / standard foundations only |

The project does not import a general Tenenbaum or de la Bretèche–Tenenbaum theorem as an assumption.  It proves the finite special cases it needs through local multiplicative mean-value, exact `ZMod` root counts, CRT periodicity, finite Bonferroni truncation, and explicit factorial/polynomial error estimates.

## 7. Proof architecture

The dependency spine is:

```text
erdos327Conclusion_unconditional
└─ erdos327FullConclusion_unconditional
   ├─ choose fixed source budget K
   ├─ choose one sufficiently late J
   │  └─ fix L = sourceCoupledCutoff J = 8·2^J + 1
   ├─ intersect source, mixed, and odd-tail eventual statements
   ├─ erdos327FullConclusion_of_canonical_estimates
   │  ├─ rough count / irregular-source tail
   │  ├─ centered source conflicts → source coordinates → sieve schedule
   │  ├─ irregular odd-host tail
   │  └─ mixed conflicts → mixed coordinates → sieve schedule
   └─ analytic assembly → finite assembly → endpoint rescaling
```

At the bottom, the final finite set is

\[
(O\setminus\operatorname{mixedBad}(O,B))\ \cup\ \{2b:b\in B\},
\]

where `O` is odd and `B` is a score-filtered two-admissible source.  Odd–odd pairs never conflict; doubling turns `ConflictOne (2a) (2b)` into `ConflictTwo a b`; all odd–even conflicts are deleted; and the odd and doubled layers are disjoint.  `card_assembledSet` proves exact cardinality accounting.

For the four canonical estimates, write `r = roughDensity L > 0` and let the assembly parameter be `ρ=r/2`.

1. The raw rough source has at least `Nr/4` vertices.
2. Irregular-source deletion is at most `Nr/8`, leaving at least `Nr/8 = Nρ/4`.
3. Rank deletion is at most `Nr/16 = Nρ/8`, leaving the doubled source `B` with at least `Nr/16 = Nρ/8` vertices.
4. Odd-host and mixed deletions are each at most `Nr/64 = Nρ/32`.
5. Exact assembly therefore has at least
   `N - Nρ/32 - Nρ/32 + Nρ/8 = (1+ρ/16)N`
   members in `1,…,2N`.
6. `erdos327Conclusion_of_evenEndpoint` converts `η=ρ/16=r/32` into the all-endpoint witness `ε=η/4=r/128>0`.

This is an explicit symbolic lower bound after the eventual cutoff is selected.  The local Mertens theorem further certifies
`ε = roughDensity(L)/128 ≥ mertensLowerConstant/(128 log L) > 0`.
A numeric `ε` is not extracted because several `Filter.Eventually` and classical-existence steps choose `L` and later thresholds without computation.  That affects effectiveness, not positivity or quantifier order.

### Quantifier and uniformity check

The most dangerous possible error was letting the density cutoff depend on `N`.  The final proof does the opposite:

1. `exists_sourceTailBudget` chooses `K` independently of both `L` and `N`.
2. Source estimates hold eventually in `J`, while mixed and odd-tail estimates hold eventually in `L`.
3. `tendsto_sourceCoupledCutoff_atTop` pulls the latter two predicates back along `L(J)=8·2^J+1`.
4. The proof intersects all three eventual predicates and chooses one fixed `J`, hence one fixed `L` and one fixed `ε=r(L)/128`.
5. Only then does it define a single threshold
   `N₀ = max Ns (max Nm (max L (4 * roughPrimeModulus L)))`
   and prove the four bounds for every `N≥N₀`.

The sieve schedule itself uses `R=128h²` and a cutoff of the form `2^⌊j/(16R)⌋`; eventual dominance is proved from explicit logarithmic, factorial, and polynomial boundary estimates.  The source main ranges consume `1/64+1/64+1/64+1/128`, with a further `1/128` error allowance, totalling `1/16`.  The five mixed pieces consume `5/512 < 1/64`; the fixed `+1` exceptional edge is absorbed by an explicit positive-density threshold.  I found no mutually inconsistent parameter hypotheses or use of explosion.

## 8. Adversarial checks

### Source-level and repository checks

- Unfolded every final definition and checked interval endpoints, types, coercions, pair quantifiers, and order of existential/universal binders.
- Followed the complete public-theorem projection into the full unconditional parameter selection.
- Searched the original project source for proof escape hatches and inspected all generated/tracked artifact classes; none is load-bearing.
- Inspected the exact five-file Mathlib fork delta and axiom-probed the Mertens APIs actually used.
- Checked all direct/inherited package hashes, package `HEAD`s, manifest immutability, Git object integrity, current branch/remote, and build workflow target.
- Traced the finite injections in `CoordinateCounting.lean` and `MixedMainReduction.lean`; equality of chosen triples reconstructs the original endpoint(s), and the exceptional mixed range has cardinality at most one.
- Checked signs and directions in rough counting, source/host deletion budgets, rank loss, mixed loss, exact union cardinality, and endpoint rounding.
- Checked transition blocks: source blocks with `8X<L` and mixed blocks with `16X<L` are proved empty; the remaining below-cutoff blocks use all-cutoff analytic fallbacks rather than assuming the erroneous lower bound.

### Independent finite falsification

[`audit/finite_checks.py`](audit/finite_checks.py) uses only Python's standard library and does not call project code.  It was run as:

```text
$ /usr/bin/time -p python3 audit/finite_checks.py
ok: recovered mixed conflicts: 90
ok: generated coprime triples: 18864
ok: three-form residue pairs: 3354
ok: exact mixed anatomy instances: 144090
ok: Sawin conflict pairs: 844
ok: rough cutoff representations: 7847
ok: rough source density bounds: 252
ok: mixed boundary instances: 1335
ok: exceptional endpoint pairs: 250
real 4.03
user 3.98
sys 0.03
```

These tests attempted to falsify:

- odd–odd nonconflict, doubling equivalence, and cancellation of the mixed odd/even relation;
- recovery, generation, coprimality, and uniqueness of mixed coordinates;
- the `3p−2` local root count for both three-form systems;
- the exact localized mixed anatomy identity, including `u=1` and small rough cutoffs;
- the Sawin/source divisibility coordinate relation;
- the rough cutoff endpoint claim and periodic rough-source lower bound;
- endpoint inequalities `w≤6u` and `2u+w≤8u` in the mixed range;
- the claim that the canonical endpoint intervals admit at most one pair with `a>4b`.

All tests passed.  They are sanity/falsification evidence, not a replacement for the general Lean proof.  The author's two Python certificates also ran successfully, but because they are author-supplied and are outside Lean's theorem dependency, I did not count them as independent trust evidence.

## 9. Manuscript comparison

The Lean proof implements the manuscript's architecture but is not a line-by-line transcription.  In particular, where the paper cites general black-box mean-value and multivariable upper-bound results, Lean proves specialized finite versions with explicit schedules and errors.

| Manuscript result | Lean theorem/module | Status |
|---|---|---|
| Main first-question construction | `assembledSet`, `oneAdmissible_assembledSet`, `assembly_density_bound` | Formalized |
| Even-endpoint to original interval | `erdos327Conclusion_of_evenEndpoint` | Formalized, including floor loss |
| One-variable mean value | `MeanValue`, `WeightedMangoldt`, `WeightedMangoldtUniform`, `ResidualMean` | Specialized sufficient version proved locally |
| Centered factor-count tail | `CenteredTail`, `CenteredTailBounds` | Formalized with explicit constants |
| Rough source density | `RoughCount`, local `Mertens` wrapper | Formalized |
| Source estimate | source coordinate, scheduled main/terminal/boundary/error, and `SourceFinalSummation` modules | Sufficient scheduled theorem formalized; not the paper's raw big-O statement literally |
| Sawin/source conclusion | `erdos327SecondConclusion_of_analytic_source`; second unconditional theorem | Formalized |
| Mixed coordinate parametrization | `Coordinates`, `MixedMainReduction`, `MixedIndicator` | Formalized |
| Mixed estimate | mixed scheduled main/terminal/boundary/final modules | Sufficient budget theorem formalized; not the raw big-O statement literally |
| Parameter window | `Parameters`, `TailInstantiation`, `AsymptoticParameterSelection`, `SourceErrorCoupling` | Formalized with the coupled cutoff |
| Final theorem | `CanonicalReduction`, `Unconditional` | Formalized and unconditional |

Lean-only infrastructure includes exact finite CRT/Bonferroni bounds, polynomial truncated boundaries, all-cutoff transition handling, and the coupled source schedule.  Manuscript-only presentation includes broader black-box propositions and asymptotic `O`-notation not exposed under identical theorem names in Lean.

### The two published errata

1. **Unjustified dyadic lower bound.**  The Lean proof never assumes every block starts above `L`.  `SourceSmallBlocks.lean` proves a source block empty when `8X<L` and gives an all-cutoff fallback for `X<L≤8X`; `MixedSmallBlocks.lean` proves the analogous empty range `16X<L` and handles the transition.  Thus the manuscript's version-1 omission is not in Lean.
2. **Anatomy identity.**  Lean proves `mixed_odd_factorCount_eq` using the localized `primeFactorCountBetween` function, multiplicativity, and roughness of `2u+w`; nearby bounds use precisely this identity.  No replacement by a stronger unjustified full `Ω_{≥L}(w)` statement was found.

There is also a manuscript-only expository problem in the attempted correction: it says `w` may have one prime factor exceeding `x=2u+w`.  Since the coordinate box has `u≥1`, one has `w<x` identically, so no prime factor of positive `w` can exceed `x`.  Consequently the exact identity used by Lean is sound and the manuscript's weaker `≥ … -1` remains true, but the sentence explaining its loss is false and the extra paper factor is unnecessary.  The supplied Python certificate tests only the looser implication from `w≤4x`, so it does not notice this simplification.

Git history confirms that commit `c9aa14f2a3445ee528ed1bc01cc4e4e9a284171c` changed the manuscript, controls, PDF, and certificate for the errata but no Lean source.  Every tracked Lean file last changed in the initial proof commit, which independently supports (but does not by itself prove) the claim that the formal proof was unaffected.

## 10. Issues found

| Classification | Finding | Effect on theorem |
|---|---|---|
| Fatal | None found | None |
| Serious | None found | None |
| Minor / caveat | Direct Mathlib dependency is an exact snapshot of an open, unmerged Mertens PR rather than a release | Increases review and long-term-fetchability risk; exact source compiled and axiom audit found no added assumption |
| Minor / caveat | No concrete numeral for `ε` or `N₀` is extracted | The existential theorem and positivity remain valid; symbolic witness is `roughDensity L/128` |
| Expository | Revised manuscript says `w` may contain one prime factor above `x=2u+w`, although `w<x` | Paper bound is merely weaker; Lean proves the correct exact localized identity |
| No issue | Version-1 dyadic lower-bound gap | Lean has explicit empty/transition-block proofs and did not depend on it |
| No issue | Version-1 anatomy equality concern | Lean's localized equality is valid and was independently tested on 144,090 small instances |
| No issue | Use of classical/noncomputable definitions | Produces kernel-checked proof terms; reflected only in standard `Classical.choice` trust |
| No issue | CI used a dependency cache | Independent cache-free/clean builds, not CI alone, are the reproduction basis |

## 11. Remaining uncertainty

- This was a targeted adversarial audit of all load-bearing interfaces, parameter choices, exact dependency changes, and representative proof internals, not a handwritten rederivation of every tactic step in 30,683 lines.  Kernel checking covers those steps, but a later expert review could still find that a correctly proved intermediate statement is mathematically weaker than intended at some interface I did not prioritize.
- I did not independently formalize a second proof of the analytic estimates.  The strongest evidence is the checked term closure, exact fork audit, manual interface inspection, and finite falsification.
- The Lean compiler/kernel and the pinned core/library sources remain part of the trusted computing base; this audit did not bootstrap or formally verify Lean itself.
- The unmerged Mertens contribution lacks the social assurance of an accepted Mathlib review, although its exact source and theorem closure were checked here.
- The existing proof does not make its eventual cutoff effective enough to print a usable numerical `ε` or `N₀`; extracting one would require constructive threshold bookkeeping or an additional formal computation.

None of these is a known logical gap in the claimed theorem.

## 12. Final assessment

```text
Does Lean compile the claimed theorem? YES
Does the theorem match Erdős 327 first question? YES
Does #print axioms reveal nonstandard assumptions? NO
Was the build independently reproduced? YES
Were the key dependency modifications audited? YES
Is there a known logical gap remaining? NO
Would you currently treat the first question as proved? YES
```

The final `YES` is qualified only by the ordinary Lean trusted-computing-base assumption and the review-status caveats above.  The dependency answer is `YES` for the exact five-file fork delta and all load-bearing Mertens declarations, not a claim to have audited every theorem in all of Mathlib.  The build and axiom answers refer to the exact pinned commit and dependency graph recorded in sections 4–6.

## Provenance appendix

The GitHub repository was created on 2026-07-29; the initial proof publication commit is `5c6db2f53668edd621ec75d48821113345565ede` at 2026-07-29 17:02:05−04:00.  The relevant history is:

| Commit | Time (author offset) | Subject | Lean effect |
|---|---|---|---|
| `5c6db2f53668edd621ec75d48821113345565ede` | 2026-07-29 17:02:05−04:00 | `publish Erdos 327 proof claim` | Adds all audited Lean proof files |
| `bfb40f6cf0ac97e3c8f71747579ff3eecc165115` | 2026-07-29 18:07:06−04:00 | module inventory correction | No Lean source change |
| `c9aa14f2a3445ee528ed1bc01cc4e4e9a284171c` | 2026-07-29 20:22:59−04:00 | manuscript errata | No Lean source change |
| `a7201442f71af90a8e7b930f993c8eec69f685cf` | 2026-07-29 20:25:47−04:00 | merge companion manuscript | No Lean source change |

The successful CI run cited in section 4 is a push run on the final row's exact SHA.  No required Lean source is excluded from version control; the only deliberately excluded required-to-regenerate directory is `.lake`, which contains fetched dependencies and build products described in the reproduction section.
