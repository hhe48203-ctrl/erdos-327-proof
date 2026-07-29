# Lean formalization status

Date: 2026-07-29

- Lean: `4.33.0-rc1`
- Mathlib source: `teorth/mathlib4`
- Mathlib revision: `da1f94df976c7cd38117281c57d6ee3046c8d104`
- Root target: `Erdos327`
- Verified root build: 8,757 jobs

## Status

Complete and unconditional.

The development proves:

```lean
Erdos327.Analytic.erdos327FullConclusion_unconditional :
  Erdos327.Erdos327FullConclusion
```

and exposes the two components separately as
`erdos327Conclusion_unconditional` and
`erdos327SecondConclusion_unconditional`.

`#print axioms` reports only:

```text
propext
Classical.choice
Quot.sound
```

There are no project-local axioms, placeholders, opaque proof interfaces, or
unsafe declarations.

## Proof-layer inventory

| Layer | Representative modules |
|---|---|
| Problem statements and finite construction | `Defs`, `Basic`, `Assembly`, `AnalyticAssembly`, `CanonicalReduction` |
| Conflict coordinates | `Coordinates`, `SourceCoordinates`, `MixedMainReduction` |
| Centered anatomy tails | `CenteredTailBounds`, `TailInstantiation`, `Regularity` |
| Mertens and rough density | `MertensElementary`, `WeightedMangoldtUniform`, `RoughCount` |
| Specialized local three-form weights | `WeightedLinearSieveLocal`, `ThreeFormWeightBridge` |
| Finite scheduled upper sieve | `WeightedLinearSieve`, `SieveSchedule`, `SieveScheduleErrors`, `ScheduledProductBounds` |
| Source summation | `SourceScheduledSummation`, `SourceMainSummation`, `SourceTerminalSummation`, `SourceBoundarySummation`, `SourceErrorCoupling`, `SourceFinalSummation` |
| Mixed summation | `MixedScheduledSummation`, `MixedMainSummation`, `MixedTerminalSummation`, `MixedBoundarySummation`, `MixedBudgetSummation`, `MixedFinalSummation` |
| Common cutoff and final theorem | `Unconditional` |

## Analytic closure

The earlier audit identified three missing library-level ingredients:
Mertens' product estimate, a centered nonnegative multiplicative mean-value
bound, and a three-linear-form upper bound. The final development closes
these gaps inside the project in the exact forms required by the proof.

The three-form component is not imported as a black-box axiom. It consists of
an exact local calculation, a finite upper-sieve expansion, explicit
factorial and polynomial truncation errors, and a schedule whose errors
vanish fast enough for the source and mixed dyadic sums.

The final mixed boundary is also explicit. It is partitioned into at most
four transition blocks and at most `L` positive small-residual blocks; the
latter escape every fixed dyadic prefix as `N → ∞`. This closes the last
uniformity gap before the final `1/64` density budget.

## Prior-formalization search

A dated search on 2026-07-29 found no prior public Lean formalization of
Erdős Problem 327 or Sawin's result. Mathlib contains elementary
`ArithmeticFunction.cardFactors` infrastructure; an open Mertens PR and
one-dimensional Selberg-sieve developments provide nearby prerequisites.
No proved public Lean implementation of the specialized centered
Hardy--Ramanujan tail or the required three-linear-form estimate was found.
This is a search report, not a categorical priority claim.

## Reproduction

```bash
cd lean
lake build Erdos327
```
