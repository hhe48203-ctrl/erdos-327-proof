import Erdos327

/-!
Reproducible axiom-closure probe for the independent audit.

Run from `lean/` with:

    lake env lean ../audit/AxiomAudit.lean
-/

-- Public conclusions.
#check Erdos327.Analytic.erdos327Conclusion_unconditional
#check Erdos327.Analytic.erdos327SecondConclusion_unconditional
#check Erdos327.Analytic.erdos327FullConclusion_unconditional
#print axioms Erdos327.Analytic.erdos327Conclusion_unconditional
#print axioms Erdos327.Analytic.erdos327SecondConclusion_unconditional
#print axioms Erdos327.Analytic.erdos327FullConclusion_unconditional

-- Load-bearing results imported from the pinned Mathlib fork.
#print axioms Mertens.sum_prime_inv_sub_isBigO_nat
#print axioms Mertens.sum_prime_inv_sub_sub_bound_nat
#print axioms Mertens.prod_prime_one_minus_inv_eq_nat
#print axioms Mertens.E₃_bound
#print axioms Mertens.prod_prime_one_minus_inv_asymp_nat

-- Representative local results from each major analytic layer.
#print axioms Erdos327.Analytic.mertensLowerConstant_div_log_le_primeProduct
#print axioms Erdos327.Analytic.mertensLowerConstant_div_log_le_roughDensity
#print axioms Erdos327.Analytic.roughSourceInterval_card_lower
#print axioms Erdos327.Analytic.factorWeight_partialSum_le_eulerProduct_uniform
#print axioms Erdos327.Analytic.roughResidualSubinterval_le_mertens
#print axioms Erdos327.Analytic.card_irregularRoughSource_le_explicit
#print axioms Erdos327.Analytic.finiteWeightBoxSum_le_primeInvSum_add_truncated_boundary
#print axioms Erdos327.Analytic.source_threeFormBoxSum_le_sharp
#print axioms Erdos327.Analytic.mixed_threeFormBoxSum_le_sharp
#print axioms Erdos327.Analytic.card_rankBad_le_sourceCoordinateSet
#print axioms Erdos327.Analytic.card_mixedEdges_le_mixedMainCoordinateSet_add_one
#print axioms Erdos327.Analytic.mixed_odd_factorCount_eq
#print axioms Erdos327.Analytic.card_rankBad_le_exactRefinedScheduled_sum
#print axioms Erdos327.Analytic.card_mixedEdges_le_refinedScheduled_sum_add_one
#print axioms Erdos327.Analytic.source_initialBlock_empty_or_analytic
#print axioms Erdos327.Analytic.mixedCoordinateBoxBlock_eq_empty_of_sixteen_mul_lt
#print axioms Erdos327.Analytic.eventually_sum_sourceEulerMain_transition_le_roughDensity
#print axioms Erdos327.Analytic.eventually_sum_sourceEulerMain_smallResidual_le
#print axioms Erdos327.Analytic.eventually_sum_mixedCanonicalBoundaryBlock_le_roughDensity
#print axioms Erdos327.Analytic.eventually_exists_forall_card_rankBad_le_roughDensity
#print axioms Erdos327.Analytic.eventually_exists_forall_sum_mixedRefined_add_one_le_roughDensity
#print axioms Erdos327.Analytic.exists_sourceTailBudget
#print axioms Erdos327.Analytic.eventually_oddBudget_meets_tail
#print axioms Erdos327.Analytic.tendsto_sourceCoupledCutoff_atTop

-- Combinatorial assembly and the final reduction.
#print axioms Erdos327.assembly_density_bound
#print axioms Erdos327.erdos327Conclusion_of_evenEndpoint
#print axioms Erdos327.erdos327FullConclusion_of_canonical_estimates
