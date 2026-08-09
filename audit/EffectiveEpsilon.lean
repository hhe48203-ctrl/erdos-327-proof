import Erdos327

/-!
Audit-only effectivization lemmas for the proof of Erdős Problem 327.

Run from `lean/` with:

    lake env lean ../audit/EffectiveEpsilon.lean
-/

namespace Erdos327.EffectiveAudit

open Filter Finset Real Topology

open Erdos327.Analytic

open scoped BigOperators

noncomputable section

namespace Analytic

/-- A deliberately generous explicit source-tail intercept. -/
def explicitSourceBudget : ℝ := 400000000

/-!
## One explicit common dyadic start

The exponent is deliberately divisible by `20000`.  This keeps every
later `1 / 10000` power comparison exact while leaving a very large
margin for the fixed constants in the source and mixed estimates.
-/

def explicitScale : ℕ := 10 ^ 26

def explicitQuarterExponent : ℕ := 5000 * explicitScale

def explicitLogExponent : ℕ := 4 * explicitQuarterExponent

def explicitJ : ℕ := 2 ^ explicitLogExponent

def explicitTinyRootExponent : ℕ := 2 * 10 ^ 25

private theorem explicitLogExponent_eq_tinyRoot :
    explicitLogExponent = 100000 * explicitTinyRootExponent := by
  norm_num [explicitLogExponent, explicitQuarterExponent, explicitScale,
    explicitTinyRootExponent]

private theorem explicitJ_cast_eq_pow :
    (explicitJ : ℝ) = (2 : ℝ) ^ explicitLogExponent := by
  unfold explicitJ
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]

private theorem log_explicitJ_eq :
    log (explicitJ : ℝ) = (explicitLogExponent : ℝ) * log 2 := by
  rw [explicitJ_cast_eq_pow, Real.log_pow]

private theorem explicitQuarterExponent_ge_768 :
    768 ≤ explicitQuarterExponent := by
  norm_num [explicitQuarterExponent, explicitScale]

private theorem explicit_linear_le_pow_half :
    384 * explicitLogExponent ≤
      2 ^ (2 * explicitQuarterExponent) := by
  have hpow :=
    Nat.two_mul_sq_add_one_le_two_pow_two_mul explicitQuarterExponent
  have hlinear :
      384 * (4 * explicitQuarterExponent) ≤
        2 * explicitQuarterExponent ^ 2 + 1 := by
    nlinarith [explicitQuarterExponent_ge_768]
  simpa [explicitLogExponent] using hlinear.trans hpow

private theorem explicitJ_log_div_sqrt_le :
    log (explicitJ : ℝ) / √(explicitJ : ℝ) ≤ (1 / 384 : ℝ) := by
  have hJnat :
      explicitJ = (2 ^ (2 * explicitQuarterExponent)) ^ 2 := by
    unfold explicitJ explicitLogExponent
    rw [← pow_mul]
    congr 1
  have hJcast :
      (explicitJ : ℝ) =
        ((2 : ℝ) ^ (2 * explicitQuarterExponent)) ^ 2 := by
    exact_mod_cast hJnat
  have hsqrt :
      √(explicitJ : ℝ) =
        (2 : ℝ) ^ (2 * explicitQuarterExponent) := by
    rw [hJcast, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity :
        0 ≤ (2 : ℝ) ^ (2 * explicitQuarterExponent))]
  have hlog :
      log (explicitJ : ℝ) =
        (explicitLogExponent : ℝ) * log 2 := by
    rw [hJcast, Real.log_pow, Real.log_pow]
    push_cast
    unfold explicitLogExponent
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hlog2 : log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_two_lt_d9]
  have hlinear :
      (384 : ℝ) * explicitLogExponent ≤
        (2 : ℝ) ^ (2 * explicitQuarterExponent) := by
    exact_mod_cast explicit_linear_le_pow_half
  have hden :
      0 < (2 : ℝ) ^ (2 * explicitQuarterExponent) := by positivity
  rw [hlog, hsqrt]
  calc
    (explicitLogExponent : ℝ) * log 2 /
          (2 : ℝ) ^ (2 * explicitQuarterExponent) ≤
        (explicitLogExponent : ℝ) /
          (2 : ℝ) ^ (2 * explicitQuarterExponent) := by
      exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_right (Nat.cast_nonneg _) hlog2) hden.le
    _ ≤ (1 / 384 : ℝ) := by
      apply (div_le_iff₀ hden).2
      nlinarith only [hlinear]

private theorem explicitJ_ge_exp_two :
    exp (2 : ℝ) ≤ (explicitJ : ℝ) := by
  have hexp : exp (2 : ℝ) < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 1, Real.exp_one_lt_three]
  have hfour : 4 ≤ explicitLogExponent := by
    norm_num [explicitLogExponent, explicitQuarterExponent, explicitScale]
  have hJ : 16 ≤ explicitJ := by
    calc
      16 = 2 ^ (4 : ℕ) := by norm_num
      _ ≤ 2 ^ explicitLogExponent :=
        Nat.pow_le_pow_right (by norm_num) hfour
      _ = explicitJ := by rfl
  have hJ9 : 9 ≤ explicitJ := (by norm_num : 9 ≤ 16).trans hJ
  exact hexp.le.trans (by exact_mod_cast hJ9)

private theorem explicitJ_ge_sixty_four : 64 ≤ explicitJ := by
  have hsix : 6 ≤ explicitLogExponent := by
    norm_num [explicitLogExponent, explicitQuarterExponent, explicitScale]
  calc
    64 = 2 ^ (6 : ℕ) := by norm_num
    _ ≤ 2 ^ explicitLogExponent :=
      Nat.pow_le_pow_right (by norm_num) hsix
    _ = explicitJ := by rfl

private theorem explicit_log_add_one_le_div
    {j : ℕ} (hj : explicitJ ≤ j) :
    log (((j + 1 : ℕ) : ℝ)) ≤ (j : ℝ) / 384 := by
  let x : ℝ := (j + 1 : ℕ)
  have hj2 : 2 ≤ j :=
    (by norm_num : 2 ≤ 64).trans (explicitJ_ge_sixty_four.trans hj)
  have hxJ : (explicitJ : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hj.trans (Nat.le_succ j)
  have hxExp : exp (2 : ℝ) ≤ x := explicitJ_ge_exp_two.trans hxJ
  have hratio : log x / √x ≤ (1 / 384 : ℝ) :=
    (Real.log_div_sqrt_antitoneOn
      explicitJ_ge_exp_two hxExp hxJ).trans explicitJ_log_div_sqrt_le
  have hxpos : 0 < x := (Real.exp_pos 2).trans_le hxExp
  have hsqrtpos : 0 < √x := Real.sqrt_pos.2 hxpos
  have hsqrt : √x ≤ (j : ℝ) := by
    apply (Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ j)).2
    dsimp [x]
    push_cast
    have hj2r : (2 : ℝ) ≤ j := by exact_mod_cast hj2
    nlinarith only [hj2r]
  have hlog : log x ≤ (1 / 384 : ℝ) * √x :=
    (div_le_iff₀ hsqrtpos).mp hratio
  calc
    log (((j + 1 : ℕ) : ℝ)) = log x := by rfl
    _ ≤ (1 / 384 : ℝ) * √x := hlog
    _ ≤ (1 / 384 : ℝ) * (j : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ = (j : ℝ) / 384 := by ring

private theorem explicitLogExponent_le_tinyRootPower :
    (explicitLogExponent : ℝ) ≤
      (2 : ℝ) ^ explicitTinyRootExponent := by
  have hsmall : (explicitLogExponent : ℝ) ≤ (2 : ℝ) ^ (128 : ℕ) := by
    norm_num [explicitLogExponent, explicitQuarterExponent, explicitScale]
  have hroot : 128 ≤ explicitTinyRootExponent := by
    norm_num [explicitTinyRootExponent]
  exact hsmall.trans
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hroot)

private theorem explicitJ_tiny_rpow_eq :
    (explicitJ : ℝ) ^ (1 / 100000 : ℝ) =
      (2 : ℝ) ^ explicitTinyRootExponent := by
  have hJpos : (0 : ℝ) < explicitJ := by
    exact_mod_cast (show 0 < explicitJ by unfold explicitJ; positivity)
  have hrelation :
      (explicitLogExponent : ℝ) =
        100000 * (explicitTinyRootExponent : ℝ) := by
    exact_mod_cast explicitLogExponent_eq_tinyRoot
  have hexponent :
      (explicitLogExponent : ℝ) * log 2 * (1 / 100000 : ℝ) =
        (explicitTinyRootExponent : ℝ) * log 2 := by
    calc
      (explicitLogExponent : ℝ) * log 2 * (1 / 100000 : ℝ) =
          ((explicitLogExponent : ℝ) / 100000) * log 2 := by ring
      _ = (explicitTinyRootExponent : ℝ) * log 2 := by
        congr 1
        apply (div_eq_iff (by norm_num : (100000 : ℝ) ≠ 0)).2
        nlinarith only [hrelation]
  rw [Real.rpow_def_of_pos hJpos, log_explicitJ_eq, hexponent]
  calc
    exp ((explicitTinyRootExponent : ℝ) * log 2) =
        exp (log 2) ^ explicitTinyRootExponent := by
      simpa using (Real.exp_nat_mul (log 2) explicitTinyRootExponent)
    _ = (2 : ℝ) ^ explicitTinyRootExponent := by
      rw [Real.exp_log (by norm_num)]

private theorem explicitJ_medium_rpow_eq :
    (explicitJ : ℝ) ^ (1 / 10000 : ℝ) =
      (2 : ℝ) ^ (2 * explicitScale) := by
  have hJpos : (0 : ℝ) < explicitJ := by
    exact_mod_cast (show 0 < explicitJ by unfold explicitJ; positivity)
  have hrelation :
      (explicitLogExponent : ℝ) =
        10000 * ((2 * explicitScale : ℕ) : ℝ) := by
    norm_num [explicitLogExponent, explicitQuarterExponent, explicitScale]
  have hexponent :
      (explicitLogExponent : ℝ) * log 2 * (1 / 10000 : ℝ) =
        ((2 * explicitScale : ℕ) : ℝ) * log 2 := by
    calc
      (explicitLogExponent : ℝ) * log 2 * (1 / 10000 : ℝ) =
          ((explicitLogExponent : ℝ) / 10000) * log 2 := by ring
      _ = ((2 * explicitScale : ℕ) : ℝ) * log 2 := by
        congr 1
        apply (div_eq_iff (by norm_num : (10000 : ℝ) ≠ 0)).2
        nlinarith only [hrelation]
  rw [Real.rpow_def_of_pos hJpos, log_explicitJ_eq, hexponent]
  calc
    exp (((2 * explicitScale : ℕ) : ℝ) * log 2) =
        exp (log 2) ^ (2 * explicitScale) := by
      simpa using (Real.exp_nat_mul (log 2) (2 * explicitScale))
    _ = (2 : ℝ) ^ (2 * explicitScale) := by
      rw [Real.exp_log (by norm_num)]

private theorem explicitJ_small_rpow_eq :
    (explicitJ : ℝ) ^ (1 / 20000 : ℝ) =
      (2 : ℝ) ^ explicitScale := by
  have hJpos : (0 : ℝ) < explicitJ := by
    exact_mod_cast (show 0 < explicitJ by unfold explicitJ; positivity)
  have hrelation :
      (explicitLogExponent : ℝ) =
        20000 * (explicitScale : ℝ) := by
    norm_num [explicitLogExponent, explicitQuarterExponent, explicitScale]
  have hexponent :
      (explicitLogExponent : ℝ) * log 2 * (1 / 20000 : ℝ) =
        (explicitScale : ℝ) * log 2 := by
    calc
      (explicitLogExponent : ℝ) * log 2 * (1 / 20000 : ℝ) =
          ((explicitLogExponent : ℝ) / 20000) * log 2 := by ring
      _ = (explicitScale : ℝ) * log 2 := by
        congr 1
        apply (div_eq_iff (by norm_num : (20000 : ℝ) ≠ 0)).2
        nlinarith only [hrelation]
  rw [Real.rpow_def_of_pos hJpos, log_explicitJ_eq, hexponent]
  calc
    exp ((explicitScale : ℝ) * log 2) =
        exp (log 2) ^ explicitScale := by
      simpa using (Real.exp_nat_mul (log 2) explicitScale)
    _ = (2 : ℝ) ^ explicitScale := by
      rw [Real.exp_log (by norm_num)]

private theorem explicitJ_ge_exp_tiny_inverse :
    exp ((1 / 100000 : ℝ)⁻¹) ≤ (explicitJ : ℝ) := by
  have hJpos : (0 : ℝ) < explicitJ := by
    exact_mod_cast (show 0 < explicitJ by unfold explicitJ; positivity)
  have hlog2 : (2 / 3 : ℝ) < log 2 := by
    exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hT : (150000 : ℝ) ≤ explicitLogExponent := by
    norm_num [explicitLogExponent, explicitQuarterExponent, explicitScale]
  have hlogLower : (100000 : ℝ) ≤ log (explicitJ : ℝ) := by
    rw [log_explicitJ_eq]
    nlinarith only [hlog2, hT]
  have hexp : exp (100000 : ℝ) ≤ (explicitJ : ℝ) := by
    calc
      exp (100000 : ℝ) ≤ exp (log (explicitJ : ℝ)) :=
        exp_le_exp.mpr hlogLower
      _ = (explicitJ : ℝ) := Real.exp_log hJpos
  convert hexp using 1 <;> norm_num

/-- A single explicit logarithmic absorption strong enough for every
power at most ten used by the source and mixed schedules. -/
theorem explicit_log_rpow_le_tiny_of_succ
    {j : ℕ} (hj : explicitJ ≤ j + 1) {m : ℝ}
    (hm0 : 0 ≤ m) (hm10 : m ≤ 10) :
    log (((j + 1 : ℕ) : ℝ)) ^ m ≤
      (((j + 1 : ℕ) : ℝ) ^ (1 / 10000 : ℝ)) := by
  let x : ℝ := (j + 1 : ℕ)
  have hxJ : (explicitJ : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hj
  have hxDomain : exp ((1 / 100000 : ℝ)⁻¹) ≤ x :=
    explicitJ_ge_exp_tiny_inverse.trans hxJ
  have hJpos : (0 : ℝ) < explicitJ := by
    exact_mod_cast (show 0 < explicitJ by unfold explicitJ; positivity)
  have hxpos : 0 < x :=
    (Real.exp_pos ((1 / 100000 : ℝ)⁻¹)).trans_le hxDomain
  have hlogJ : log (explicitJ : ℝ) ≤
      (explicitJ : ℝ) ^ (1 / 100000 : ℝ) := by
    rw [log_explicitJ_eq, explicitJ_tiny_rpow_eq]
    exact (mul_le_of_le_one_right (Nat.cast_nonneg _)
      (by linarith [Real.log_two_lt_d9])).trans
        explicitLogExponent_le_tinyRootPower
  have hratioJ :
      log (explicitJ : ℝ) /
          (explicitJ : ℝ) ^ (1 / 100000 : ℝ) ≤ 1 :=
    (div_le_one (Real.rpow_pos_of_pos hJpos _)).2 hlogJ
  have hratioX :
      log x / x ^ (1 / 100000 : ℝ) ≤ 1 :=
    (Real.log_div_self_rpow_antitoneOn
      (by norm_num : (0 : ℝ) < 1 / 100000)
      explicitJ_ge_exp_tiny_inverse hxDomain hxJ).trans hratioJ
  have hlogBase : log x ≤ x ^ (1 / 100000 : ℝ) :=
    (div_le_one (Real.rpow_pos_of_pos hxpos _)).mp hratioX
  have hlogOne : (1 : ℝ) ≤ log x := by
    have hexpTwo : exp (2 : ℝ) ≤ x :=
      explicitJ_ge_exp_two.trans hxJ
    exact (by norm_num : (1 : ℝ) ≤ 2).trans
      ((Real.le_log_iff_exp_le hxpos).2 hexpTwo)
  calc
    log (((j + 1 : ℕ) : ℝ)) ^ m = log x ^ m := by rfl
    _ ≤ (x ^ (1 / 100000 : ℝ)) ^ m :=
      Real.rpow_le_rpow (zero_le_one.trans hlogOne) hlogBase hm0
    _ = x ^ ((1 / 100000 : ℝ) * m) :=
      (Real.rpow_mul hxpos.le _ _).symm
    _ ≤ x ^ (1 / 10000 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le
        (by
          dsimp [x]
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))
        (by nlinarith only [hm10])

theorem explicit_log_rpow_le_tiny
    {j : ℕ} (hj : explicitJ ≤ j) {m : ℝ}
    (hm0 : 0 ≤ m) (hm10 : m ≤ 10) :
    log (((j + 1 : ℕ) : ℝ)) ^ m ≤
      (((j + 1 : ℕ) : ℝ) ^ (1 / 10000 : ℝ)) :=
  explicit_log_rpow_le_tiny_of_succ
    (hj.trans (Nat.le_succ j)) hm0 hm10

private theorem tiny_le_sourceTerminalLogAbsorption :
    (1 / 10000 : ℝ) ≤ sourceTerminalLogAbsorption := by
  unfold sourceTerminalLogAbsorption sourceTerminalDyadicExponent
    sourceTerminalResidualExponent sourceCanonicalBudgetExponent
    sourceAnatomySlope
  rw [Real.log_four_eq]
  nlinarith [Real.log_two_lt_d9]

private theorem tiny_le_sourceTransitionLogAbsorption :
    (1 / 10000 : ℝ) ≤ sourceTransitionLogAbsorption := by
  unfold sourceTransitionLogAbsorption sourceTransitionAbsorbedExponent
    sourceBulkPowerExponent sourceCanonicalBudgetExponent sourceAnatomySlope
  rw [Real.log_four_eq]
  nlinarith [Real.log_two_lt_d9]

theorem explicit_sourceTerminalProfile_absorbed
    {j : ℕ} (hj : explicitJ ≤ j) :
    log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) ≤
      (((j + 1 : ℕ) : ℝ) ^ sourceTerminalLogAbsorption) := by
  have htiny := explicit_log_rpow_le_tiny hj
    (m := (5 : ℝ)) (by norm_num) (by norm_num)
  exact htiny.trans
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))
      tiny_le_sourceTerminalLogAbsorption)

theorem explicit_sourceTransitionProfile_absorbed
    {j : ℕ} (hj : explicitJ ≤ j) :
    log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) ≤
      (((j + 1 : ℕ) : ℝ) ^ sourceTransitionLogAbsorption) := by
  have htiny := explicit_log_rpow_le_tiny hj
    (m := (5 : ℝ)) (by norm_num) (by norm_num)
  exact htiny.trans
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))
      tiny_le_sourceTransitionLogAbsorption)

/-- The exact finite-sieve dominance condition is valid from `explicitJ`
onward; unlike the production theorem, this contains no hidden eventual
threshold. -/
theorem explicit_sieveSchedule_dominates
    {j : ℕ} (hj : explicitJ ≤ j) :
    32 * Erdos327.Analytic.sieveRadius j ≤ j := by
  have hj1 : 1 ≤ j := by
    have hJpos : 0 < explicitJ := by
      unfold explicitJ
      positivity
    omega
  let x : ℝ := (j + 1 : ℕ)
  have hxJ : (explicitJ : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hj.trans (Nat.le_succ j)
  have hxExp : exp (2 : ℝ) ≤ x := explicitJ_ge_exp_two.trans hxJ
  have hratio : log x / √x ≤ (1 / 384 : ℝ) :=
    (Real.log_div_sqrt_antitoneOn
      explicitJ_ge_exp_two hxExp hxJ).trans explicitJ_log_div_sqrt_le
  have hratio0 : 0 ≤ log x / √x := by
    apply div_nonneg
    · exact log_nonneg (by
        dsimp [x]
        exact_mod_cast (show 1 ≤ j + 1 by omega))
    · positivity
  have hsquare :=
    (sq_le_sq₀ hratio0 (by norm_num : (0 : ℝ) ≤ 1 / 384)).2 hratio
  have hxpos : 0 < x := (Real.exp_pos 2).trans_le hxExp
  have hlogBound : 147456 * log x ^ 2 ≤ x := by
    rw [div_pow, Real.sq_sqrt hxpos.le] at hsquare
    have hm := (div_le_iff₀ hxpos).mp hsquare
    norm_num at hm
    nlinarith only [hm]
  have hheight := Erdos327.Analytic.sieveHeight_cast_sq_le hj1
  have hlog2 : (2 / 3 : ℝ) < log 2 := by
    exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hlog2sq : 0 < log (2 : ℝ) ^ 2 :=
    sq_pos_of_pos (log_pos (by norm_num))
  have hcoefficient : 4 / log (2 : ℝ) ^ 2 ≤ 9 := by
    apply (div_le_iff₀ hlog2sq).2
    nlinarith only [hlog2]
  have hheight' :
      (Erdos327.Analytic.sieveHeight j : ℝ) ^ 2 ≤
        9 * log x ^ 2 := by
    calc
      (Erdos327.Analytic.sieveHeight j : ℝ) ^ 2 ≤
          4 * log (j + 1 : ℕ) ^ 2 / log 2 ^ 2 := hheight
      _ = (4 / log (2 : ℝ) ^ 2) * log x ^ 2 := by
        dsimp [x]
        ring
      _ ≤ 9 * log x ^ 2 :=
        mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg _)
  have hjReal : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hfinal :
      4096 * (Erdos327.Analytic.sieveHeight j : ℝ) ^ 2 ≤
        (j : ℝ) := by
    have hxEq : x = (j : ℝ) + 1 := by
      dsimp [x]
      push_cast
      ring
    rw [hxEq] at hlogBound hheight'
    nlinarith only [hheight', hlogBound, hjReal]
  have hcast :
      ((32 * Erdos327.Analytic.sieveRadius j : ℕ) : ℝ) ≤
        (j : ℝ) := by
    norm_num only [Erdos327.Analytic.sieveRadius, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow]
    convert hfinal using 1 <;> ring
  exact_mod_cast hcast

private theorem explicit_boundary_polynomial_le
    {j : ℕ} (hj : explicitJ ≤ j) :
    2570 * (((j + 1 : ℕ) : ℝ) ^ 10) ≤
      (Erdos327.Analytic.dyadicScale j : ℝ) ^ (3 / 4 : ℝ) := by
  let x : ℝ := (j + 1 : ℕ)
  let X : ℝ := Erdos327.Analytic.dyadicScale j
  have hj48 : 48 ≤ j :=
    (by norm_num : 48 ≤ 64).trans (explicitJ_ge_sixty_four.trans hj)
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hXpos : 0 < X := by
    dsimp [X]
    simp [Erdos327.Analytic.dyadicScale]
  have hXone : (1 : ℝ) ≤ X := by
    dsimp [X, Erdos327.Analytic.dyadicScale]
    exact_mod_cast Nat.one_le_pow j 2 (by norm_num)
  have hlogX : log X = (j : ℝ) * log 2 := by
    dsimp [X]
    simp [Erdos327.Analytic.dyadicScale, Real.log_pow]
  have hlog := explicit_log_add_one_le_div hj
  have hlog2 : (2 / 3 : ℝ) < log 2 := by
    exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hpolyExponent :
      (10 : ℝ) * log x ≤ (1 / 4 : ℝ) * ((j : ℝ) * log 2) := by
    dsimp [x]
    nlinarith only [hlog, hlog2, hj0]
  have hpoly : x ^ (10 : ℕ) ≤ X ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hxpos,
      Real.rpow_def_of_pos hXpos, hlogX]
    apply exp_le_exp.mpr
    nlinarith only [hpolyExponent]
  have hexpTwelve : exp ((12 : ℝ) * log 2) = 4096 := by
    calc
      exp ((12 : ℝ) * log 2) =
          exp (log ((2 : ℝ) ^ (12 : ℕ))) := by
        rw [Real.log_pow]
        norm_num
      _ = (2 : ℝ) ^ (12 : ℕ) := Real.exp_log (by positivity)
      _ = 4096 := by norm_num
  have hfactorExponent :
      (12 : ℝ) * log 2 ≤
        (1 / 4 : ℝ) * ((j : ℝ) * log 2) := by
    have hj48r : (48 : ℝ) ≤ j := by exact_mod_cast hj48
    nlinarith only [hj48r, log_pos (by norm_num : (1 : ℝ) < 2)]
  have hfactor : (2570 : ℝ) ≤ X ^ (1 / 4 : ℝ) := by
    calc
      (2570 : ℝ) ≤ 4096 := by norm_num
      _ = exp ((12 : ℝ) * log 2) := hexpTwelve.symm
      _ ≤ exp ((1 / 4 : ℝ) * ((j : ℝ) * log 2)) :=
        exp_le_exp.mpr hfactorExponent
      _ = X ^ (1 / 4 : ℝ) := by
        rw [Real.rpow_def_of_pos hXpos, hlogX]
        congr 1
        ring
  calc
    2570 * (((j + 1 : ℕ) : ℝ) ^ 10) =
        2570 * x ^ (10 : ℕ) := by rfl
    _ ≤ X ^ (1 / 4 : ℝ) * X ^ (1 / 4 : ℝ) :=
      mul_le_mul hfactor hpoly (pow_nonneg hxpos.le _)
        (Real.rpow_nonneg hXpos.le _)
    _ = X ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hXpos]
      norm_num
    _ ≤ X ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hXone (by norm_num)
    _ = (Erdos327.Analytic.dyadicScale j : ℝ) ^ (3 / 4 : ℝ) := by
      rfl

private theorem explicit_scheduledPolynomialBoundary_le
    {j : ℕ} (hj : explicitJ ≤ j) :
    Erdos327.Analytic.scheduledPolynomialBoundary j ≤
      (Erdos327.Analytic.dyadicScale j : ℝ) ^ 2 /
        (((j + 1 : ℕ) : ℝ) ^ 8) :=
  Erdos327.Analytic.scheduledPolynomialBoundary_le_dyadic_sq_div_add_one_pow_eight
    (explicit_sieveSchedule_dominates hj)
    (explicit_boundary_polynomial_le hj)

private theorem sievePrimeReserve_le_nine :
    Erdos327.Analytic.sievePrimeReserve ≤ (9 : ℝ) := by
  have hlog2pos : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog2lo : (2 / 3 : ℝ) < log 2 := by
    exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hlog2hi : log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_two_lt_d9]
  have hloglogLo : (-1 : ℝ) ≤ log (log 2) := by
    apply (Real.le_log_iff_exp_le hlog2pos).2
    exact Real.exp_neg_one_lt_half.le.trans (by linarith)
  have hloglogHi : log (log 2) ≤ 0 :=
    log_nonpos hlog2pos.le hlog2hi
  have hbounds :=
    Mertens.Weight.M_bounds (f := Mertens.Weight.prime)
  simp only [Mertens.Weight.prime_upperBound_eq,
    Mertens.Weight.prime_lowerBound_eq] at hbounds
  have hratio : log (4 : ℝ) / log 2 = 2 := by
    rw [Real.log_four_eq]
    field_simp
  have hMupper :
      Mertens.Weight.M (f := Mertens.Weight.prime) ≤ 4 := by
    rw [hratio] at hbounds
    linarith [hloglogLo]
  have hthree : 3 / log (2 : ℝ) ≤ (9 / 2 : ℝ) := by
    apply (div_le_iff₀ hlog2pos).2
    nlinarith [hlog2lo]
  have hnegthree :
      (-9 / 2 : ℝ) ≤ -3 / log (2 : ℝ) := by
    calc
      (-9 / 2 : ℝ) = -(9 / 2 : ℝ) := by ring
      _ ≤ -(3 / log (2 : ℝ)) := neg_le_neg hthree
      _ = -3 / log (2 : ℝ) := by ring
  have hMlower :
      (-5 : ℝ) ≤ Mertens.Weight.M (f := Mertens.Weight.prime) := by
    linarith [hbounds.2, hnegthree, hloglogHi]
  have hMabs :
      |Mertens.Weight.M (f := Mertens.Weight.prime)| ≤ (5 : ℝ) :=
    (abs_le).2 ⟨hMlower, hMupper.trans (by norm_num)⟩
  have hreserveFraction :
      (log (4 : ℝ) + 3) / log 4 ≤ 4 := by
    have hlog4 : 0 < log (4 : ℝ) := log_pos (by norm_num)
    apply (div_le_iff₀ hlog4).2
    rw [Real.log_four_eq]
    nlinarith [hlog2lo]
  unfold Erdos327.Analytic.sievePrimeReserve
  linarith

private theorem explicit_sieveHeight_ge_twenty
    {j : ℕ} (hj : explicitJ ≤ j) :
    20 ≤ Erdos327.Analytic.sieveHeight j := by
  have htwenty : 20 ≤ explicitLogExponent := by
    norm_num [explicitLogExponent, explicitQuarterExponent, explicitScale]
  have hpow : 2 ^ (20 : ℕ) ≤ explicitJ := by
    unfold explicitJ
    exact Nat.pow_le_pow_right (by norm_num) htwenty
  have hpowj : 2 ^ (20 : ℕ) ≤ j + 1 :=
    hpow.trans (hj.trans (Nat.le_succ j))
  have hlog : 20 ≤ Nat.log 2 (j + 1) :=
    Nat.le_log_of_pow_le (by norm_num) hpowj
  unfold Erdos327.Analytic.sieveHeight
  omega

private theorem explicit_three_mul_primeInvSum_le
    {j : ℕ} (hj : explicitJ ≤ j) :
    3 * Erdos327.Analytic.primeInvSum
          (Erdos327.Analytic.sieveCutoff j) ≤
      (9 / 2 : ℝ) * Erdos327.Analytic.sieveHeight j := by
  have hdom := explicit_sieveSchedule_dominates hj
  have hprime :=
    Erdos327.Analytic.primeInvSum_sieveCutoff_le_height_add_reserve hdom
  have hheight : (20 : ℝ) ≤ Erdos327.Analytic.sieveHeight j := by
    exact_mod_cast explicit_sieveHeight_ge_twenty hj
  nlinarith only [hprime, sievePrimeReserve_le_nine, hheight]

private theorem explicit_scheduledFactorialTail_le
    {j : ℕ} (hj : explicitJ ≤ j) :
    Erdos327.Analytic.scheduledFactorialTail j ≤
      1 / (((j + 1 : ℕ) : ℝ) ^ 8) :=
  (Erdos327.Analytic.scheduledFactorialTail_le_quarter_pow
      (explicit_three_mul_primeInvSum_le hj)).trans
    (Erdos327.Analytic.quarter_pow_sieveRadius_le_inv_add_one_pow_eight j)

private theorem explicit_forall_sourceScheduledSieve_le_main_add_error
    {j : ℕ} (hj : explicitJ ≤ j) (L : ℕ) :
    sourceAllCutoffSharpSieveBound
        L (sieveCutoff j) (dyadicScale j) (sieveRadius j) ≤
      sourceScheduledEulerSieveMain L j +
        9 * (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) := by
  have htail := explicit_scheduledFactorialTail_le hj
  have hboundary := explicit_scheduledPolynomialBoundary_le hj
  have htailScaled :
      8 * (dyadicScale j : ℝ) ^ 2 * scheduledFactorialTail j ≤
        8 * (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) := by
    calc
      8 * (dyadicScale j : ℝ) ^ 2 * scheduledFactorialTail j ≤
          8 * (dyadicScale j : ℝ) ^ 2 *
            (1 / (((j + 1 : ℕ) : ℝ) ^ 8)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring
  have htailScaled' :
      8 * (dyadicScale j : ℝ) ^ 2 *
          ((3 * primeInvSum (sieveCutoff j)) ^
              (2 * sieveRadius j + 1) /
            ((2 * sieveRadius j + 1).factorial : ℝ)) ≤
        8 * (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) := by
    change
      8 * (dyadicScale j : ℝ) ^ 2 *
          ((3 * primeInvSum (sieveCutoff j)) ^
              (2 * sieveRadius j + 1) /
            ((2 * sieveRadius j + 1).factorial : ℝ)) ≤
        8 * (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) at htailScaled
    exact htailScaled
  have hboundary' :
      ((2 * sieveRadius j + 1 : ℕ) : ℝ) *
          (sieveCutoff j : ℝ) ^ (2 * sieveRadius j) *
          (3 : ℝ) ^ (2 * sieveRadius j) *
          (9 * (dyadicScale j : ℝ) +
            (sieveCutoff j : ℝ) ^ (2 * sieveRadius j)) ≤
        (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) := by
    change
      ((2 * sieveRadius j + 1 : ℕ) : ℝ) *
          (sieveCutoff j : ℝ) ^ (2 * sieveRadius j) *
          (3 : ℝ) ^ (2 * sieveRadius j) *
          (9 * (dyadicScale j : ℝ) +
            (sieveCutoff j : ℝ) ^ (2 * sieveRadius j)) ≤
        (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) at hboundary
    exact hboundary
  unfold sourceAllCutoffSharpSieveBound sourceScheduledEulerSieveMain
  calc
    8 * (dyadicScale j : ℝ) ^ 2 *
          exp (sourceAllCutoffMertensEnvelope L (sieveCutoff j)) +
        8 * (dyadicScale j : ℝ) ^ 2 *
          ((3 * primeInvSum (sieveCutoff j)) ^
              (2 * sieveRadius j + 1) /
            ((2 * sieveRadius j + 1).factorial : ℝ)) +
        ((2 * sieveRadius j + 1 : ℕ) : ℝ) *
          (sieveCutoff j : ℝ) ^ (2 * sieveRadius j) *
          (3 : ℝ) ^ (2 * sieveRadius j) *
          (9 * (dyadicScale j : ℝ) +
            (sieveCutoff j : ℝ) ^ (2 * sieveRadius j)) ≤
      8 * (dyadicScale j : ℝ) ^ 2 *
          exp (sourceAllCutoffMertensEnvelope L (sieveCutoff j)) +
        8 * (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) +
        (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) :=
      add_le_add (add_le_add le_rfl htailScaled') hboundary'
    _ = 8 * (dyadicScale j : ℝ) ^ 2 *
          exp (sourceAllCutoffMertensEnvelope L (sieveCutoff j)) +
        9 * (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) := by ring

private theorem explicit_sourceExactRefinedBlock_le_main_add_error
    {j : ℕ} (hj : explicitJ ≤ j)
    (L : ℕ) (K : ℝ) (hL : 3 ≤ L) (N : ℕ) :
    sourceExactRefinedScheduledBlockBound
        L N sourceAnatomySlope K j ≤
      sourceScheduledEulerBlockMain
        L N sourceAnatomySlope K j +
      sourceScheduledErrorBlockBound N K j := by
  have hsieve := explicit_forall_sourceScheduledSieve_le_main_add_error hj L
  have hdom := explicit_sieveSchedule_dominates hj
  clear hj
  have hz : 2 ≤ sieveCutoff j :=
    two_le_sieveCutoff_of_dominance hdom
  have hclamp : sourceClampedSieveCutoff j = sieveCutoff j :=
    sourceClampedSieveCutoff_eq hz
  by_cases hfar : 8 * dyadicScale j < L
  · rw [sourceExactRefinedScheduledBlockBound, if_pos hfar]
    have hmain0 :
        0 ≤ sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j := by
      unfold sourceScheduledEulerBlockMain
        sourceScheduledEulerSieveMain sourceDyadicBudget
        sourceDyadicResidualMoment
      positivity
    have herror0 :
        0 ≤ sourceScheduledErrorBlockBound N K j := by
      unfold sourceScheduledErrorBlockBound sourceBudgetConstant
      positivity
    linarith
  · have hnear : L ≤ 8 * dyadicScale j := Nat.le_of_not_gt hfar
    have hbudget := sourceScheduledBudget_le_quadratic (K := K) hL hnear
    have hresidual := sourceDyadicResidualMoment_le
      L (dyadicScale j) (2 * N / dyadicScale j ^ 2)
    have hresidual0 :
        0 ≤ sourceDyadicResidualMoment
          L (dyadicScale j) (2 * N / dyadicScale j ^ 2) := by
      unfold sourceDyadicResidualMoment
      positivity
    have hsqResidualNat := dyadic_sq_mul_residualCutoff_le N j
    have hsqResidual :
        (dyadicScale j : ℝ) ^ 2 *
            sourceDyadicResidualMoment
              L (dyadicScale j) (2 * N / dyadicScale j ^ 2) ≤
          2 * (N : ℝ) := by
      calc
        (dyadicScale j : ℝ) ^ 2 *
              sourceDyadicResidualMoment
                L (dyadicScale j) (2 * N / dyadicScale j ^ 2) ≤
            (dyadicScale j : ℝ) ^ 2 *
              (2 * N / dyadicScale j ^ 2 : ℕ) :=
          mul_le_mul_of_nonneg_left hresidual (by positivity)
        _ ≤ 2 * (N : ℝ) := by exact_mod_cast hsqResidualNat
    have hdenom :
        0 ≤ 9 / (((j + 1 : ℕ) : ℝ) ^ 8) := by positivity
    have hcombined :
        sourceDyadicBudget L (dyadicScale j) sourceAnatomySlope K *
            ((dyadicScale j : ℝ) ^ 2 *
              sourceDyadicResidualMoment
                L (dyadicScale j) (2 * N / dyadicScale j ^ 2)) ≤
          (sourceBudgetConstant K * (((j + 3 : ℕ) : ℝ) ^ 2)) *
            (2 * (N : ℝ)) := by
      exact mul_le_mul hbudget hsqResidual
        (mul_nonneg (by positivity) hresidual0)
        (by unfold sourceBudgetConstant; positivity)
    have herror :
        sourceDyadicBudget L (dyadicScale j) sourceAnatomySlope K *
            (9 * (dyadicScale j : ℝ) ^ 2 /
              (((j + 1 : ℕ) : ℝ) ^ 8)) *
            sourceDyadicResidualMoment
              L (dyadicScale j) (2 * N / dyadicScale j ^ 2) ≤
          sourceScheduledErrorBlockBound N K j := by
      calc
        sourceDyadicBudget L (dyadicScale j) sourceAnatomySlope K *
              (9 * (dyadicScale j : ℝ) ^ 2 /
                (((j + 1 : ℕ) : ℝ) ^ 8)) *
              sourceDyadicResidualMoment
                L (dyadicScale j) (2 * N / dyadicScale j ^ 2) =
            (9 / (((j + 1 : ℕ) : ℝ) ^ 8)) *
              (sourceDyadicBudget L (dyadicScale j)
                  sourceAnatomySlope K *
                ((dyadicScale j : ℝ) ^ 2 *
                  sourceDyadicResidualMoment
                    L (dyadicScale j)
                      (2 * N / dyadicScale j ^ 2))) := by ring
        _ ≤ (9 / (((j + 1 : ℕ) : ℝ) ^ 8)) *
              ((sourceBudgetConstant K *
                  (((j + 3 : ℕ) : ℝ) ^ 2)) *
                (2 * (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hcombined hdenom
        _ = sourceScheduledErrorBlockBound N K j := by
          unfold sourceScheduledErrorBlockBound
          ring
    rw [sourceExactRefinedScheduledBlockBound, if_neg hfar,
      sourceScheduledFallbackBlockBound, hclamp]
    have hbudget0 :
        0 ≤ sourceDyadicBudget L (dyadicScale j)
          sourceAnatomySlope K := by
      unfold sourceDyadicBudget
      positivity
    have hscaled :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsieve hbudget0) hresidual0
    refine hscaled.trans ?_
    unfold sourceScheduledEulerBlockMain
    linarith

/-- The source block reduction is fully explicit from `explicitJ` onward. -/
theorem explicit_sourceExactRefinedBlock_le_supported_main_add_error
    {j : ℕ} (hj : explicitJ ≤ j)
    (L : ℕ) (K : ℝ) (hL : 3 ≤ L) (N : ℕ) :
    sourceExactRefinedScheduledBlockBound
        L N sourceAnatomySlope K j ≤
      sourceSupportedEulerBlockMain L N K j +
        sourceScheduledErrorBlockBound N K j := by
  have hmain :=
    explicit_sourceExactRefinedBlock_le_main_add_error hj L K hL N
  by_cases hnear : L ≤ 8 * dyadicScale j
  · simpa [sourceSupportedEulerBlockMain, hnear] using hmain
  · have hfar : 8 * dyadicScale j < L := by omega
    rw [sourceExactRefinedScheduledBlockBound, if_pos hfar,
      sourceSupportedEulerBlockMain, if_neg hnear]
    unfold sourceScheduledErrorBlockBound sourceBudgetConstant
    positivity

/-- A rational lower bound for the explicit Mertens constant used by the proof. -/
theorem one_div_6561_le_mertensLowerConstant :
    (1 / 6561 : ℝ) ≤ Erdos327.Analytic.mertensLowerConstant := by
  have hlog2 : (2 / 3 : ℝ) < log 2 := by
    exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hthree : 3 / log 2 < (9 / 2 : ℝ) := by
    rw [div_lt_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))]
    nlinarith
  have herror : Erdos327.Analytic.mertensLowerError < 7 := by
    unfold Erdos327.Analytic.mertensLowerError
    rw [Real.log_four_eq]
    have hlog2ne : log (2 : ℝ) ≠ 0 :=
      (log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    field_simp [hlog2ne] at hthree ⊢
    nlinarith [hthree]
  have hsum :
      Real.eulerMascheroniConstant +
          Erdos327.Analytic.mertensLowerError ≤ 8 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have he : exp (8 : ℝ) ≤ 6561 := by
    calc
      exp (8 : ℝ) = exp (1 : ℝ) ^ (8 : ℕ) := by
        simpa using (Real.exp_nat_mul (1 : ℝ) 8)
      _ ≤ (3 : ℝ) ^ (8 : ℕ) :=
        (pow_le_pow_left₀ (exp_nonneg 1) Real.exp_one_lt_three.le 8)
      _ = 6561 := by norm_num
  have hinv : (1 / 6561 : ℝ) ≤ exp (-8 : ℝ) := by
    rw [one_div, Real.exp_neg]
    exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 6561) (exp_pos 8)).2 he
  calc
    (1 / 6561 : ℝ) ≤ exp (-8 : ℝ) := hinv
    _ ≤ exp
        (-Real.eulerMascheroniConstant -
          Erdos327.Analytic.mertensLowerError) := by
      apply exp_le_exp.mpr
      linarith
    _ = Erdos327.Analytic.mertensLowerConstant := by
      unfold Erdos327.Analytic.mertensLowerConstant
      rw [← exp_add]
      ring_nf

/-- The explicit roughness cutoff attached to the common dyadic start. -/
def explicitL : ℕ := sourceCoupledCutoff explicitJ

/-- An exact rational real number below the final gain
`roughDensity explicitL / 128`. -/
def explicitEpsilon : ℝ :=
  (1 / 128 : ℝ) * (1 / 6561 : ℝ) *
    (1 / ((explicitJ + 4 : ℕ) : ℝ))

theorem explicitEpsilon_pos : 0 < explicitEpsilon := by
  unfold explicitEpsilon
  positivity

/-- This is the exact quantitative endpoint of the Mertens comparison;
no eventual threshold is used. -/
theorem explicitEpsilon_le_final_gain :
    explicitEpsilon ≤ roughDensity explicitL / 128 := by
  have hL : 3 ≤ explicitL := by
    exact three_le_sourceCoupledCutoff explicitJ
  have hlog : 0 < log (explicitL : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < explicitL by omega))
  have hlogUpper :
      log (explicitL : ℝ) ≤ ((explicitJ + 4 : ℕ) : ℝ) := by
    have hbase := log_sourceCoupledCutoff_le explicitJ
    have hlog2 : log (2 : ℝ) ≤ 1 := by
      linarith [Real.log_two_lt_d9]
    dsimp [explicitL]
    exact hbase.trans
      (mul_le_of_le_one_right (Nat.cast_nonneg _) hlog2)
  have hinv :
      1 / (((explicitJ + 4 : ℕ) : ℝ)) ≤
        1 / log (explicitL : ℝ) :=
    one_div_le_one_div_of_le hlog hlogUpper
  have hmertens := mertensLowerConstant_div_log_le_roughDensity hL
  calc
    explicitEpsilon =
        ((1 / 6561 : ℝ) *
          (1 / (((explicitJ + 4 : ℕ) : ℝ)))) / 128 := by
      unfold explicitEpsilon
      ring
    _ ≤ ((1 / 6561 : ℝ) *
          (1 / log (explicitL : ℝ))) / 128 := by
      gcongr
    _ = ((1 / 6561 : ℝ) / log (explicitL : ℝ)) / 128 := by
      ring
    _ ≤ (mertensLowerConstant / log (explicitL : ℝ)) / 128 := by
      gcongr
      exact one_div_6561_le_mertensLowerConstant
    _ ≤ roughDensity explicitL / 128 :=
      div_le_div_of_nonneg_right hmertens (by norm_num)

private theorem sourceBudgetConstant_explicit_eq :
    sourceBudgetConstant explicitSourceBudget =
      (2 : ℝ) ^ (800000004 : ℕ) := by
  have hexponent :
      log (4 : ℝ) * (explicitSourceBudget + 2) =
        log ((4 : ℝ) ^ (400000002 : ℕ)) := by
    rw [Real.log_pow]
    norm_num [explicitSourceBudget]
    ring
  unfold sourceBudgetConstant
  rw [hexponent, Real.exp_log (by positivity)]
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]

private theorem sourceErrorTailConstant_explicit_le :
    sourceErrorTailConstant explicitSourceBudget ≤
      (2 : ℝ) ^ explicitScale := by
  have hexponent : (800000004 : ℕ) + 8 ≤ explicitScale := by
    norm_num [explicitScale]
  unfold sourceErrorTailConstant powerTailConstant
  norm_num only
  rw [sourceBudgetConstant_explicit_eq]
  calc
    162 * (2 : ℝ) ^ (800000004 : ℕ) * (1 / 5 : ℝ) ≤
        256 * (2 : ℝ) ^ (800000004 : ℕ) := by
      rw [show 162 * (2 : ℝ) ^ (800000004 : ℕ) * (1 / 5 : ℝ) =
          (162 / 5 : ℝ) * (2 : ℝ) ^ (800000004 : ℕ) by ring]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = (2 : ℝ) ^ ((800000004 : ℕ) + 8) := by
      rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, ← pow_add]
    _ ≤ (2 : ℝ) ^ explicitScale :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent

private theorem explicit_sourceError_power_budget :
    (5 * 128 * 6561 : ℝ) * (2 : ℝ) ^ explicitScale ≤
      (explicitJ : ℝ) ^ (4 : ℕ) := by
  have hcoefficient : (5 * 128 * 6561 : ℝ) ≤
      (2 : ℝ) ^ (23 : ℕ) := by norm_num
  have hexponent : explicitScale + 23 ≤ 4 * explicitLogExponent := by
    norm_num [explicitLogExponent, explicitQuarterExponent, explicitScale]
  calc
    (5 * 128 * 6561 : ℝ) * (2 : ℝ) ^ explicitScale ≤
        (2 : ℝ) ^ (23 : ℕ) * (2 : ℝ) ^ explicitScale :=
      mul_le_mul_of_nonneg_right hcoefficient (by positivity)
    _ = (2 : ℝ) ^ (explicitScale + 23) := by
      rw [← pow_add]
      congr 1
    _ ≤ (2 : ℝ) ^ (4 * explicitLogExponent) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent
    _ = (explicitJ : ℝ) ^ (4 : ℕ) := by
      unfold explicitJ
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [← pow_mul]
      congr 1

private theorem sourceErrorCoefficient_explicit_le :
    5 * sourceErrorTailConstant explicitSourceBudget *
        (explicitJ : ℝ) ^ (-4 : ℝ) ≤
      (1 / (128 * 6561) : ℝ) := by
  have hpow :
      (5 * 128 * 6561 : ℝ) * (2 : ℝ) ^ explicitScale ≤
        (explicitJ : ℝ) ^ (4 : ℕ) :=
    explicit_sourceError_power_budget
  have hnum :
      (5 * 128 * 6561 : ℝ) *
          sourceErrorTailConstant explicitSourceBudget ≤
        (explicitJ : ℝ) ^ (4 : ℕ) := by
    exact (mul_le_mul_of_nonneg_left sourceErrorTailConstant_explicit_le
      (by norm_num)).trans hpow
  have hJposNat : 0 < explicitJ :=
    (by norm_num : 0 < 64).trans_le explicitJ_ge_sixty_four
  have hJpos : (0 : ℝ) < explicitJ := by exact_mod_cast hJposNat
  rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num,
    Real.rpow_neg hJpos.le]
  have hfour :
      (explicitJ : ℝ) ^ (4 : ℝ) = (explicitJ : ℝ) ^ (4 : ℕ) := by
    simpa only [Nat.cast_ofNat] using
      (Real.rpow_natCast (explicitJ : ℝ) 4)
  rw [hfour]
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (pow_pos hJpos 4)).2
  have hquot :
      5 * sourceErrorTailConstant explicitSourceBudget ≤
        (explicitJ : ℝ) ^ (4 : ℕ) / (128 * 6561) := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 128 * 6561)).2
    calc
      5 * sourceErrorTailConstant explicitSourceBudget * (128 * 6561) =
          (5 * 128 * 6561) *
            sourceErrorTailConstant explicitSourceBudget := by ring
      _ ≤ (explicitJ : ℝ) ^ (4 : ℕ) := hnum
  calc
    5 * sourceErrorTailConstant explicitSourceBudget ≤
        (explicitJ : ℝ) ^ (4 : ℕ) / (128 * 6561) := hquot
    _ = (1 / (128 * 6561) : ℝ) *
        (explicitJ : ℝ) ^ (4 : ℕ) := by ring

/-- The coupled source schedule-error budget is certified at the fixed
explicit start. -/
theorem explicit_sourceScheduledErrorTail_le_roughDensity
    (N M : ℕ) :
    (∑ j ∈ Ico explicitJ M,
      sourceScheduledErrorBlockBound N explicitSourceBudget j) ≤
        (N : ℝ) * roughDensity (sourceCoupledCutoff explicitJ) / 128 := by
  have hJ1 : 1 ≤ explicitJ := by
    exact (by norm_num : 1 ≤ 64).trans explicitJ_ge_sixty_four
  have hJpos : (0 : ℝ) < explicitJ := by exact_mod_cast hJ1
  have hlogUpper := log_sourceCoupledCutoff_le explicitJ
  have hJfour : explicitJ + 4 ≤ 5 * explicitJ := by omega
  have hlog2 : log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_two_lt_d9]
  have hlogUpper' :
      log (sourceCoupledCutoff explicitJ : ℝ) ≤
        5 * (explicitJ : ℝ) := by
    have hJfourReal :
        ((explicitJ + 4 : ℕ) : ℝ) ≤ 5 * (explicitJ : ℝ) := by
      exact_mod_cast hJfour
    calc
      log (sourceCoupledCutoff explicitJ : ℝ) ≤
          ((explicitJ + 4 : ℕ) : ℝ) * log 2 := hlogUpper
      _ ≤ ((explicitJ + 4 : ℕ) : ℝ) :=
        mul_le_of_le_one_right (by positivity) hlog2
      _ ≤ 5 * (explicitJ : ℝ) := hJfourReal
  have hpowers :
      (explicitJ : ℝ) ^ (-5 : ℝ) * (explicitJ : ℝ) =
        (explicitJ : ℝ) ^ (-4 : ℝ) := by
    calc
      (explicitJ : ℝ) ^ (-5 : ℝ) * (explicitJ : ℝ) =
          (explicitJ : ℝ) ^ (-5 : ℝ) *
            (explicitJ : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (explicitJ : ℝ) ^ ((-5 : ℝ) + 1) := by
        rw [Real.rpow_add hJpos]
      _ = (explicitJ : ℝ) ^ (-4 : ℝ) := by
        congr 1
        ring
  have hconstant0 :
      0 ≤ sourceErrorTailConstant explicitSourceBudget *
        (explicitJ : ℝ) ^ (-5 : ℝ) :=
    mul_nonneg (sourceErrorTailConstant_pos _).le
      (Real.rpow_nonneg hJpos.le _)
  have hsmall :
      sourceErrorTailConstant explicitSourceBudget *
          (explicitJ : ℝ) ^ (-5 : ℝ) *
          log (sourceCoupledCutoff explicitJ : ℝ) ≤
        mertensLowerConstant / 128 := by
    calc
      sourceErrorTailConstant explicitSourceBudget *
            (explicitJ : ℝ) ^ (-5 : ℝ) *
            log (sourceCoupledCutoff explicitJ : ℝ) ≤
          sourceErrorTailConstant explicitSourceBudget *
            (explicitJ : ℝ) ^ (-5 : ℝ) *
            (5 * (explicitJ : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogUpper' hconstant0
      _ = 5 * sourceErrorTailConstant explicitSourceBudget *
            (explicitJ : ℝ) ^ (-4 : ℝ) := by rw [← hpowers]; ring
      _ ≤ (1 / (128 * 6561) : ℝ) :=
        sourceErrorCoefficient_explicit_le
      _ = (1 / 6561 : ℝ) / 128 := by ring
      _ ≤ mertensLowerConstant / 128 :=
        div_le_div_of_nonneg_right one_div_6561_le_mertensLowerConstant
          (by norm_num)
  have hcutoff : 3 ≤ sourceCoupledCutoff explicitJ :=
    three_le_sourceCoupledCutoff explicitJ
  have hlog : 0 < log (sourceCoupledCutoff explicitJ : ℝ) :=
    log_pos (by exact_mod_cast
      (show 1 < sourceCoupledCutoff explicitJ by
        have := three_le_sourceCoupledCutoff explicitJ
        omega))
  have hcoefficient :
      sourceErrorTailConstant explicitSourceBudget *
          (explicitJ : ℝ) ^ (-5 : ℝ) ≤
        (mertensLowerConstant /
          log (sourceCoupledCutoff explicitJ : ℝ)) / 128 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 128)).2
    apply (le_div_iff₀ hlog).2
    calc
      sourceErrorTailConstant explicitSourceBudget *
            (explicitJ : ℝ) ^ (-5 : ℝ) * 128 *
            log (sourceCoupledCutoff explicitJ : ℝ) =
          128 * (sourceErrorTailConstant explicitSourceBudget *
            (explicitJ : ℝ) ^ (-5 : ℝ) *
            log (sourceCoupledCutoff explicitJ : ℝ)) := by ring
      _ ≤ 128 * (mertensLowerConstant / 128) :=
        mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _ = mertensLowerConstant := by ring
  have hmertens := mertensLowerConstant_div_log_le_roughDensity hcutoff
  calc
    (∑ j ∈ Ico explicitJ M,
        sourceScheduledErrorBlockBound N explicitSourceBudget j) ≤
      sourceErrorTailConstant explicitSourceBudget * (N : ℝ) *
        (explicitJ : ℝ) ^ (-5 : ℝ) :=
      sum_sourceScheduledErrorBlockBound_le_rpow hJ1
    _ = (N : ℝ) *
        (sourceErrorTailConstant explicitSourceBudget *
          (explicitJ : ℝ) ^ (-5 : ℝ)) := by ring
    _ ≤ (N : ℝ) *
        ((mertensLowerConstant /
          log (sourceCoupledCutoff explicitJ : ℝ)) / 128) :=
      mul_le_mul_of_nonneg_left hcoefficient (Nat.cast_nonneg N)
    _ ≤ (N : ℝ) *
        (roughDensity (sourceCoupledCutoff explicitJ) / 128) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hmertens (by norm_num))
        (Nat.cast_nonneg N)
    _ = (N : ℝ) * roughDensity (sourceCoupledCutoff explicitJ) / 128 := by
      ring

/-- A crude explicit bound for the uniform weighted Mangoldt constant. -/
private theorem tsum_nat_add_one_neg_three_halves_le_three :
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ))) ≤ 3 := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro N
    by_cases hN : N = 0
    · simp [hN]
    · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
      have htail :=
        Erdos327.Analytic.sum_Ico_add_one_rpow_le
          (r := (-3 / 2 : ℝ)) (by norm_num) (J := 1) (M := N)
          (by norm_num)
      rw [(sum_range_add_sum_Ico
        (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ))) hN1).symm]
      norm_num [Erdos327.Analytic.powerTailConstant] at htail ⊢
      linarith

private theorem tsum_nat_neg_three_halves_le_three :
    (∑' n : ℕ, ((n : ℝ) ^ (-3 / 2 : ℝ))) ≤ 3 := by
  have hs : Summable (fun n : ℕ ↦ ((n : ℝ) ^ (-3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := hs.sum_add_tsum_nat_add 1
  norm_num at hshift
  rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring]
  calc
    (∑' n : ℕ, ((n : ℝ) ^ (-(3 / 2 : ℝ)))) =
        ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := hshift.symm
    _ = ∑' n : ℕ,
        (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
      apply tsum_congr
      intro n
      norm_num [Nat.cast_add]
    _ ≤ 3 := by
      simpa only [show (-(3 / 2 : ℝ)) = (-3 / 2 : ℝ) by ring] using
        tsum_nat_add_one_neg_three_halves_le_three

private theorem tsum_prime_log_div_sq_le_six :
    (∑' p : Nat.Primes, log (p : ℝ) / (p : ℝ) ^ 2) ≤ 6 := by
  have hpoint (p : Nat.Primes) :
      log (p : ℝ) / (p : ℝ) ^ 2 ≤
        2 * (p : ℝ) ^ (-3 / 2 : ℝ) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
    calc
      log (p : ℝ) / (p : ℝ) ^ 2 =
          log (p : ℝ) * (p : ℝ)⁻¹ ^ 2 := by field_simp
      _ ≤ ((p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) *
          (p : ℝ)⁻¹ ^ 2 := by
        gcongr
        exact Real.log_le_rpow_div hp0.le (by norm_num)
      _ = 2 * (p : ℝ) ^ (-3 / 2 : ℝ) := by
        rw [div_eq_mul_inv, ← Real.rpow_natCast,
          Real.inv_rpow hp0.le, ← Real.rpow_neg hp0.le]
        rw [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num]
        ring_nf
        rw [← Real.rpow_add hp0]
        norm_num
  have hprimeSummable :=
    Erdos327.Analytic.summable_prime_log_div_sq
  have hrpowPrime :
      Summable (fun p : Nat.Primes ↦
        2 * (p : ℝ) ^ (-3 / 2 : ℝ)) :=
    (Nat.Primes.summable_rpow.mpr (by norm_num)).mul_left 2
  calc
    (∑' p : Nat.Primes, log (p : ℝ) / (p : ℝ) ^ 2) ≤
        ∑' p : Nat.Primes, 2 * (p : ℝ) ^ (-3 / 2 : ℝ) :=
      hprimeSummable.tsum_le_tsum hpoint hrpowPrime
    _ ≤ ∑' n : ℕ, 2 * (n : ℝ) ^ (-3 / 2 : ℝ) := by
      exact
        (Real.summable_nat_rpow.mpr (by norm_num : (-3 / 2 : ℝ) < -1)).mul_left 2
          |>.tsum_subtype_le
            (fun n : ℕ ↦ 2 * (n : ℝ) ^ (-3 / 2 : ℝ))
            {n : ℕ | n.Prime} (fun _ ↦ by positivity)
    _ = 2 * (∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ)) := by
      rw [tsum_mul_left]
    _ ≤ 6 := by
      linarith [tsum_nat_neg_three_halves_le_three]

private theorem weightedMangoldtTailConstant_eq_tsum_all
    (w : ℕ → ℝ) :
    Erdos327.Analytic.weightedMangoldtTailConstant w =
      ∑' pk : Nat.Primes × ℕ,
        Erdos327.Analytic.weightedPrimePowerAll w pk := by
  let f : ℕ → ℝ :=
    Erdos327.Analytic.weightedNonprimeMangoldtTerm w
  let s : Set ℕ := {n | IsPrimePow n}
  unfold Erdos327.Analytic.weightedMangoldtTailConstant
  change (∑' n : ℕ, f n) = _
  calc
    (∑' n : ℕ, f n) = ∑' n : ℕ, s.indicator f n := by
      apply tsum_congr
      intro n
      by_cases hn : IsPrimePow n
      · simp [s, hn]
      · simp [s, hn, f,
          Erdos327.Analytic.weightedNonprimeMangoldtTerm,
          ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
    _ = ∑' n : s, f n :=
      (_root_.tsum_subtype s f).symm
    _ = ∑' pk : Nat.Primes × ℕ,
        f (Nat.Primes.prodNatEquiv pk) := by
      exact (Nat.Primes.prodNatEquiv.tsum_eq
        (fun n : s ↦ f n)).symm
    _ = ∑' pk : Nat.Primes × ℕ,
        Erdos327.Analytic.weightedPrimePowerAll w pk := by
      apply tsum_congr
      rintro ⟨p, k⟩
      simp [f, Erdos327.Analytic.weightedPrimePowerAll,
        Nat.Primes.coe_prodNatEquiv_apply]

private def weightedPrimePowerAllMajorant
    (pk : Nat.Primes × ℕ) : ℝ :=
  (15 / 2) *
    (log (pk.1 : ℝ) / (pk.1 : ℝ) ^ 2) *
      (5 / 6 : ℝ) ^ pk.2

private theorem weightedPrimePowerAll_le_majorant
    {w : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p, w p ≤ 5 / 2) (hw2 : w 2 ≤ 1)
    (pk : Nat.Primes × ℕ) :
    Erdos327.Analytic.weightedPrimePowerAll w pk ≤
      weightedPrimePowerAllMajorant pk := by
  rcases pk with ⟨p, k⟩
  cases k with
  | zero =>
      simp [Erdos327.Analytic.weightedPrimePowerAll,
        Erdos327.Analytic.weightedNonprimeMangoldtTerm,
        p.prop, weightedPrimePowerAllMajorant]
      positivity
  | succ k =>
      calc
        Erdos327.Analytic.weightedPrimePowerAll w (p, k + 1) =
            Erdos327.Analytic.weightedPrimePowerTail w (p, k) := by
          simp [Erdos327.Analytic.weightedPrimePowerAll,
            Erdos327.Analytic.weightedPrimePowerTail, Nat.add_assoc]
        _ ≤ Erdos327.Analytic.weightedPrimePowerMajorant (p, k) :=
          Erdos327.Analytic.weightedPrimePowerTail_le_majorant
            hw0 hw hw2 (p, k)
        _ = weightedPrimePowerAllMajorant (p, k + 1) := by
          unfold Erdos327.Analytic.weightedPrimePowerMajorant
            weightedPrimePowerAllMajorant
          rw [pow_succ]
          ring

private theorem summable_weightedPrimePowerAllMajorant :
    Summable weightedPrimePowerAllMajorant := by
  have h := Erdos327.Analytic.summable_weightedPrimePowerMajorant.mul_left
    (6 / 5 : ℝ)
  refine h.congr ?_
  intro pk
  unfold weightedPrimePowerAllMajorant
    Erdos327.Analytic.weightedPrimePowerMajorant
  ring

private theorem tsum_weightedPrimePowerAllMajorant_le_270 :
    (∑' pk : Nat.Primes × ℕ, weightedPrimePowerAllMajorant pk) ≤ 270 := by
  have hgeom : ∑' k : ℕ, (5 / 6 : ℝ) ^ k = 6 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  rw [summable_weightedPrimePowerAllMajorant.tsum_prod' (fun p ↦ by
    unfold weightedPrimePowerAllMajorant
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left
      ((15 / 2 : ℝ) * (log (p : ℝ) / (p : ℝ) ^ 2)))]
  simp only [weightedPrimePowerAllMajorant, tsum_mul_left, hgeom]
  have heq :
      (fun p : Nat.Primes ↦
        (15 / 2 : ℝ) * (log (p : ℝ) / (p : ℝ) ^ 2) * 6) =
      (fun p : Nat.Primes ↦
        45 * (log (p : ℝ) / (p : ℝ) ^ 2)) := by
    funext p
    ring
  rw [heq, tsum_mul_left]
  linarith [tsum_prime_log_div_sq_le_six]

theorem uniformWeightedMangoldtConstant_le_thousand :
    Erdos327.Analytic.uniformWeightedMangoldtConstant ≤ (1000 : ℝ) := by
  have htail :
      Erdos327.Analytic.weightedMangoldtTailConstant
          Erdos327.Analytic.maximalPrimeWeight ≤ 270 := by
    rw [weightedMangoldtTailConstant_eq_tsum_all]
    have hpoint := weightedPrimePowerAll_le_majorant
      Erdos327.Analytic.maximalPrimeWeight_nonneg
      Erdos327.Analytic.maximalPrimeWeight_le_five_halves (by simp)
    have hall : Summable (fun pk : Nat.Primes × ℕ ↦
        Erdos327.Analytic.weightedPrimePowerAll
          Erdos327.Analytic.maximalPrimeWeight pk) :=
      summable_weightedPrimePowerAllMajorant.of_nonneg_of_le
        (fun pk ↦
          Erdos327.Analytic.weightedNonprimeMangoldtTerm_nonneg
            Erdos327.Analytic.maximalPrimeWeight_nonneg _)
        hpoint
    exact (hall.tsum_le_tsum hpoint
      summable_weightedPrimePowerAllMajorant).trans
        tsum_weightedPrimePowerAllMajorant_le_270
  unfold Erdos327.Analytic.uniformWeightedMangoldtConstant
    Erdos327.Analytic.weightedMangoldtConstant
  have hlog4 : log (4 : ℝ) < 2 := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_lt_d9]
  linarith

/-- A crude power bound for the source centered-tail constant. -/
private theorem reciprocalPrimeErrorReserve_le_seven :
    Erdos327.Analytic.reciprocalPrimeErrorReserve ≤ (7 : ℝ) := by
  have hlog2 : (2 / 3 : ℝ) < log 2 := by
    exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hthree : 3 / log 2 < (9 / 2 : ℝ) := by
    rw [div_lt_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))]
    nlinarith
  unfold Erdos327.Analytic.reciprocalPrimeErrorReserve
  rw [Real.log_four_eq]
  have hlog2ne : log (2 : ℝ) ≠ 0 :=
    (log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp [hlog2ne] at hthree ⊢
  nlinarith [hthree]

private theorem cutoffTailReserve_le_fifteen :
    Erdos327.Analytic.cutoffTailReserve ≤ (15 : ℝ) := by
  unfold Erdos327.Analytic.cutoffTailReserve
  nlinarith [reciprocalPrimeErrorReserve_le_seven,
    Real.log_two_lt_d9]

private theorem roughCenteredMomentConstant_source_le :
    Erdos327.Analytic.roughCenteredMomentConstant
        Erdos327.Analytic.sourceTailBase ≤ (3 : ℝ) ^ (100 : ℕ) := by
  have hM : (0 : ℝ) < Erdos327.Analytic.mertensLowerConstant :=
    Erdos327.Analytic.mertensLowerConstant_pos
  have hMinv : Erdos327.Analytic.mertensLowerConstant⁻¹ ≤ (6561 : ℝ) := by
    have hsmall : (0 : ℝ) < 1 / 6561 := by norm_num
    simpa using
      (inv_le_inv₀ hM hsmall).2 one_div_6561_le_mertensLowerConstant
  have hfront :
      2 * (Erdos327.Analytic.uniformWeightedMangoldtConstant + 1) /
          Erdos327.Analytic.mertensLowerConstant ≤ (3 : ℝ) ^ (15 : ℕ) := by
    rw [div_eq_mul_inv]
    calc
      2 * (Erdos327.Analytic.uniformWeightedMangoldtConstant + 1) *
            Erdos327.Analytic.mertensLowerConstant⁻¹ ≤
          2 * (1000 + 1) * 6561 := by
        gcongr
        · exact uniformWeightedMangoldtConstant_le_thousand
      _ ≤ (3 : ℝ) ^ (15 : ℕ) := by norm_num
  let E : ℝ :=
    Erdos327.Analytic.sourceTailBase *
        Erdos327.Analytic.cutoffTailReserve +
      2 * Erdos327.Analytic.reciprocalPrimeErrorReserve + 38
  have hE : E ≤ 82 := by
    dsimp [E]
    have hz : Erdos327.Analytic.sourceTailBase ≤ (2 : ℝ) := by
      norm_num [Erdos327.Analytic.sourceTailBase]
    have hcut0 : 0 ≤ Erdos327.Analytic.cutoffTailReserve :=
      Erdos327.Analytic.cutoffTailReserve_nonneg
    have hmul :
        Erdos327.Analytic.sourceTailBase *
            Erdos327.Analytic.cutoffTailReserve ≤ 2 * 15 :=
      mul_le_mul hz cutoffTailReserve_le_fifteen hcut0 (by norm_num)
    linarith [hmul, reciprocalPrimeErrorReserve_le_seven]
  have hexp : exp E ≤ (3 : ℝ) ^ (82 : ℕ) := by
    calc
      exp E ≤ exp (82 : ℝ) := exp_le_exp.mpr hE
      _ = exp (1 : ℝ) ^ (82 : ℕ) := by
        simpa using (Real.exp_nat_mul (1 : ℝ) 82)
      _ ≤ (3 : ℝ) ^ (82 : ℕ) :=
        pow_le_pow_left₀ (exp_nonneg 1) Real.exp_one_lt_three.le 82
  unfold Erdos327.Analytic.roughCenteredMomentConstant
  change
    (2 * (Erdos327.Analytic.uniformWeightedMangoldtConstant + 1) /
        Erdos327.Analytic.mertensLowerConstant) * exp E ≤ _
  calc
    (2 * (Erdos327.Analytic.uniformWeightedMangoldtConstant + 1) /
          Erdos327.Analytic.mertensLowerConstant) * exp E ≤
        (3 : ℝ) ^ (15 : ℕ) * (3 : ℝ) ^ (82 : ℕ) := by
      gcongr
    _ = (3 : ℝ) ^ (97 : ℕ) := by rw [← pow_add]
    _ ≤ (3 : ℝ) ^ (100 : ℕ) := by norm_num

private theorem source_centeredTailRatio_gap :
    (1 / 4000000000000 : ℝ) ≤
      1 - Erdos327.Analytic.centeredTailRatio
        Erdos327.Analytic.sourceAnatomySlope
        Erdos327.Analytic.sourceTailBase := by
  let x : ℝ := 1 / 1000000
  let d : ℝ :=
    Erdos327.Analytic.sourceAnatomySlope *
        log Erdos327.Analytic.sourceTailBase -
      (Erdos327.Analytic.sourceTailBase - 1)
  have hx : 0 ≤ x := by norm_num [x]
  have hlog : 2 * x / (x + 2) ≤ log (1 + x) :=
    Real.le_log_one_add_of_nonneg hx
  have hdefs :
      Erdos327.Analytic.sourceAnatomySlope = 1 + x ∧
      Erdos327.Analytic.sourceTailBase = 1 + x := by
    constructor <;> norm_num [Erdos327.Analytic.sourceAnatomySlope,
      Erdos327.Analytic.sourceTailBase, x]
  have hd : (1 / 3000000000000 : ℝ) ≤ d := by
    rcases hdefs with ⟨hA, hz⟩
    dsimp [d]
    rw [hA, hz]
    have hx2 : 0 < x + 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 1 + x)
    calc
      (1 / 3000000000000 : ℝ) ≤
          (1 + x) * (2 * x / (x + 2)) - x := by
        norm_num [x]
      _ ≤ (1 + x) * log (1 + x) - x :=
        sub_le_sub_right hmul x
      _ = (1 + x) * log (1 + x) - (1 + x - 1) := by ring
  have hd0 : 0 < d := (by norm_num : (0 : ℝ) < 1 / 3000000000000).trans_le hd
  have hexpLower : 1 + d ≤ exp d := by
    simpa [add_comm] using Real.add_one_le_exp d
  have hexpInv : exp (-d) ≤ 1 / (1 + d) := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (by positivity : 0 < exp d) (by linarith : 0 < 1 + d)).2
      hexpLower
  have hfrac : (1 / 4000000000000 : ℝ) ≤ d / (1 + d) := by
    rw [le_div_iff₀ (by linarith : 0 < 1 + d)]
    nlinarith [hd]
  have hratio :
      Erdos327.Analytic.centeredTailRatio
          Erdos327.Analytic.sourceAnatomySlope
          Erdos327.Analytic.sourceTailBase = exp (-d) := by
    unfold Erdos327.Analytic.centeredTailRatio
    dsimp [d]
    congr 1
    ring
  rw [hratio]
  calc
    (1 / 4000000000000 : ℝ) ≤ d / (1 + d) := hfrac
    _ = 1 - 1 / (1 + d) := by field_simp <;> ring
    _ ≤ 1 - exp (-d) := by linarith

private theorem source_centeredTailRatio_inv_le :
    (1 - Erdos327.Analytic.centeredTailRatio
        Erdos327.Analytic.sourceAnatomySlope
        Erdos327.Analytic.sourceTailBase)⁻¹ ≤
      (3 : ℝ) ^ (27 : ℕ) := by
  have hsmall : (0 : ℝ) < 1 / 4000000000000 := by norm_num
  have hgap := source_centeredTailRatio_gap
  have hinv :
      (1 - Erdos327.Analytic.centeredTailRatio
          Erdos327.Analytic.sourceAnatomySlope
          Erdos327.Analytic.sourceTailBase)⁻¹ ≤
        (1 / 4000000000000 : ℝ)⁻¹ :=
    (inv_le_inv₀ (hsmall.trans_le hgap) hsmall).2 hgap
  calc
    _ ≤ (1 / 4000000000000 : ℝ)⁻¹ := hinv
    _ = 4000000000000 := by norm_num
    _ ≤ (3 : ℝ) ^ (27 : ℕ) := by norm_num

private theorem source_exp_anatomy_log_le_three :
    exp (Erdos327.Analytic.sourceAnatomySlope *
      log Erdos327.Analytic.sourceTailBase) ≤ (3 : ℝ) := by
  have hz : (0 : ℝ) < Erdos327.Analytic.sourceTailBase := by
    norm_num [Erdos327.Analytic.sourceTailBase]
  have hlog := Real.log_lt_sub_one_of_pos hz
    (by norm_num [Erdos327.Analytic.sourceTailBase])
  have hA : Erdos327.Analytic.sourceAnatomySlope ≤ (2 : ℝ) := by
    norm_num [Erdos327.Analytic.sourceAnatomySlope]
  have hlog0 : 0 ≤ log Erdos327.Analytic.sourceTailBase :=
    log_nonneg (by norm_num [Erdos327.Analytic.sourceTailBase])
  have hprod :
      Erdos327.Analytic.sourceAnatomySlope *
          log Erdos327.Analytic.sourceTailBase ≤ 1 := by
    calc
      Erdos327.Analytic.sourceAnatomySlope *
            log Erdos327.Analytic.sourceTailBase ≤
          2 * (Erdos327.Analytic.sourceTailBase - 1) :=
        mul_le_mul hA hlog.le hlog0 (by norm_num)
      _ ≤ 1 := by norm_num [Erdos327.Analytic.sourceTailBase]
  exact (exp_le_exp.mpr hprod).trans Real.exp_one_lt_three.le

theorem source_centeredTailConstant_le :
    Erdos327.Analytic.roughCenteredTailConstant
        Erdos327.Analytic.sourceAnatomySlope
        Erdos327.Analytic.sourceTailBase ≤ (3 : ℝ) ^ (150 : ℕ) := by
  unfold Erdos327.Analytic.roughCenteredTailConstant
  have hmoment0 : 0 ≤ Erdos327.Analytic.roughCenteredMomentConstant
      Erdos327.Analytic.sourceTailBase :=
    Erdos327.Analytic.roughCenteredMomentConstant_nonneg _
  have hexp0 : 0 ≤ exp (Erdos327.Analytic.sourceAnatomySlope *
      log Erdos327.Analytic.sourceTailBase) := (exp_pos _).le
  have hinv0 : 0 ≤
      (1 - Erdos327.Analytic.centeredTailRatio
        Erdos327.Analytic.sourceAnatomySlope
        Erdos327.Analytic.sourceTailBase)⁻¹ := by
    apply inv_nonneg.mpr
    exact (by norm_num : (0 : ℝ) ≤ 1 / 4000000000000).trans
      source_centeredTailRatio_gap
  calc
    Erdos327.Analytic.roughCenteredMomentConstant
          Erdos327.Analytic.sourceTailBase *
        exp (Erdos327.Analytic.sourceAnatomySlope *
          log Erdos327.Analytic.sourceTailBase) *
        (1 - Erdos327.Analytic.centeredTailRatio
          Erdos327.Analytic.sourceAnatomySlope
          Erdos327.Analytic.sourceTailBase)⁻¹ ≤
      (3 : ℝ) ^ (100 : ℕ) * 3 * (3 : ℝ) ^ (27 : ℕ) := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact roughCenteredMomentConstant_source_le
          · exact source_exp_anatomy_log_le_three
          · exact hexp0
          · positivity
        · exact source_centeredTailRatio_inv_le
        · exact hinv0
        · positivity
    _ = (3 : ℝ) ^ (128 : ℕ) := by ring
    _ ≤ (3 : ℝ) ^ (150 : ℕ) := by norm_num

/-- The fixed source intercept satisfies the exact tail budget used downstream. -/
theorem explicitSourceBudget_spec :
    Erdos327.Analytic.roughCenteredTailConstant
          Erdos327.Analytic.sourceAnatomySlope
          Erdos327.Analytic.sourceTailBase *
        Erdos327.Analytic.sourceTailBase ^ (-explicitSourceBudget) ≤
      (1 / 8 : ℝ) := by
  let x : ℝ := 1 / 1000000
  have hbase :
      Erdos327.Analytic.sourceTailBase = 1 + x := by
    norm_num [Erdos327.Analytic.sourceTailBase, x]
  have hmillion :
      (2 : ℝ) ≤ Erdos327.Analytic.sourceTailBase ^ (1000000 : ℕ) := by
    have hbern := one_add_mul_le_pow (a := x)
      (by norm_num [x] : (-2 : ℝ) ≤ x) 1000000
    rw [hbase]
    norm_num [x] at hbern ⊢
    exact hbern
  have hlarge :
      (8 : ℝ) * (3 : ℝ) ^ (150 : ℕ) ≤
        Erdos327.Analytic.sourceTailBase ^ (400000000 : ℕ) := by
    calc
      (8 : ℝ) * (3 : ℝ) ^ (150 : ℕ) ≤
          (8 : ℝ) * (4 : ℝ) ^ (150 : ℕ) := by gcongr <;> norm_num
      _ = (2 : ℝ) ^ (303 : ℕ) := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num,
          show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
          ← pow_mul, ← pow_add]
      _ ≤ (2 : ℝ) ^ (400 : ℕ) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num)
      _ ≤ (Erdos327.Analytic.sourceTailBase ^ (1000000 : ℕ)) ^
          (400 : ℕ) :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hmillion 400
      _ = Erdos327.Analytic.sourceTailBase ^ (400000000 : ℕ) := by
        rw [← pow_mul]
  have hrpow :
      (8 : ℝ) * (3 : ℝ) ^ (150 : ℕ) ≤
        Erdos327.Analytic.sourceTailBase ^ explicitSourceBudget := by
    simpa [explicitSourceBudget, Real.rpow_natCast] using hlarge
  have hleft0 :
      0 ≤ Erdos327.Analytic.roughCenteredTailConstant
        Erdos327.Analytic.sourceAnatomySlope
        Erdos327.Analytic.sourceTailBase :=
    Erdos327.Analytic.roughCenteredTailConstant_nonneg
      Erdos327.Analytic.sourceTail_gap
  have hpowPos :
      0 < Erdos327.Analytic.sourceTailBase ^ explicitSourceBudget :=
    Real.rpow_pos_of_pos
      (by norm_num [Erdos327.Analytic.sourceTailBase]) _
  have htargetPos :
      0 < (8 : ℝ) * (3 : ℝ) ^ (150 : ℕ) := by positivity
  have hinv :
      (Erdos327.Analytic.sourceTailBase ^ explicitSourceBudget)⁻¹ ≤
        ((8 : ℝ) * (3 : ℝ) ^ (150 : ℕ))⁻¹ :=
    (inv_le_inv₀ hpowPos htargetPos).2 hrpow
  rw [Real.rpow_neg_eq_inv_rpow,
    Real.inv_rpow (by norm_num [Erdos327.Analytic.sourceTailBase] :
      0 ≤ Erdos327.Analytic.sourceTailBase)]
  calc
    Erdos327.Analytic.roughCenteredTailConstant
          Erdos327.Analytic.sourceAnatomySlope
          Erdos327.Analytic.sourceTailBase *
        (Erdos327.Analytic.sourceTailBase ^ explicitSourceBudget)⁻¹ ≤
      (3 : ℝ) ^ (150 : ℕ) *
        ((8 : ℝ) * (3 : ℝ) ^ (150 : ℕ))⁻¹ := by
      exact mul_le_mul source_centeredTailConstant_le hinv
        (inv_nonneg.mpr hpowPos.le) (by positivity)
    _ = (1 / 8 : ℝ) := by
      field_simp

/-! ## Explicit odd-host tail constant -/

private theorem unrestrictedCenteredMomentConstant_odd_le :
    unrestrictedCenteredMomentConstant oddTailBase ≤
      (3 : ℝ) ^ (76 : ℕ) := by
  have hfrac0 :
      0 ≤ (log (4 : ℝ) + 3) / log 4 := by positivity
  have habs :
      |Mertens.Weight.M (f := Mertens.Weight.prime)| ≤
        sievePrimeReserve := by
    unfold sievePrimeReserve
    linarith
  have hM :
      Mertens.Weight.M (f := Mertens.Weight.prime) ≤ 9 :=
    (le_abs_self _).trans (habs.trans sievePrimeReserve_le_nine)
  have hcutProduct :
      (oddTailBase - 1) * cutoffTailReserve ≤ 15 := by
    have hz : 0 ≤ oddTailBase - 1 ∧ oddTailBase - 1 ≤ 1 := by
      constructor <;> norm_num [oddTailBase]
    exact (mul_le_mul hz.2 cutoffTailReserve_le_fifteen
      cutoffTailReserve_nonneg (by norm_num)).trans (by norm_num)
  let E : ℝ :=
    Mertens.Weight.M (f := Mertens.Weight.prime) +
      reciprocalPrimeErrorReserve +
      (oddTailBase - 1) * cutoffTailReserve + 38
  have hE : E ≤ 69 := by
    dsimp [E]
    linarith [hM, reciprocalPrimeErrorReserve_le_seven, hcutProduct]
  have hfront :
      2 * (uniformWeightedMangoldtConstant + 1) ≤
        (3 : ℝ) ^ (7 : ℕ) := by
    calc
      2 * (uniformWeightedMangoldtConstant + 1) ≤ 2 * (1000 + 1) := by
        gcongr
        exact uniformWeightedMangoldtConstant_le_thousand
      _ ≤ (3 : ℝ) ^ (7 : ℕ) := by norm_num
  have hexp : exp E ≤ (3 : ℝ) ^ (69 : ℕ) := by
    calc
      exp E ≤ exp (69 : ℝ) := exp_le_exp.mpr hE
      _ = exp (1 : ℝ) ^ (69 : ℕ) := by
        simpa using (Real.exp_nat_mul (1 : ℝ) 69)
      _ ≤ (3 : ℝ) ^ (69 : ℕ) :=
        pow_le_pow_left₀ (exp_nonneg 1) Real.exp_one_lt_three.le 69
  unfold unrestrictedCenteredMomentConstant
  change 2 * (uniformWeightedMangoldtConstant + 1) * exp E ≤ _
  calc
    2 * (uniformWeightedMangoldtConstant + 1) * exp E ≤
        (3 : ℝ) ^ (7 : ℕ) * (3 : ℝ) ^ (69 : ℕ) := by
      exact mul_le_mul hfront hexp (exp_nonneg _) (by positivity)
    _ = (3 : ℝ) ^ (76 : ℕ) := by rw [← pow_add]

private theorem odd_exp_anatomy_log_le_three :
    exp (oddAnatomySlope * log oddTailBase) ≤ (3 : ℝ) := by
  have hz : (0 : ℝ) < oddTailBase := by norm_num [oddTailBase]
  have hlog := Real.log_lt_sub_one_of_pos hz
    (by norm_num [oddTailBase])
  have hA : oddAnatomySlope ≤ (2 : ℝ) := by
    norm_num [oddAnatomySlope]
  have hlog0 : 0 ≤ log oddTailBase :=
    log_nonneg (by norm_num [oddTailBase])
  have hprod : oddAnatomySlope * log oddTailBase ≤ 1 := by
    calc
      oddAnatomySlope * log oddTailBase ≤
          2 * (oddTailBase - 1) :=
        mul_le_mul hA hlog.le hlog0 (by norm_num)
      _ ≤ 1 := by norm_num [oddTailBase]
  exact (exp_le_exp.mpr hprod).trans Real.exp_one_lt_three.le

private theorem odd_centeredTailRatio_gap :
    (1 / 300000 : ℝ) ≤
      1 - centeredTailRatio oddAnatomySlope oddTailBase := by
  let d : ℝ :=
    oddAnatomySlope * log oddTailBase - (oddTailBase - 1)
  have hd : (1 / 250000 : ℝ) ≤ d := by
    dsimp [d]
    norm_num [oddAnatomySlope, oddTailBase] at ⊢
    nlinarith [Erdos327.log_zo_lower]
  have hd0 : 0 < d := (by norm_num : (0 : ℝ) < 1 / 250000).trans_le hd
  have hexpLower : 1 + d ≤ exp d := by
    simpa [add_comm] using Real.add_one_le_exp d
  have hexpInv : exp (-d) ≤ 1 / (1 + d) := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (by positivity : 0 < exp d)
      (by linarith : 0 < 1 + d)).2 hexpLower
  have hfrac : (1 / 300000 : ℝ) ≤ d / (1 + d) := by
    rw [le_div_iff₀ (by linarith : 0 < 1 + d)]
    nlinarith [hd]
  have hratio :
      centeredTailRatio oddAnatomySlope oddTailBase = exp (-d) := by
    unfold centeredTailRatio
    dsimp [d]
    congr 1
    ring
  rw [hratio]
  calc
    (1 / 300000 : ℝ) ≤ d / (1 + d) := hfrac
    _ = 1 - 1 / (1 + d) := by field_simp <;> ring
    _ ≤ 1 - exp (-d) := by linarith

private theorem odd_centeredTailRatio_inv_le :
    (1 - centeredTailRatio oddAnatomySlope oddTailBase)⁻¹ ≤
      (3 : ℝ) ^ (12 : ℕ) := by
  have hsmall : (0 : ℝ) < 1 / 300000 := by norm_num
  have hinv :
      (1 - centeredTailRatio oddAnatomySlope oddTailBase)⁻¹ ≤
        (1 / 300000 : ℝ)⁻¹ :=
    (inv_le_inv₀ (hsmall.trans_le odd_centeredTailRatio_gap) hsmall).2
      odd_centeredTailRatio_gap
  calc
    _ ≤ (1 / 300000 : ℝ)⁻¹ := hinv
    _ = 300000 := by norm_num
    _ ≤ (3 : ℝ) ^ (12 : ℕ) := by norm_num

theorem odd_centeredTailConstant_le :
    unrestrictedCenteredTailConstant oddAnatomySlope oddTailBase ≤
      (3 : ℝ) ^ (100 : ℕ) := by
  unfold unrestrictedCenteredTailConstant
  have hmoment0 : 0 ≤ unrestrictedCenteredMomentConstant oddTailBase :=
    unrestrictedCenteredMomentConstant_nonneg _
  have hexp0 : 0 ≤ exp (oddAnatomySlope * log oddTailBase) :=
    (exp_pos _).le
  have hinv0 :
      0 ≤ (1 - centeredTailRatio oddAnatomySlope oddTailBase)⁻¹ := by
    exact inv_nonneg.mpr
      ((by norm_num : (0 : ℝ) ≤ 1 / 300000).trans
        odd_centeredTailRatio_gap)
  calc
    unrestrictedCenteredMomentConstant oddTailBase *
          exp (oddAnatomySlope * log oddTailBase) *
          (1 - centeredTailRatio oddAnatomySlope oddTailBase)⁻¹ ≤
        (3 : ℝ) ^ (76 : ℕ) * 3 * (3 : ℝ) ^ (12 : ℕ) := by
      apply mul_le_mul
      · exact mul_le_mul unrestrictedCenteredMomentConstant_odd_le
          odd_exp_anatomy_log_le_three hexp0 (by positivity)
      · exact odd_centeredTailRatio_inv_le
      · exact hinv0
      · positivity
    _ = (3 : ℝ) ^ (89 : ℕ) := by ring
    _ ≤ (3 : ℝ) ^ (100 : ℕ) := by norm_num

private theorem odd_deletion_gap :
    (1 / 5000 : ℝ) ≤
      oddBudgetSlope * log oddTailBase - 1 := by
  norm_num [oddBudgetSlope, oddTailBase] at ⊢
  nlinarith [Erdos327.log_zo_lower]

private theorem explicitJ_medium_dominates_odd_constant :
    128 * 6561 *
        unrestrictedCenteredTailConstant oddAnatomySlope oddTailBase ≤
      (explicitJ : ℝ) ^ (1 / 10000 : ℝ) := by
  have hscale : 200 ≤ 2 * explicitScale := by
    norm_num [explicitScale]
  calc
    128 * 6561 *
          unrestrictedCenteredTailConstant oddAnatomySlope oddTailBase ≤
        128 * 6561 * (3 : ℝ) ^ (100 : ℕ) := by
      gcongr
      exact odd_centeredTailConstant_le
    _ ≤ (2 : ℝ) ^ (200 : ℕ) := by norm_num
    _ ≤ (2 : ℝ) ^ (2 * explicitScale) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hscale
    _ = (explicitJ : ℝ) ^ (1 / 10000 : ℝ) :=
      explicitJ_medium_rpow_eq.symm

private theorem sqrt_explicitJ_le_log_explicitL :
    √(explicitJ : ℝ) ≤ log (explicitL : ℝ) := by
  have hJ64 : (64 : ℝ) ≤ explicitJ := by
    exact Nat.cast_le.2 explicitJ_ge_sixty_four
  have hJ0 : (0 : ℝ) ≤ explicitJ := by positivity
  have hsqrt :
      √(explicitJ : ℝ) ≤ (2 / 3 : ℝ) * explicitJ := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith only [hJ64]
  have hlog2 : (2 / 3 : ℝ) ≤ log 2 :=
    (by norm_num : (2 / 3 : ℝ) < 0.6931471803).le.trans
      Real.log_two_gt_d9.le
  have hdyadic :
      (dyadicScale explicitJ : ℝ) ≤ (explicitL : ℝ) := by
    change (dyadicScale explicitJ : ℝ) ≤
      (sourceCoupledCutoff explicitJ : ℝ)
    apply Nat.cast_le.2
    have hpos := dyadicScale_pos explicitJ
    have hcut := eight_dyadicScale_lt_sourceCoupledCutoff explicitJ
    omega
  have hdyadicPos : (0 : ℝ) < dyadicScale explicitJ := by
    exact Nat.cast_pos.2 (dyadicScale_pos explicitJ)
  calc
    √(explicitJ : ℝ) ≤ (2 / 3 : ℝ) * explicitJ := hsqrt
    _ ≤ (explicitJ : ℝ) * log 2 := by
      nlinarith only [hlog2, hJ0]
    _ = log (dyadicScale explicitJ : ℝ) :=
      (log_dyadicScale explicitJ).symm
    _ ≤ log (explicitL : ℝ) :=
      Real.log_le_log hdyadicPos hdyadic

private theorem explicit_odd_coefficient_le_log_gap :
    128 * 6561 *
        unrestrictedCenteredTailConstant oddAnatomySlope oddTailBase ≤
      log (explicitL : ℝ) ^
        (oddBudgetSlope * log oddTailBase - 1) := by
  have hJ0 : (0 : ℝ) ≤ explicitJ := by positivity
  have hroot :
      (explicitJ : ℝ) ^ (1 / 10000 : ℝ) =
        (√(explicitJ : ℝ)) ^ (1 / 5000 : ℝ) := by
    calc
      (explicitJ : ℝ) ^ (1 / 10000 : ℝ) =
          (explicitJ : ℝ) ^
            ((1 / 2 : ℝ) * (1 / 5000 : ℝ)) := by
        congr 1
        norm_num
      _ = ((explicitJ : ℝ) ^ (1 / 2 : ℝ)) ^
          (1 / 5000 : ℝ) := Real.rpow_mul hJ0 _ _
      _ = (√(explicitJ : ℝ)) ^ (1 / 5000 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
  have hlogOne : (1 : ℝ) ≤ log (explicitL : ℝ) := by
    have hJOne : (1 : ℝ) ≤ explicitJ := by
      exact (by norm_num : (1 : ℝ) ≤ 64).trans
        (Nat.cast_le.2 explicitJ_ge_sixty_four)
    exact (Real.one_le_sqrt.mpr hJOne).trans
      sqrt_explicitJ_le_log_explicitL
  calc
    128 * 6561 *
          unrestrictedCenteredTailConstant oddAnatomySlope oddTailBase ≤
        (explicitJ : ℝ) ^ (1 / 10000 : ℝ) :=
      explicitJ_medium_dominates_odd_constant
    _ = (√(explicitJ : ℝ)) ^ (1 / 5000 : ℝ) := hroot
    _ ≤ log (explicitL : ℝ) ^ (1 / 5000 : ℝ) :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _)
        sqrt_explicitJ_le_log_explicitL (by norm_num)
    _ ≤ log (explicitL : ℝ) ^
          (oddBudgetSlope * log oddTailBase - 1) :=
      Real.rpow_le_rpow_of_exponent_le hlogOne odd_deletion_gap

/-- The fixed cutoff meets the odd-host regularity budget without an
eventual parameter choice. -/
theorem explicit_oddBudget_meets_tail :
    2 * unrestrictedCenteredTailConstant oddAnatomySlope oddTailBase *
        oddTailBase ^ (-oddBudget explicitL) ≤
      roughDensity explicitL / 64 := by
  let C : ℝ :=
    unrestrictedCenteredTailConstant oddAnatomySlope oddTailBase
  let η : ℝ := oddBudgetSlope * log oddTailBase
  have hL : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  have hLreal : (1 : ℝ) < explicitL := by
    exact (by norm_num : (1 : ℝ) < 3).trans_le (Nat.cast_le.2 hL)
  have hlog : 0 < log (explicitL : ℝ) := log_pos hLreal
  have hcoefficient :
      64 * 6561 * (2 * C) ≤
        log (explicitL : ℝ) ^ (η - 1) := by
    dsimp [C, η]
    convert explicit_odd_coefficient_le_log_gap using 1 <;> ring
  have hpower :
      log (explicitL : ℝ) ^ (-η) * log (explicitL : ℝ) =
        log (explicitL : ℝ) ^ (1 - η) := by
    rw [← Real.rpow_add_one hlog.ne' (-η)]
    congr 1
    ring
  have hcancel :
      log (explicitL : ℝ) ^ (η - 1) *
          log (explicitL : ℝ) ^ (1 - η) = 1 := by
    rw [← Real.rpow_add hlog]
    norm_num
  have hscaled :
      (64 * 6561 * (2 * C)) *
          log (explicitL : ℝ) ^ (1 - η) ≤ 1 := by
    calc
      (64 * 6561 * (2 * C)) *
            log (explicitL : ℝ) ^ (1 - η) ≤
          log (explicitL : ℝ) ^ (η - 1) *
            log (explicitL : ℝ) ^ (1 - η) :=
        mul_le_mul_of_nonneg_right hcoefficient
          (Real.rpow_nonneg hlog.le _)
      _ = 1 := hcancel
  have hfirst :
      (2 * C) * log (explicitL : ℝ) ^ (-η) ≤
        ((1 / 6561 : ℝ) / log (explicitL : ℝ)) / 64 := by
    rw [div_div]
    apply (le_div_iff₀ (mul_pos hlog (by norm_num))).2
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 6561)).2
    calc
      (2 * C) * log (explicitL : ℝ) ^ (-η) *
            (log (explicitL : ℝ) * 64) * 6561 =
          (64 * 6561 * (2 * C)) *
            (log (explicitL : ℝ) ^ (-η) *
              log (explicitL : ℝ)) := by ring
      _ = (64 * 6561 * (2 * C)) *
            log (explicitL : ℝ) ^ (1 - η) := by rw [hpower]
      _ ≤ 1 := hscaled
  have hmertens := mertensLowerConstant_div_log_le_roughDensity hL
  rw [oddBudget, base_rpow_neg_mul_loglog
    (by linarith [oddTailBase_gt_one]) hLreal]
  change (2 * C) * log (explicitL : ℝ) ^ (-η) ≤ _
  have hconstant :
      ((1 / 6561 : ℝ) / log (explicitL : ℝ)) / 64 ≤
        (mertensLowerConstant / log (explicitL : ℝ)) / 64 := by
    gcongr
    exact one_div_6561_le_mertensLowerConstant
  exact hfirst.trans <| hconstant.trans
    (div_le_div_of_nonneg_right hmertens (by norm_num))

/-! ## Crude fixed-constant bounds for the source outer ranges -/

private theorem log_two_lower_half :
    (1 / 2 : ℝ) ≤ log 2 := by
  exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).le.trans
    Real.log_two_gt_d9.le

private theorem source_product_log_ratio_le :
    (log 4 + 3) / log 2 ≤ (15 / 2 : ℝ) := by
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog2Lower : (2 / 3 : ℝ) < log 2 :=
    (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  rw [Real.log_four_eq]
  apply (div_le_iff₀ hlog2).2
  nlinarith

private theorem sourceLargeProductConstant_le :
    sourceLargeProductConstant ≤ (2 : ℝ) ^ (90 : ℕ) := by
  have habs :
      |Mertens.Weight.M (f := Mertens.Weight.prime)| ≤ 9 := by
    have hfrac : 0 ≤ (log (4 : ℝ) + 3) / log 4 := by positivity
    have hreserve :
        |Mertens.Weight.M (f := Mertens.Weight.prime)| ≤
          sievePrimeReserve := by
      unfold sievePrimeReserve
      linarith only [hfrac]
    exact hreserve.trans sievePrimeReserve_le_nine
  have hM := (abs_le.mp habs).1
  have hexponent :
      -(5 / 2 : ℝ) * Mertens.Weight.M (f := Mertens.Weight.prime) +
          (5 / 2 : ℝ) * ((log 4 + 3) / log 2) + 11 / 4 + 3 / 8 ≤
        45 := by
    nlinarith [source_product_log_ratio_le]
  calc
    sourceLargeProductConstant ≤ exp (45 : ℝ) := by
      unfold sourceLargeProductConstant
      exact exp_le_exp.mpr hexponent
    _ = exp (1 : ℝ) ^ (45 : ℕ) := by
      simpa using (Real.exp_nat_mul (1 : ℝ) 45)
    _ ≤ (3 : ℝ) ^ (45 : ℕ) :=
      pow_le_pow_left₀ (exp_nonneg 1) Real.exp_one_lt_three.le 45
    _ ≤ (4 : ℝ) ^ (45 : ℕ) :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) (by norm_num) 45
    _ = (2 : ℝ) ^ (90 : ℕ) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]

private theorem sourceSmallProductConstant_le :
    sourceSmallProductConstant ≤ (2 : ℝ) ^ (90 : ℕ) := by
  have habs :
      |Mertens.Weight.M (f := Mertens.Weight.prime)| ≤ 9 := by
    have hfrac : 0 ≤ (log (4 : ℝ) + 3) / log 4 := by positivity
    have hreserve :
        |Mertens.Weight.M (f := Mertens.Weight.prime)| ≤
          sievePrimeReserve := by
      unfold sievePrimeReserve
      linarith only [hfrac]
    exact hreserve.trans sievePrimeReserve_le_nine
  have hM := (abs_le.mp habs).1
  have hexponent :
      -(5 / 2 : ℝ) * Mertens.Weight.M (f := Mertens.Weight.prime) +
          (5 / 2 : ℝ) * ((log 4 + 3) / log 2) + 11 / 4 ≤
        45 := by
    nlinarith [source_product_log_ratio_le]
  calc
    sourceSmallProductConstant ≤ exp (45 : ℝ) := by
      unfold sourceSmallProductConstant
      exact exp_le_exp.mpr hexponent
    _ = exp (1 : ℝ) ^ (45 : ℕ) := by
      simpa using (Real.exp_nat_mul (1 : ℝ) 45)
    _ ≤ (3 : ℝ) ^ (45 : ℕ) :=
      pow_le_pow_left₀ (exp_nonneg 1) Real.exp_one_lt_three.le 45
    _ ≤ (4 : ℝ) ^ (45 : ℕ) :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) (by norm_num) 45
    _ = (2 : ℝ) ^ (90 : ℕ) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]

private theorem sourceScheduledProductConstant_le :
    sourceScheduledProductConstant ≤ (2 : ℝ) ^ (100 : ℕ) := by
  have hrpow : (4 : ℝ) ^ (3 / 4 : ℝ) ≤ 4 := by
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by norm_num : (3 / 4 : ℝ) ≤ 1)).trans_eq (Real.rpow_one 4)
  calc
    sourceScheduledProductConstant ≤
        (2 : ℝ) ^ (90 : ℕ) + (2 : ℝ) ^ (90 : ℕ) * 4 := by
      unfold sourceScheduledProductConstant
      gcongr
      · exact sourceLargeProductConstant_le
      · exact sourceSmallProductConstant_le
    _ = 5 * (2 : ℝ) ^ (90 : ℕ) := by ring
    _ ≤ 8 * (2 : ℝ) ^ (90 : ℕ) := by gcongr <;> norm_num
    _ = (2 : ℝ) ^ (93 : ℕ) := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← pow_add]
    _ ≤ (2 : ℝ) ^ (100 : ℕ) := by norm_num

private theorem residualMomentConstant_quarter_le :
    residualMomentConstant (1 / 4 : ℝ) ≤
      (2 : ℝ) ^ (120 : ℕ) := by
  have hfront : 2 * (log (4 : ℝ) + 5) ≤ (16 : ℝ) := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_lt_d9]
  have hexponent :
      (1 / 4 : ℝ) * cutoffTailReserve +
          2 * reciprocalPrimeErrorReserve + 38 ≤ 56 := by
    nlinarith [cutoffTailReserve_le_fifteen,
      reciprocalPrimeErrorReserve_le_seven]
  have hexp :
      exp ((1 / 4 : ℝ) * cutoffTailReserve +
          2 * reciprocalPrimeErrorReserve + 38) ≤
        (2 : ℝ) ^ (112 : ℕ) := by
    calc
      _ ≤ exp (56 : ℝ) := exp_le_exp.mpr hexponent
      _ = exp (1 : ℝ) ^ (56 : ℕ) := by
        simpa using (Real.exp_nat_mul (1 : ℝ) 56)
      _ ≤ (3 : ℝ) ^ (56 : ℕ) :=
        pow_le_pow_left₀ (exp_nonneg 1) Real.exp_one_lt_three.le 56
      _ ≤ (4 : ℝ) ^ (56 : ℕ) :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) (by norm_num) 56
      _ = (2 : ℝ) ^ (112 : ℕ) := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
  unfold residualMomentConstant
  calc
    2 * (log 4 + 5) *
          exp ((1 / 4 : ℝ) * cutoffTailReserve +
            2 * reciprocalPrimeErrorReserve + 38) ≤
        16 * (2 : ℝ) ^ (112 : ℕ) := by gcongr
    _ = (2 : ℝ) ^ (116 : ℕ) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← pow_add]
    _ ≤ (2 : ℝ) ^ (120 : ℕ) := by norm_num

private theorem scheduledLogLossConstant_le :
    scheduledLogLossConstant ≤ (2 : ℝ) ^ (16 : ℕ) := by
  have hlogPos : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hsq : (1 / 4 : ℝ) ≤ log (2 : ℝ) ^ 2 := by
    nlinarith [log_two_lower_half,
      sq_nonneg (log (2 : ℝ) - 1 / 2)]
  unfold scheduledLogLossConstant
  apply (div_le_iff₀ (sq_pos_of_pos hlogPos)).2
  calc
    (16384 : ℝ) ≤ (2 : ℝ) ^ (16 : ℕ) * (1 / 4 : ℝ) := by norm_num
    _ ≤ (2 : ℝ) ^ (16 : ℕ) * log (2 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)

private theorem log_two_rpow_neg_five_halves_le :
    log (2 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 8 := by
  have hbase :
      log (2 : ℝ) ^ (-(5 / 2 : ℝ)) ≤
        (1 / 2 : ℝ) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) log_two_lower_half
      (by norm_num)
  calc
    log (2 : ℝ) ^ (-(5 / 2 : ℝ)) ≤
        (1 / 2 : ℝ) ^ (-(5 / 2 : ℝ)) := hbase
    _ ≤ (1 / 2 : ℝ) ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (by norm_num)
    _ = 8 := by
      rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num

private theorem sourceCanonicalBudget_rpow_le_nine :
    (3 : ℝ) ^ sourceCanonicalBudgetExponent ≤ 9 := by
  have hexponent : sourceCanonicalBudgetExponent ≤ (2 : ℝ) :=
    sourceCanonicalBudgetExponent_lt_three_halves.le.trans (by norm_num)
  calc
    (3 : ℝ) ^ sourceCanonicalBudgetExponent ≤ (3 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
    _ = 9 := by norm_num [Real.rpow_natCast]

private theorem two_rpow_five_halves_le_eight :
    (2 : ℝ) ^ (5 / 2 : ℝ) ≤ 8 := by
  calc
    (2 : ℝ) ^ (5 / 2 : ℝ) ≤ (2 : ℝ) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 8 := by norm_num [Real.rpow_natCast]

private theorem scheduledLogLossConstant_rpow_le :
    scheduledLogLossConstant ^ (5 / 2 : ℝ) ≤
      (2 : ℝ) ^ (48 : ℕ) := by
  have hbase := Real.rpow_le_rpow scheduledLogLossConstant_pos.le
    scheduledLogLossConstant_le (by norm_num : (0 : ℝ) ≤ 5 / 2)
  calc
    scheduledLogLossConstant ^ (5 / 2 : ℝ) ≤
        ((2 : ℝ) ^ (16 : ℕ)) ^ (5 / 2 : ℝ) := hbase
    _ ≤ ((2 : ℝ) ^ (16 : ℕ)) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (by norm_num)
    _ = ((2 : ℝ) ^ (16 : ℕ)) ^ (3 : ℕ) :=
      Real.rpow_natCast _ 3
    _ = (2 : ℝ) ^ (48 : ℕ) := by rw [← pow_mul]

private theorem sourceBulkRawConstant_explicit_le :
    sourceBulkRawConstant explicitSourceBudget ≤
      (2 : ℝ) ^ (800000228 : ℕ) := by
  unfold sourceBulkRawConstant
  rw [sourceBudgetConstant_explicit_eq]
  calc
    16 * (2 : ℝ) ^ (800000004 : ℕ) *
          sourceScheduledProductConstant *
          residualMomentConstant (1 / 4 : ℝ) ≤
        16 * (2 : ℝ) ^ (800000004 : ℕ) *
          (2 : ℝ) ^ (100 : ℕ) * (2 : ℝ) ^ (120 : ℕ) := by
      have hprefix :
          16 * (2 : ℝ) ^ (800000004 : ℕ) *
              sourceScheduledProductConstant ≤
            16 * (2 : ℝ) ^ (800000004 : ℕ) *
              (2 : ℝ) ^ (100 : ℕ) :=
        mul_le_mul_of_nonneg_left sourceScheduledProductConstant_le
          (by positivity)
      exact mul_le_mul hprefix residualMomentConstant_quarter_le
        (residualMomentConstant_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ (800000228 : ℕ) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
        ← pow_add, ← pow_add, ← pow_add]

private theorem sourceBulkProfileConstant_explicit_le :
    sourceBulkProfileConstant explicitSourceBudget ≤
      (2 : ℝ) ^ (800001000 : ℕ) := by
  unfold sourceBulkProfileConstant
  calc
    sourceBulkRawConstant explicitSourceBudget *
          (3 : ℝ) ^ sourceCanonicalBudgetExponent *
          (2 : ℝ) ^ (5 / 2 : ℝ) *
          log (2 : ℝ) ^ (-(5 / 2 : ℝ)) *
          scheduledLogLossConstant ^ (5 / 2 : ℝ) ≤
        (2 : ℝ) ^ (800000228 : ℕ) * 16 * 8 * 8 *
          (2 : ℝ) ^ (48 : ℕ) := by
      have h₁ := mul_le_mul sourceBulkRawConstant_explicit_le
        (sourceCanonicalBudget_rpow_le_nine.trans (by norm_num : (9 : ℝ) ≤ 16))
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (800000228 : ℕ))
      have h₂ := mul_le_mul h₁ two_rpow_five_halves_le_eight
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        (by positivity :
          0 ≤ (2 : ℝ) ^ (800000228 : ℕ) * 16)
      have h₃ := mul_le_mul h₂ log_two_rpow_neg_five_halves_le
        (Real.rpow_nonneg (log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) _)
        (by positivity :
          0 ≤ (2 : ℝ) ^ (800000228 : ℕ) * 16 * 8)
      exact mul_le_mul h₃ scheduledLogLossConstant_rpow_le
        (Real.rpow_nonneg scheduledLogLossConstant_pos.le _)
        (by positivity)
    _ = (2 : ℝ) ^ (800000286 : ℕ) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
        show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num,
        ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    _ ≤ (2 : ℝ) ^ (800001000 : ℕ) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num)

private theorem explicitJ_tenth_rpow_eq :
    (explicitJ : ℝ) ^ (1 / 10 : ℝ) =
      (2 : ℝ) ^ (2000 * explicitScale) := by
  have hJpos : (0 : ℝ) < explicitJ := by
    exact Nat.cast_pos.2 (show 0 < explicitJ by unfold explicitJ; positivity)
  have hrelation :
      (explicitLogExponent : ℝ) =
        10 * ((2000 * explicitScale : ℕ) : ℝ) := by
    norm_num [explicitLogExponent, explicitQuarterExponent, explicitScale]
  have hexponent :
      (explicitLogExponent : ℝ) * log 2 * (1 / 10 : ℝ) =
        ((2000 * explicitScale : ℕ) : ℝ) * log 2 := by
    calc
      (explicitLogExponent : ℝ) * log 2 * (1 / 10 : ℝ) =
          ((explicitLogExponent : ℝ) / 10) * log 2 := by ring
      _ = ((2000 * explicitScale : ℕ) : ℝ) * log 2 := by
        congr 1
        apply (div_eq_iff (by norm_num : (10 : ℝ) ≠ 0)).2
        nlinarith only [hrelation]
  rw [Real.rpow_def_of_pos hJpos, log_explicitJ_eq, hexponent]
  calc
    exp (((2000 * explicitScale : ℕ) : ℝ) * log 2) =
        exp (log 2) ^ (2000 * explicitScale) := by
      simpa using
        (Real.exp_nat_mul (log 2) (2000 * explicitScale))
    _ = (2 : ℝ) ^ (2000 * explicitScale) := by
      rw [Real.exp_log (by norm_num)]

private theorem sourceBulk_absorbed_exponent_le :
    sourceBulkPowerExponent + (1 / 10000 : ℝ) ≤ (-11 / 10 : ℝ) := by
  unfold sourceBulkPowerExponent sourceCanonicalBudgetExponent
    sourceAnatomySlope
  rw [Real.log_four_eq]
  nlinarith [Real.log_two_lt_d9]

private theorem explicit_sourceBulk_profile_term_le
    {j : ℕ} (hj : explicitJ ≤ j) :
    (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
        log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) ≤
      (((j + 1 : ℕ) : ℝ) ^ (-11 / 10 : ℝ)) := by
  have hbase : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have habs := explicit_log_rpow_le_tiny hj
    (m := (5 : ℝ)) (by norm_num) (by norm_num)
  calc
    (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) ≤
        (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
          (((j + 1 : ℕ) : ℝ) ^ (1 / 10000 : ℝ)) :=
      mul_le_mul_of_nonneg_left habs
        (Real.rpow_nonneg (zero_le_one.trans hbase) _)
    _ = (((j + 1 : ℕ) : ℝ) ^
          (sourceBulkPowerExponent + 1 / 10000)) := by
      rw [Real.rpow_add (by positivity)]
    _ ≤ (((j + 1 : ℕ) : ℝ) ^ (-11 / 10 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hbase
        sourceBulk_absorbed_exponent_le

private theorem explicit_sourceBulk_profile_tail_le
    (M : ℕ) :
    (∑ j ∈ Ico explicitJ M,
        (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) ≤
      10 * (explicitJ : ℝ) ^ (-1 / 10 : ℝ) := by
  have hJ1 : 1 ≤ explicitJ :=
    (by omega : 1 ≤ 64).trans explicitJ_ge_sixty_four
  have htail := sum_Ico_add_one_rpow_le
    (r := (-11 / 10 : ℝ)) (by norm_num)
    (J := explicitJ) (M := M) hJ1
  calc
    (∑ j ∈ Ico explicitJ M,
        (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) ≤
      ∑ j ∈ Ico explicitJ M,
        (((j + 1 : ℕ) : ℝ) ^ (-11 / 10 : ℝ)) := by
          apply sum_le_sum
          intro j hj
          exact explicit_sourceBulk_profile_term_le (mem_Ico.mp hj).1
    _ ≤ 10 * (explicitJ : ℝ) ^ (-1 / 10 : ℝ) := by
      have hconstant :
          powerTailConstant (-11 / 10 : ℝ) = 10 := by
        norm_num [powerTailConstant]
      have hexponent : (-11 / 10 : ℝ) + 1 = -1 / 10 := by norm_num
      simpa only [hconstant, hexponent] using htail

private theorem explicit_sourceBulk_coefficient_small :
    10 * sourceBulkProfileConstant explicitSourceBudget *
        (explicitJ : ℝ) ^ (-1 / 10 : ℝ) ≤
      mertensLowerConstant / 64 := by
  have hcoefficient :
      640 * 6561 * sourceBulkProfileConstant explicitSourceBudget ≤
        (explicitJ : ℝ) ^ (1 / 10 : ℝ) := by
    have hnum : (640 * 6561 : ℝ) ≤ (2 : ℝ) ^ (23 : ℕ) := by norm_num
    calc
      640 * 6561 * sourceBulkProfileConstant explicitSourceBudget ≤
          (2 : ℝ) ^ (23 : ℕ) *
            (2 : ℝ) ^ (800001000 : ℕ) :=
        mul_le_mul hnum sourceBulkProfileConstant_explicit_le
          (sourceBulkProfileConstant_pos _).le (by positivity)
      _ = (2 : ℝ) ^ (800001023 : ℕ) := by rw [← pow_add]
      _ ≤ (2 : ℝ) ^ (2000 * explicitScale) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num [explicitScale])
      _ = (explicitJ : ℝ) ^ (1 / 10 : ℝ) :=
        explicitJ_tenth_rpow_eq.symm
  have hJpos : (0 : ℝ) < explicitJ :=
    Nat.cast_pos.2 (show 0 < explicitJ by unfold explicitJ; positivity)
  have hcancel :
      (explicitJ : ℝ) ^ (1 / 10 : ℝ) *
          (explicitJ : ℝ) ^ (-1 / 10 : ℝ) = 1 := by
    rw [← Real.rpow_add hJpos]
    have hexponent : (1 / 10 : ℝ) + -1 / 10 = 0 := by norm_num
    rw [hexponent, Real.rpow_zero]
  have hscaled :
      (640 * 6561 * sourceBulkProfileConstant explicitSourceBudget) *
          (explicitJ : ℝ) ^ (-1 / 10 : ℝ) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hcoefficient
      (Real.rpow_nonneg hJpos.le _)).trans_eq hcancel
  have hrational :
      10 * sourceBulkProfileConstant explicitSourceBudget *
          (explicitJ : ℝ) ^ (-1 / 10 : ℝ) ≤
        (1 / 6561 : ℝ) / 64 := by
    rw [div_eq_mul_inv]
    apply (le_mul_inv_iff₀ (by norm_num : (0 : ℝ) < 64)).2
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 6561)).2
    calc
      10 * sourceBulkProfileConstant explicitSourceBudget *
            (explicitJ : ℝ) ^ (-1 / 10 : ℝ) * 64 * 6561 =
          (640 * 6561 * sourceBulkProfileConstant explicitSourceBudget) *
            (explicitJ : ℝ) ^ (-1 / 10 : ℝ) := by ring
      _ ≤ 1 := hscaled
  exact hrational.trans <|
    div_le_div_of_nonneg_right one_div_6561_le_mertensLowerConstant
      (by norm_num)

/-- The fixed dyadic start meets the complete source bulk budget. -/
theorem explicit_sum_sourceEulerMain_bulk_le_roughDensity
    (L N M : ℕ) (hL : 3 ≤ L) :
    (∑ j ∈ sourceBulkIndexSet L N explicitJ M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope explicitSourceBudget j) ≤
      (N : ℝ) * roughDensity L / 64 := by
  have hJ1 : 1 ≤ explicitJ :=
    (by omega : 1 ≤ 64).trans explicitJ_ge_sixty_four
  have hmain := sum_sourceEulerMain_bulk_le_profile
    (L := L) (N := N) (J := explicitJ) (M := M)
    (K := explicitSourceBudget) hL hJ1
  have htail := explicit_sourceBulk_profile_tail_le M
  have hlog : 0 < log (L : ℝ) :=
    log_pos ((by norm_num : (1 : ℝ) < 3).trans_le (Nat.cast_le.2 hL))
  have hfactor : 0 ≤ (N : ℝ) / log (L : ℝ) :=
    div_nonneg (Nat.cast_nonneg N) hlog.le
  have hcoefficient :
      sourceBulkProfileConstant explicitSourceBudget *
          (∑ j ∈ Ico explicitJ M,
            (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) ≤
        mertensLowerConstant / 64 := by
    calc
      _ ≤ sourceBulkProfileConstant explicitSourceBudget *
          (10 * (explicitJ : ℝ) ^ (-1 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_left htail
          (sourceBulkProfileConstant_pos _).le
      _ = 10 * sourceBulkProfileConstant explicitSourceBudget *
          (explicitJ : ℝ) ^ (-1 / 10 : ℝ) := by ring
      _ ≤ mertensLowerConstant / 64 :=
        explicit_sourceBulk_coefficient_small
  have hmertens := mertensLowerConstant_div_log_le_roughDensity hL
  calc
    _ ≤ sourceBulkProfileConstant explicitSourceBudget *
          ((N : ℝ) / log L) *
          (∑ j ∈ Ico explicitJ M,
            (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) := hmain
    _ = (sourceBulkProfileConstant explicitSourceBudget *
          (∑ j ∈ Ico explicitJ M,
            (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ))) *
          ((N : ℝ) / log L) := by ring
    _ ≤ (mertensLowerConstant / 64) * ((N : ℝ) / log L) :=
      mul_le_mul_of_nonneg_right hcoefficient hfactor
    _ = (N : ℝ) * (mertensLowerConstant / log L) / 64 := by ring
    _ ≤ (N : ℝ) * roughDensity L / 64 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmertens (Nat.cast_nonneg N))
        (by norm_num)

/-- At the fixed dyadic start, only the terminal range's ambient-`N`
threshold remains existential. -/
theorem explicit_exists_sourceTerminal_start_for_roughDensity :
    ∃ N₀ : ℕ, ∀ L N M : ℕ, 3 ≤ L → N₀ ≤ N →
      (∑ j ∈ sourceTerminalIndexSet L N explicitJ M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope explicitSourceBudget j) ≤
        (N : ℝ) * roughDensity L / 64 := by
  have hJ1 : 1 ≤ explicitJ :=
    (by omega : 1 ≤ 64).trans explicitJ_ge_sixty_four
  have hC : 0 < sourceTerminalSumConstant explicitSourceBudget :=
    sourceTerminalSumConstant_pos _
  have hε : 0 < mertensLowerConstant / 64 := by
    positivity [mertensLowerConstant_pos]
  have hthreshold :
      0 < (mertensLowerConstant / 64) /
        sourceTerminalSumConstant explicitSourceBudget :=
    div_pos hε hC
  have hev :
      ∀ᶠ N : ℕ in atTop,
        (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^
          (sourceTerminalAbsorbedDyadicExponent +
            sourceTerminalResidualExponent + 1)) <
          (mertensLowerConstant / 64) /
            sourceTerminalSumConstant explicitSourceBudget :=
    (tendsto_order.1 tendsto_sourceTerminalLogProfile).2 _ hthreshold
  rcases eventually_atTop.1 hev with ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro L N M hL hN
  have hmain := sum_sourceEulerMain_terminal_le_log_rpow
    (L := L) (N := N) (J := explicitJ) (M := M)
    (K := explicitSourceBudget) hL hJ1
    (fun j hj ↦ explicit_sourceTerminalProfile_absorbed hj)
  have hprofile := (lt_div_iff₀ hC).mp (hN₀ N hN)
  have hprofile' :
      sourceTerminalSumConstant explicitSourceBudget *
          (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^
            (sourceTerminalAbsorbedDyadicExponent +
              sourceTerminalResidualExponent + 1)) ≤
        mertensLowerConstant / 64 := by
    simpa [mul_comm] using hprofile.le
  have hlog : 0 < log (L : ℝ) :=
    log_pos ((by norm_num : (1 : ℝ) < 3).trans_le (Nat.cast_le.2 hL))
  have hfactor : 0 ≤ (N : ℝ) / log L :=
    div_nonneg (Nat.cast_nonneg N) hlog.le
  have hmertens := mertensLowerConstant_div_log_le_roughDensity hL
  calc
    _ ≤ sourceTerminalSumConstant explicitSourceBudget *
          ((N : ℝ) / log L) *
          (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^
            (sourceTerminalAbsorbedDyadicExponent +
              sourceTerminalResidualExponent + 1)) := hmain
    _ = (sourceTerminalSumConstant explicitSourceBudget *
          (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^
            (sourceTerminalAbsorbedDyadicExponent +
              sourceTerminalResidualExponent + 1))) *
          ((N : ℝ) / log L) := by ring
    _ ≤ (mertensLowerConstant / 64) * ((N : ℝ) / log L) :=
      mul_le_mul_of_nonneg_right hprofile' hfactor
    _ = (N : ℝ) * (mertensLowerConstant / log L) / 64 := by ring
    _ ≤ (N : ℝ) * roughDensity L / 64 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmertens (Nat.cast_nonneg N))
        (by norm_num)

private theorem sourceBoundaryRawConstant_explicit_le :
    sourceBoundaryRawConstant explicitSourceBudget ≤
      (2 : ℝ) ^ (800000108 : ℕ) := by
  unfold sourceBoundaryRawConstant
  rw [sourceBudgetConstant_explicit_eq]
  calc
    16 * (2 : ℝ) ^ (800000004 : ℕ) *
          sourceScheduledProductConstant ≤
        16 * (2 : ℝ) ^ (800000004 : ℕ) *
          (2 : ℝ) ^ (100 : ℕ) :=
      mul_le_mul_of_nonneg_left sourceScheduledProductConstant_le
        (by positivity)
    _ = (2 : ℝ) ^ (800000108 : ℕ) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
        ← pow_add, ← pow_add]

private theorem sourceScheduledIndexProfileConstant_le :
    sourceScheduledIndexProfileConstant (5 / 2 : ℝ) ≤
      (2 : ℝ) ^ (58 : ℕ) := by
  unfold sourceScheduledIndexProfileConstant
  have h₁ := mul_le_mul
    (sourceCanonicalBudget_rpow_le_nine.trans (by norm_num : (9 : ℝ) ≤ 16))
    two_rpow_five_halves_le_eight
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    (by norm_num : (0 : ℝ) ≤ 16)
  have h₂ := mul_le_mul h₁ log_two_rpow_neg_five_halves_le
    (Real.rpow_nonneg (log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) _)
    (by positivity : (0 : ℝ) ≤ 16 * 8)
  have h₃ := mul_le_mul h₂ scheduledLogLossConstant_rpow_le
    (Real.rpow_nonneg scheduledLogLossConstant_pos.le _)
    (by positivity : (0 : ℝ) ≤ 16 * 8 * 8)
  calc
    _ ≤ 16 * 8 * 8 * (2 : ℝ) ^ (48 : ℕ) := h₃
    _ = (2 : ℝ) ^ (58 : ℕ) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
        show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num,
        ← pow_add, ← pow_add, ← pow_add]

private theorem sourceTransition_rpow_factor_le :
    (3 * log (2 : ℝ)) ^ (-sourceTransitionAbsorbedExponent) ≤ 16 := by
  have hbasePos : 0 < 3 * log (2 : ℝ) := by
    positivity [log_pos (by norm_num : (1 : ℝ) < 2)]
  have hbaseOne : (1 : ℝ) ≤ 3 * log 2 := by
    nlinarith [log_two_lower_half]
  have hbaseThree : 3 * log (2 : ℝ) ≤ 3 := by
    nlinarith [Real.log_two_lt_d9]
  have hexponent : -sourceTransitionAbsorbedExponent ≤ (2 : ℝ) := by
    unfold sourceTransitionAbsorbedExponent sourceBulkPowerExponent
      sourceCanonicalBudgetExponent sourceAnatomySlope
    rw [Real.log_four_eq]
    nlinarith [log_two_lower_half]
  calc
    (3 * log (2 : ℝ)) ^ (-sourceTransitionAbsorbedExponent) ≤
        (3 * log (2 : ℝ)) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbaseOne hexponent
    _ ≤ (3 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow hbasePos.le hbaseThree (by norm_num)
    _ = 9 := by norm_num [Real.rpow_natCast]
    _ ≤ 16 := by norm_num

private theorem sourceTransitionAsymptoticConstant_explicit_le :
    sourceTransitionAsymptoticConstant explicitSourceBudget ≤
      (2 : ℝ) ^ (800001000 : ℕ) := by
  unfold sourceTransitionAsymptoticConstant
  have h₁ := mul_le_mul (by norm_num : (3 : ℝ) ≤ 4)
    sourceBoundaryRawConstant_explicit_le
    (sourceBoundaryRawConstant_pos _).le (by norm_num : (0 : ℝ) ≤ 4)
  have h₂ := mul_le_mul h₁ sourceScheduledIndexProfileConstant_le
    (sourceScheduledIndexProfileConstant_pos _).le
    (by positivity :
      0 ≤ (4 : ℝ) * (2 : ℝ) ^ (800000108 : ℕ))
  have h₃ := mul_le_mul h₂ sourceTransition_rpow_factor_le
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 3 * log (2 : ℝ)) _)
    (by positivity :
      0 ≤ (4 : ℝ) * (2 : ℝ) ^ (800000108 : ℕ) *
        (2 : ℝ) ^ (58 : ℕ))
  calc
    _ ≤ 4 * (2 : ℝ) ^ (800000108 : ℕ) *
          (2 : ℝ) ^ (58 : ℕ) * 16 := h₃
    _ = (2 : ℝ) ^ (800000172 : ℕ) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
        show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
        ← pow_add, ← pow_add, ← pow_add]
    _ ≤ (2 : ℝ) ^ (800001000 : ℕ) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num)

private theorem explicitJ_medium_le_log_explicitL_rpow :
    (explicitJ : ℝ) ^ (1 / 10000 : ℝ) ≤
      log (explicitL : ℝ) ^ (1 / 5000 : ℝ) := by
  have hJ0 : (0 : ℝ) ≤ explicitJ := by positivity
  have hroot :
      (explicitJ : ℝ) ^ (1 / 10000 : ℝ) =
        (√(explicitJ : ℝ)) ^ (1 / 5000 : ℝ) := by
    calc
      (explicitJ : ℝ) ^ (1 / 10000 : ℝ) =
          (explicitJ : ℝ) ^ ((1 / 2 : ℝ) * (1 / 5000 : ℝ)) := by
        congr 1
        norm_num
      _ = ((explicitJ : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 5000 : ℝ) :=
        Real.rpow_mul hJ0 _ _
      _ = (√(explicitJ : ℝ)) ^ (1 / 5000 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
  rw [hroot]
  exact Real.rpow_le_rpow (Real.sqrt_nonneg _)
    sqrt_explicitJ_le_log_explicitL (by norm_num)

private theorem sourceTransition_power_gap :
    (1 / 5000 : ℝ) ≤ -sourceTransitionAbsorbedExponent - 1 := by
  unfold sourceTransitionAbsorbedExponent sourceBulkPowerExponent
    sourceCanonicalBudgetExponent sourceAnatomySlope
  rw [Real.log_four_eq]
  nlinarith [Real.log_two_lt_d9]

private theorem explicit_sourceTransitionAsymptotic_le_roughDensity :
    sourceTransitionAsymptoticConstant explicitSourceBudget *
        log (explicitL : ℝ) ^ sourceTransitionAbsorbedExponent ≤
      roughDensity explicitL / 64 := by
  let C := sourceTransitionAsymptoticConstant explicitSourceBudget
  let a := sourceTransitionAbsorbedExponent
  have hL : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  have hlog : 0 < log (explicitL : ℝ) :=
    log_pos ((by norm_num : (1 : ℝ) < 3).trans_le (Nat.cast_le.2 hL))
  have hlogOne : (1 : ℝ) ≤ log (explicitL : ℝ) := by
    have hJOne : (1 : ℝ) ≤ explicitJ :=
      (by norm_num : (1 : ℝ) ≤ 64).trans
        (Nat.cast_le.2 explicitJ_ge_sixty_four)
    exact (Real.one_le_sqrt.mpr hJOne).trans
      sqrt_explicitJ_le_log_explicitL
  have hcoefficient :
      64 * 6561 * C ≤ log (explicitL : ℝ) ^ (-a - 1) := by
    have hnum : (64 * 6561 : ℝ) ≤ (2 : ℝ) ^ (19 : ℕ) := by norm_num
    calc
      64 * 6561 * C ≤
          (2 : ℝ) ^ (19 : ℕ) * (2 : ℝ) ^ (800001000 : ℕ) :=
        mul_le_mul hnum sourceTransitionAsymptoticConstant_explicit_le
          (sourceTransitionAsymptoticConstant_pos _).le (by positivity)
      _ = (2 : ℝ) ^ (800001019 : ℕ) := by rw [← pow_add]
      _ ≤ (2 : ℝ) ^ (2 * explicitScale) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num [explicitScale])
      _ = (explicitJ : ℝ) ^ (1 / 10000 : ℝ) :=
        explicitJ_medium_rpow_eq.symm
      _ ≤ log (explicitL : ℝ) ^ (1 / 5000 : ℝ) :=
        explicitJ_medium_le_log_explicitL_rpow
      _ ≤ log (explicitL : ℝ) ^ (-a - 1) :=
        Real.rpow_le_rpow_of_exponent_le hlogOne (by
          dsimp [a]
          exact sourceTransition_power_gap)
  have hcancel :
      log (explicitL : ℝ) ^ (-a - 1) *
          log (explicitL : ℝ) ^ (a + 1) = 1 := by
    rw [← Real.rpow_add hlog]
    have hexponent : (-a - 1) + (a + 1) = 0 := by ring
    rw [hexponent, Real.rpow_zero]
  have hscaled :
      (64 * 6561 * C) * log (explicitL : ℝ) ^ (a + 1) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hcoefficient
      (Real.rpow_nonneg hlog.le _)).trans_eq hcancel
  have hpower :
      log (explicitL : ℝ) ^ a * log (explicitL : ℝ) =
        log (explicitL : ℝ) ^ (a + 1) := by
    rw [← Real.rpow_add_one hlog.ne' a]
  have hfirst :
      C * log (explicitL : ℝ) ^ a ≤
        ((1 / 6561 : ℝ) / log (explicitL : ℝ)) / 64 := by
    rw [div_div]
    apply (le_div_iff₀ (mul_pos hlog (by norm_num))).2
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 6561)).2
    calc
      C * log (explicitL : ℝ) ^ a *
            (log (explicitL : ℝ) * 64) * 6561 =
          (64 * 6561 * C) *
            (log (explicitL : ℝ) ^ a * log (explicitL : ℝ)) := by ring
      _ = (64 * 6561 * C) * log (explicitL : ℝ) ^ (a + 1) := by
        rw [hpower]
      _ ≤ 1 := hscaled
  have hmertens := mertensLowerConstant_div_log_le_roughDensity hL
  have hconstant :
      ((1 / 6561 : ℝ) / log (explicitL : ℝ)) / 64 ≤
        (mertensLowerConstant / log (explicitL : ℝ)) / 64 := by
    gcongr
    exact one_div_6561_le_mertensLowerConstant
  change C * log (explicitL : ℝ) ^ a ≤ _
  exact hfirst.trans <| hconstant.trans
    (div_le_div_of_nonneg_right hmertens (by norm_num))

/-- The three-block source transition range meets its budget at the
fixed cutoff. -/
theorem explicit_sum_sourceEulerMain_transition_le_roughDensity
    (N J M : ℕ) :
    (∑ j ∈ sourceTransitionIndexSet explicitL J M,
      sourceScheduledEulerBlockMain
        explicitL N sourceAnatomySlope explicitSourceBudget j) ≤
      (N : ℝ) * roughDensity explicitL / 64 := by
  let s := sourceTransitionIndexSet explicitL J M
  let B : ℝ :=
    sourceScheduledIndexProfileConstant (5 / 2 : ℝ) *
      (3 * log (2 : ℝ)) ^ (-sourceTransitionAbsorbedExponent) *
      log (explicitL : ℝ) ^ sourceTransitionAbsorbedExponent
  have hL : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg
        (sourceScheduledIndexProfileConstant_pos _).le
        (Real.rpow_nonneg
          (mul_nonneg (by norm_num)
            (log_pos (by norm_num : (1 : ℝ) < 2)).le) _))
      (Real.rpow_nonneg
        (log_pos ((by norm_num : (1 : ℝ) < 3).trans_le
          (Nat.cast_le.2 hL))).le _)
  have hpoint :
      ∀ j ∈ s,
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
          log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ) ≤ B := by
    intro j hj
    have hj' := hj
    dsimp [s] at hj'
    rw [sourceTransitionIndexSet, mem_filter] at hj'
    have hJj : explicitJ < j := by
      by_contra hnot
      have hjJ : j ≤ explicitJ := Nat.le_of_not_gt hnot
      have hmono := dyadicScale_mono hjJ
      have hbad : explicitL ≤ 8 * dyadicScale explicitJ :=
        hj'.2.2.2.trans (Nat.mul_le_mul_left 8 hmono)
      exact (not_le_of_gt
        (eight_dyadicScale_lt_sourceCoupledCutoff explicitJ)) hbad
    have hj1 : 1 ≤ j := by
      have hJ1 : 1 ≤ explicitJ :=
        (by omega : 1 ≤ 64).trans explicitJ_ge_sixty_four
      omega
    exact sourceTransitionIndexProfile_le_logCutoff
      hL hj1 hj'.2.2.2
      (explicit_sourceTransitionProfile_absorbed hJj.le)
  have hsumCard :
      (∑ j ∈ s,
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
          log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ)) ≤
        s.card • B :=
    Finset.sum_le_card_nsmul s _ B hpoint
  have hcard : s.card ≤ 3 := by
    dsimp [s]
    exact card_sourceTransitionIndexSet_le_three explicitL J M
  have hsum :
      (∑ j ∈ s,
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
          log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ)) ≤
        3 * B := by
    calc
      _ ≤ s.card • B := hsumCard
      _ = (s.card : ℝ) * B := by simp
      _ ≤ 3 * B :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB0
  have hraw := sum_sourceEulerMain_transition_le_raw
    (L := explicitL) (N := N) (J := J) (M := M)
    (K := explicitSourceBudget) hL
  have hfactor0 :
      0 ≤ sourceBoundaryRawConstant explicitSourceBudget * (N : ℝ) :=
    mul_nonneg (sourceBoundaryRawConstant_pos _).le
      (Nat.cast_nonneg N)
  calc
    _ ≤ sourceBoundaryRawConstant explicitSourceBudget * (N : ℝ) *
          (∑ j ∈ sourceTransitionIndexSet explicitL J M,
            (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
              log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
              scheduledLogLoss j ^ (5 / 2 : ℝ)) := hraw
    _ ≤ sourceBoundaryRawConstant explicitSourceBudget * (N : ℝ) *
          (3 * B) := mul_le_mul_of_nonneg_left hsum hfactor0
    _ = (N : ℝ) *
          (sourceTransitionAsymptoticConstant explicitSourceBudget *
            log (explicitL : ℝ) ^ sourceTransitionAbsorbedExponent) := by
      unfold sourceTransitionAsymptoticConstant
      dsimp [B]
      ring
    _ ≤ (N : ℝ) * (roughDensity explicitL / 64) :=
      mul_le_mul_of_nonneg_left
        explicit_sourceTransitionAsymptotic_le_roughDensity
        (Nat.cast_nonneg N)
    _ = (N : ℝ) * roughDensity explicitL / 64 := by ring

private theorem index_le_log_two_add_one_of_pow_le
    {J N : ℕ} (hpow : 2 ^ J ≤ N) :
    J ≤ Nat.log 2 N + 1 :=
  (Nat.le_log_of_pow_le (one_lt_two : (1 : ℕ) < 2) hpow).trans
    (Nat.le_add_right _ _)

/-- The canonical bad-source estimate now uses the concrete source
budget, dyadic start, and cutoff.  Only its final `N` threshold is left
existential. -/
theorem explicit_exists_forall_card_rankBad_le_roughDensity :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((Erdos327.rankBad (Erdos327.upto N)
        (regularSource explicitL sourceAnatomySlope
          explicitSourceBudget N)
        ArithmeticFunction.cardFactors).card : ℝ) ≤
        (N : ℝ) * roughDensity explicitL / 16 := by
  rcases explicit_exists_sourceTerminal_start_for_roughDensity with
    ⟨Nt, hterminal⟩
  have hL : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  have hsmallEps : 0 < roughDensity explicitL / 128 :=
    div_pos (roughDensity_pos hL) (by norm_num)
  rcases eventually_atTop.1
      (eventually_sum_sourceEulerMain_smallResidual_le
        explicitL explicitSourceBudget hL hsmallEps) with
    ⟨Ns, hsmall⟩
  let N₀ : ℕ := max Nt (max Ns (max 2 (2 ^ explicitJ)))
  refine ⟨N₀, ?_⟩
  intro N hN
  have hNt : Nt ≤ N :=
    (le_max_left Nt (max Ns (max 2 (2 ^ explicitJ)))).trans hN
  have hNs : Ns ≤ N :=
    (le_trans (le_max_left Ns (max 2 (2 ^ explicitJ)))
      (le_max_right Nt (max Ns (max 2 (2 ^ explicitJ))))).trans hN
  have hN2 : 2 ≤ N :=
    (le_trans (le_max_left 2 (2 ^ explicitJ))
      (le_trans (le_max_right Ns (max 2 (2 ^ explicitJ)))
        (le_max_right Nt (max Ns (max 2 (2 ^ explicitJ)))))).trans hN
  have hpowN : 2 ^ explicitJ ≤ N :=
    (le_trans (le_max_right 2 (2 ^ explicitJ))
      (le_trans (le_max_right Ns (max 2 (2 ^ explicitJ)))
        (le_max_right Nt (max Ns (max 2 (2 ^ explicitJ)))))).trans hN
  have hJM : explicitJ ≤ Nat.log 2 N + 1 :=
    index_le_log_two_add_one_of_pow_le hpowN
  let M : ℕ := Nat.log 2 N + 1
  have hprefix :
      (∑ j ∈ range explicitJ,
        sourceExactRefinedScheduledBlockBound
          explicitL N sourceAnatomySlope explicitSourceBudget j) = 0 :=
    sum_sourceExactRefinedScheduledBlockBound_range_eq_zero
      (eight_dyadicScale_lt_sourceCoupledCutoff explicitJ)
  have hlate :
      (∑ j ∈ Ico explicitJ M,
        sourceExactRefinedScheduledBlockBound
          explicitL N sourceAnatomySlope explicitSourceBudget j) ≤
        (∑ j ∈ Ico explicitJ M,
          sourceSupportedEulerBlockMain
            explicitL N explicitSourceBudget j) +
        ∑ j ∈ Ico explicitJ M,
          sourceScheduledErrorBlockBound N explicitSourceBudget j := by
    calc
      _ ≤ ∑ j ∈ Ico explicitJ M,
          (sourceSupportedEulerBlockMain
              explicitL N explicitSourceBudget j +
            sourceScheduledErrorBlockBound
              N explicitSourceBudget j) := by
        apply sum_le_sum
        intro j hj
        exact explicit_sourceExactRefinedBlock_le_supported_main_add_error
          (mem_Ico.mp hj).1 explicitL explicitSourceBudget hL N
      _ = _ := by rw [sum_add_distrib]
  have hbulk :
      (∑ j ∈ sourceBulkIndexSet explicitL N explicitJ M,
        sourceScheduledEulerBlockMain
          explicitL N sourceAnatomySlope explicitSourceBudget j) ≤
        (N : ℝ) * roughDensity explicitL / 64 :=
    explicit_sum_sourceEulerMain_bulk_le_roughDensity explicitL N M hL
  have hterminalN :
      (∑ j ∈ sourceTerminalIndexSet explicitL N explicitJ M,
        sourceScheduledEulerBlockMain
          explicitL N sourceAnatomySlope explicitSourceBudget j) ≤
        (N : ℝ) * roughDensity explicitL / 64 :=
    hterminal explicitL N M hL hNt
  have htransition :
      (∑ j ∈ sourceTransitionIndexSet explicitL explicitJ M,
        sourceScheduledEulerBlockMain
          explicitL N sourceAnatomySlope explicitSourceBudget j) ≤
        (N : ℝ) * roughDensity explicitL / 64 :=
    explicit_sum_sourceEulerMain_transition_le_roughDensity N explicitJ M
  have hsmallN :
      (∑ j ∈ sourceSmallResidualIndexSet explicitL N explicitJ M,
        sourceScheduledEulerBlockMain
          explicitL N sourceAnatomySlope explicitSourceBudget j) ≤
        (roughDensity explicitL / 128) * (N : ℝ) :=
    hsmall N hNs explicitJ M
  have herror :
      (∑ j ∈ Ico explicitJ M,
        sourceScheduledErrorBlockBound N explicitSourceBudget j) ≤
        (N : ℝ) * roughDensity explicitL / 128 := by
    exact explicit_sourceScheduledErrorTail_le_roughDensity N M
  have hdom :
      ∀ j ≥ explicitJ, 32 * sieveRadius j ≤ j :=
    fun j hj ↦ explicit_sieveSchedule_dominates hj
  have hmain :
      (∑ j ∈ Ico explicitJ M,
        sourceSupportedEulerBlockMain
          explicitL N explicitSourceBudget j) ≤
        7 * ((N : ℝ) * roughDensity explicitL) / 128 := by
    rw [sum_sourceSupportedEulerBlockMain_eq_four_ranges hL hdom]
    linarith
  have hglobal := card_rankBad_le_exactRefinedScheduled_sum
    (L := explicitL) (N := N)
    (A := sourceAnatomySlope) (K := explicitSourceBudget)
    hL hN2 sourceAnatomySlope_nonneg
  calc
    ((Erdos327.rankBad (Erdos327.upto N)
        (regularSource explicitL sourceAnatomySlope
          explicitSourceBudget N)
        ArithmeticFunction.cardFactors).card : ℝ) ≤
      ∑ j ∈ range M,
        sourceExactRefinedScheduledBlockBound
          explicitL N sourceAnatomySlope explicitSourceBudget j := by
            simpa [M] using hglobal
    _ =
      (∑ j ∈ range explicitJ,
        sourceExactRefinedScheduledBlockBound
          explicitL N sourceAnatomySlope explicitSourceBudget j) +
      ∑ j ∈ Ico explicitJ M,
        sourceExactRefinedScheduledBlockBound
          explicitL N sourceAnatomySlope explicitSourceBudget j :=
      (sum_range_add_sum_Ico _ hJM).symm
    _ = ∑ j ∈ Ico explicitJ M,
        sourceExactRefinedScheduledBlockBound
          explicitL N sourceAnatomySlope explicitSourceBudget j := by
      rw [hprefix, zero_add]
    _ ≤
      (∑ j ∈ Ico explicitJ M,
        sourceSupportedEulerBlockMain
          explicitL N explicitSourceBudget j) +
      ∑ j ∈ Ico explicitJ M,
        sourceScheduledErrorBlockBound N explicitSourceBudget j := hlate
    _ ≤ 7 * ((N : ℝ) * roughDensity explicitL) / 128 +
        ((N : ℝ) * roughDensity explicitL / 128) :=
      add_le_add hmain herror
    _ = (N : ℝ) * roughDensity explicitL / 16 := by ring

/-! ## Fixed-cutoff mixed estimates -/

private theorem natLog_two_sourceCoupledCutoff (J : ℕ) :
    Nat.log 2 (sourceCoupledCutoff J) = J + 3 := by
  have hp : 1 ≤ 2 ^ J := Nat.one_le_pow J 2 (by norm_num)
  have h8 : 2 ^ (3 : ℕ) = 8 := by norm_num
  have h16 : 2 ^ (4 : ℕ) = 16 := by norm_num
  have hlower : 2 ^ (J + 3) ≤ sourceCoupledCutoff J := by
    change 2 ^ (J + 3) ≤ 8 * 2 ^ J + 1
    rw [pow_add, h8]
    omega
  have hupper : sourceCoupledCutoff J < 2 ^ ((J + 3) + 1) := by
    change 8 * 2 ^ J + 1 < 2 ^ ((J + 3) + 1)
    rw [show (J + 3) + 1 = J + 4 by omega, pow_add, h16]
    omega
  exact Nat.log_eq_of_pow_le_of_lt_pow hlower hupper

private theorem natLog_two_explicitL :
    Nat.log 2 explicitL = explicitJ + 3 :=
  natLog_two_sourceCoupledCutoff explicitJ

private theorem mixedBulkMovingStart_sourceCoupledCutoff
    (J : ℕ) (hJ : 1 ≤ J) :
    mixedBulkMovingStart (sourceCoupledCutoff J) = J - 1 := by
  unfold mixedBulkMovingStart
  rw [natLog_two_sourceCoupledCutoff]
  omega

private theorem mixedBulkMovingStart_explicitL :
    mixedBulkMovingStart explicitL = explicitJ - 1 :=
  mixedBulkMovingStart_sourceCoupledCutoff explicitJ
    ((by omega : 1 ≤ 64).trans explicitJ_ge_sixty_four)

private theorem explicit_mixedBulkProfile_absorbed
    {j : ℕ} (hj : mixedBulkMovingStart explicitL ≤ j) :
    (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
        log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) ≤
      (((j + 1 : ℕ) : ℝ) ^
        (mixedCanonicalCrossExponent + mixedBulkLogAbsorption)) := by
  have hJsucc : explicitJ ≤ j + 1 := by
    rw [mixedBulkMovingStart_explicitL] at hj
    have hJ1 : 1 ≤ explicitJ :=
      (by omega : 1 ≤ 64).trans explicitJ_ge_sixty_four
    omega
  have hlog := explicit_log_rpow_le_tiny_of_succ hJsucc
    (m := (4 : ℝ)) (by norm_num) (by norm_num)
  have hx : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  calc
    _ ≤ (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
        (((j + 1 : ℕ) : ℝ) ^ mixedBulkLogAbsorption) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [mixedBulkLogAbsorption] using hlog)
        (Real.rpow_nonneg hx.le _)
    _ = _ := by rw [← Real.rpow_add hx]

private theorem explicitScalePower_le_log_explicitL_rpow :
    (2 : ℝ) ^ explicitScale ≤
      log (explicitL : ℝ) ^ (1 / 10000 : ℝ) := by
  have hJ0 : (0 : ℝ) ≤ explicitJ := by positivity
  have hroot :
      (explicitJ : ℝ) ^ (1 / 20000 : ℝ) =
        (√(explicitJ : ℝ)) ^ (1 / 10000 : ℝ) := by
    calc
      (explicitJ : ℝ) ^ (1 / 20000 : ℝ) =
          (explicitJ : ℝ) ^
            ((1 / 2 : ℝ) * (1 / 10000 : ℝ)) := by
        congr 1
        norm_num
      _ = ((explicitJ : ℝ) ^ (1 / 2 : ℝ)) ^
            (1 / 10000 : ℝ) :=
        Real.rpow_mul hJ0 _ _
      _ = (√(explicitJ : ℝ)) ^ (1 / 10000 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
  rw [← explicitJ_small_rpow_eq, hroot]
  exact Real.rpow_le_rpow (Real.sqrt_nonneg _)
    sqrt_explicitJ_le_log_explicitL (by norm_num)

private theorem explicit_const_mul_log_rpow_le_roughDensity
    {C D η : ℝ}
    (hC0 : 0 ≤ C)
    (hC : C ≤ (2 : ℝ) ^ (explicitScale / 2))
    (hD0 : 0 < D) (hD : D ≤ 8192)
    (hgap : (1 / 10000 : ℝ) ≤ η - 1) :
    C * log (explicitL : ℝ) ^ (-η) ≤
      roughDensity explicitL / D := by
  have hL : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  have hlog : 0 < log (explicitL : ℝ) :=
    log_pos ((by norm_num : (1 : ℝ) < 3).trans_le (Nat.cast_le.2 hL))
  have hlogOne : (1 : ℝ) ≤ log (explicitL : ℝ) := by
    have hJOne : (1 : ℝ) ≤ explicitJ :=
      (by norm_num : (1 : ℝ) ≤ 64).trans
        (Nat.cast_le.2 explicitJ_ge_sixty_four)
    exact (Real.one_le_sqrt.mpr hJOne).trans
      sqrt_explicitJ_le_log_explicitL
  have hcoefficient :
      D * 6561 * C ≤ log (explicitL : ℝ) ^ (η - 1) := by
    have hfront : D * 6561 ≤ (2 : ℝ) ^ (26 : ℕ) := by
      calc
        D * 6561 ≤ 8192 * 8192 :=
          mul_le_mul hD (by norm_num : (6561 : ℝ) ≤ 8192)
            (by norm_num) (by norm_num)
        _ = (2 : ℝ) ^ (26 : ℕ) := by norm_num
    calc
      D * 6561 * C ≤
          (2 : ℝ) ^ (26 : ℕ) *
            (2 : ℝ) ^ (explicitScale / 2) :=
        mul_le_mul hfront hC hC0 (by positivity)
      _ = (2 : ℝ) ^ (explicitScale / 2 + 26) := by
        rw [add_comm, ← pow_add]
      _ ≤ (2 : ℝ) ^ explicitScale :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num [explicitScale])
      _ ≤ log (explicitL : ℝ) ^ (1 / 10000 : ℝ) :=
        explicitScalePower_le_log_explicitL_rpow
      _ ≤ log (explicitL : ℝ) ^ (η - 1) :=
        Real.rpow_le_rpow_of_exponent_le hlogOne hgap
  have hcancel :
      log (explicitL : ℝ) ^ (η - 1) *
          log (explicitL : ℝ) ^ (1 - η) = 1 := by
    rw [← Real.rpow_add hlog]
    have hexponent : (η - 1) + (1 - η) = 0 := by ring
    rw [hexponent, Real.rpow_zero]
  have hscaled :
      (D * 6561 * C) * log (explicitL : ℝ) ^ (1 - η) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hcoefficient
      (Real.rpow_nonneg hlog.le _)).trans_eq hcancel
  have hpower :
      log (explicitL : ℝ) ^ (-η) * log (explicitL : ℝ) =
        log (explicitL : ℝ) ^ (1 - η) := by
    rw [← Real.rpow_add_one hlog.ne' (-η)]
    congr 1
    ring
  have hfirst :
      C * log (explicitL : ℝ) ^ (-η) ≤
        ((1 / 6561 : ℝ) / log (explicitL : ℝ)) / D := by
    rw [div_div]
    apply (le_div_iff₀ (mul_pos hlog hD0)).2
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 6561)).2
    calc
      C * log (explicitL : ℝ) ^ (-η) *
            (log (explicitL : ℝ) * D) * 6561 =
          (D * 6561 * C) *
            (log (explicitL : ℝ) ^ (-η) * log (explicitL : ℝ)) := by
        ring
      _ = (D * 6561 * C) * log (explicitL : ℝ) ^ (1 - η) := by
        rw [hpower]
      _ ≤ 1 := hscaled
  have hmertens := mertensLowerConstant_div_log_le_roughDensity hL
  have hconstant :
      ((1 / 6561 : ℝ) / log (explicitL : ℝ)) / D ≤
        (mertensLowerConstant / log (explicitL : ℝ)) / D := by
    gcongr
    exact one_div_6561_le_mertensLowerConstant
  exact hfirst.trans <| hconstant.trans
    (div_le_div_of_nonneg_right hmertens hD0.le)

/-! ## Explicit mixed fixed-constant bounds -/

private theorem primeMertens_abs_le_nine :
    |Mertens.Weight.M (f := Mertens.Weight.prime)| ≤ (9 : ℝ) := by
  have hfrac : 0 ≤ (log (4 : ℝ) + 3) / log 4 := by positivity
  have hreserve :
      |Mertens.Weight.M (f := Mertens.Weight.prime)| ≤
        sievePrimeReserve := by
    unfold sievePrimeReserve
    linarith only [hfrac]
  exact hreserve.trans sievePrimeReserve_le_nine

private theorem mixedLargeProductConstant_le :
    mixedLargeProductConstant
        mixedCanonicalAlpha mixedCanonicalBeta mixedCanonicalS ≤
      (2 : ℝ) ^ (110 : ℕ) := by
  let a : ℝ := mixedCanonicalAlpha + mixedCanonicalBeta +
    mixedCanonicalS - 3
  let b : ℝ := 1 - mixedCanonicalAlpha - mixedCanonicalBeta -
    mixedCanonicalS
  have haLower : (-2 : ℝ) ≤ a := by
    dsimp [a]
    exact mixedCanonicalProductExponent_gt_neg_two.le
  have haUpper : a ≤ 0 := by
    dsimp [a]
    exact mixedCanonicalProductExponent_lt_zero.le
  have hbLower : (-2 : ℝ) ≤ b := by
    dsimp [b]
    norm_num [mixedCanonicalAlpha, mixedCanonicalBeta,
      mixedCanonicalS, mixedSourceWeightBase, mixedOddWeightBase]
  have hbUpper : b ≤ 0 := by
    dsimp [b]
    exact mixedCanonicalRoughnessExponent_lt_zero.le
  have habsA : |a| ≤ 2 := (abs_le).2 ⟨haLower, haUpper.trans (by norm_num)⟩
  have habsB : |b| ≤ 2 := (abs_le).2 ⟨hbLower, hbUpper.trans (by norm_num)⟩
  have hab : a + b = -2 := by
    dsimp [a, b]
    ring
  have hM := (abs_le.mp primeMertens_abs_le_nine).1
  have habsProduct :
      (|a| + |b|) * ((log 4 + 3) / log 2) ≤ 30 := by
    have habsSum : |a| + |b| ≤ 4 := by linarith
    exact (mul_le_mul habsSum source_product_log_ratio_le
      (by positivity) (by norm_num)).trans_eq (by norm_num)
  have hexponent :
      (a + b) * Mertens.Weight.M (f := Mertens.Weight.prime) +
          (|a| + |b|) * ((log 4 + 3) / log 2) +
          3 + |b| / 2 ≤ 52 := by
    rw [hab]
    nlinarith [habsProduct]
  calc
    mixedLargeProductConstant
          mixedCanonicalAlpha mixedCanonicalBeta mixedCanonicalS ≤
        exp (52 : ℝ) := by
      unfold mixedLargeProductConstant
      dsimp only
      exact exp_le_exp.mpr hexponent
    _ = exp (1 : ℝ) ^ (52 : ℕ) := by
      simpa using (Real.exp_nat_mul (1 : ℝ) 52)
    _ ≤ (4 : ℝ) ^ (52 : ℕ) :=
      pow_le_pow_left₀ (exp_nonneg 1)
        (Real.exp_one_lt_three.le.trans (by norm_num)) 52
    _ = (2 : ℝ) ^ (104 : ℕ) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
    _ ≤ (2 : ℝ) ^ (110 : ℕ) := by norm_num

private theorem mixedSmallProductConstant_le :
    mixedSmallProductConstant ≤ (2 : ℝ) ^ (80 : ℕ) := by
  have hM := (abs_le.mp primeMertens_abs_le_nine).1
  have hexponent :
      -2 * Mertens.Weight.M (f := Mertens.Weight.prime) +
          2 * ((log 4 + 3) / log 2) + 3 ≤ 36 := by
    nlinarith [source_product_log_ratio_le]
  calc
    mixedSmallProductConstant ≤ exp (36 : ℝ) := by
      unfold mixedSmallProductConstant
      exact exp_le_exp.mpr hexponent
    _ = exp (1 : ℝ) ^ (36 : ℕ) := by
      simpa using (Real.exp_nat_mul (1 : ℝ) 36)
    _ ≤ (4 : ℝ) ^ (36 : ℕ) :=
      pow_le_pow_left₀ (exp_nonneg 1)
        (Real.exp_one_lt_three.le.trans (by norm_num)) 36
    _ = (2 : ℝ) ^ (72 : ℕ) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
    _ ≤ (2 : ℝ) ^ (80 : ℕ) := by norm_num

private theorem mixedCanonicalScheduledProductConstant_le :
    mixedCanonicalScheduledProductConstant ≤
      (2 : ℝ) ^ (120 : ℕ) := by
  have hrough0 : 0 ≤ -mixedCanonicalRoughnessExponent :=
    neg_nonneg.mpr mixedCanonicalRoughnessExponent_lt_zero.le
  have hrough2 : -mixedCanonicalRoughnessExponent ≤ 2 := by
    unfold mixedCanonicalRoughnessExponent mixedCanonicalAlpha
      mixedCanonicalBeta mixedCanonicalS
    norm_num [mixedSourceWeightBase, mixedOddWeightBase]
  have hrpow :
      (5 : ℝ) ^ (-mixedCanonicalRoughnessExponent) ≤ 25 := by
    calc
      (5 : ℝ) ^ (-mixedCanonicalRoughnessExponent) ≤
          (5 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hrough2
      _ = 25 := by norm_num [Real.rpow_natCast]
  calc
    mixedCanonicalScheduledProductConstant ≤
        (2 : ℝ) ^ (110 : ℕ) +
          (2 : ℝ) ^ (80 : ℕ) * 25 := by
      unfold mixedCanonicalScheduledProductConstant
      apply add_le_add mixedLargeProductConstant_le
      calc
        mixedSmallProductConstant *
              5 ^ (-mixedCanonicalRoughnessExponent) ≤
            (2 : ℝ) ^ (80 : ℕ) *
              5 ^ (-mixedCanonicalRoughnessExponent) :=
          mul_le_mul_of_nonneg_right mixedSmallProductConstant_le
            (Real.rpow_nonneg (by norm_num) _)
        _ ≤ (2 : ℝ) ^ (80 : ℕ) * 25 :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ ≤ (2 : ℝ) ^ (110 : ℕ) + (2 : ℝ) ^ (110 : ℕ) := by
      gcongr
      norm_num
    _ = (2 : ℝ) ^ (111 : ℕ) := by ring_nf
    _ ≤ (2 : ℝ) ^ (120 : ℕ) := by norm_num

private theorem mixedCanonicalResidualConstant_le :
    mixedCanonicalResidualConstant ≤ (2 : ℝ) ^ (150 : ℕ) := by
  have hfront : 2 * (log (4 : ℝ) + 5) ≤ (16 : ℝ) := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_lt_d9]
  have hexponent :
      mixedCanonicalS * cutoffTailReserve +
          2 * reciprocalPrimeErrorReserve + 38 ≤ 67 := by
    have hs0 : 0 ≤ mixedCanonicalS := mixedCanonicalS_pos.le
    nlinarith [mixedCanonicalS_lt_one.le, cutoffTailReserve_le_fifteen,
      reciprocalPrimeErrorReserve_le_seven]
  have hexp :
      exp (mixedCanonicalS * cutoffTailReserve +
          2 * reciprocalPrimeErrorReserve + 38) ≤
        (2 : ℝ) ^ (134 : ℕ) := by
    calc
      _ ≤ exp (67 : ℝ) := exp_le_exp.mpr hexponent
      _ = exp (1 : ℝ) ^ (67 : ℕ) := by
        simpa using (Real.exp_nat_mul (1 : ℝ) 67)
      _ ≤ (4 : ℝ) ^ (67 : ℕ) :=
        pow_le_pow_left₀ (exp_nonneg 1)
          (Real.exp_one_lt_three.le.trans (by norm_num)) 67
      _ = (2 : ℝ) ^ (134 : ℕ) := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
  unfold mixedCanonicalResidualConstant
  calc
    2 * (log 4 + 5) *
          exp (mixedCanonicalS * cutoffTailReserve +
            2 * reciprocalPrimeErrorReserve + 38) ≤
        16 * (2 : ℝ) ^ (134 : ℕ) := by gcongr
    _ = (2 : ℝ) ^ (138 : ℕ) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← pow_add]
    _ ≤ (2 : ℝ) ^ (150 : ℕ) := by norm_num

private theorem mixedSourceBudgetPower_le :
    mixedSourceWeightBase ^ explicitSourceBudget ≤
      (2 : ℝ) ^ (800000000 : ℕ) := by
  have hbase0 : 0 ≤ mixedSourceWeightBase := by
    norm_num [mixedSourceWeightBase]
  have hbase : mixedSourceWeightBase ≤ (4 : ℝ) := by
    norm_num [mixedSourceWeightBase]
  have hexp0 : 0 ≤ explicitSourceBudget := by
    norm_num [explicitSourceBudget]
  calc
    mixedSourceWeightBase ^ explicitSourceBudget ≤
        (4 : ℝ) ^ explicitSourceBudget :=
      Real.rpow_le_rpow hbase0 hbase hexp0
    _ = (4 : ℝ) ^ (400000000 : ℕ) := by
      norm_num [explicitSourceBudget, Real.rpow_natCast]
    _ = (2 : ℝ) ^ (800000000 : ℕ) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]

private theorem five_rpow_mixedRegularity_le :
    (5 : ℝ) ^ mixedCanonicalRegularityExponent ≤ 25 := by
  calc
    (5 : ℝ) ^ mixedCanonicalRegularityExponent ≤ (5 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        mixedCanonicalRegularityExponent_lt_two.le
    _ = 25 := by norm_num [Real.rpow_natCast]

private theorem mixedCanonicalMainConstant_le :
    mixedCanonicalMainConstant explicitSourceBudget ≤
      (2 : ℝ) ^ (800000300 : ℕ) := by
  unfold mixedCanonicalMainConstant
  have hAB :
      mixedSourceWeightBase ^ explicitSourceBudget *
          5 ^ mixedCanonicalRegularityExponent ≤
        (2 : ℝ) ^ (800000000 : ℕ) * 32 :=
    mul_le_mul mixedSourceBudgetPower_le
      (five_rpow_mixedRegularity_le.trans (by norm_num))
      (Real.rpow_nonneg (by norm_num) _)
      (by positivity)
  calc
    8 * (mixedSourceWeightBase ^ explicitSourceBudget *
          5 ^ mixedCanonicalRegularityExponent) *
          mixedCanonicalScheduledProductConstant *
          mixedCanonicalResidualConstant ≤
        8 * ((2 : ℝ) ^ (800000000 : ℕ) * 32) *
          (2 : ℝ) ^ (120 : ℕ) * (2 : ℝ) ^ (150 : ℕ) := by
      have h1 := mul_le_mul_of_nonneg_left hAB (by norm_num : (0 : ℝ) ≤ 8)
      have h2 := mul_le_mul h1 mixedCanonicalScheduledProductConstant_le
        mixedCanonicalScheduledProductConstant_pos.le (by positivity)
      exact mul_le_mul h2 mixedCanonicalResidualConstant_le
        mixedCanonicalResidualConstant_pos.le (by positivity)
    _ = (2 : ℝ) ^ (800000278 : ℕ) := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num,
        show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num,
        ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    _ ≤ (2 : ℝ) ^ (800000300 : ℕ) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)

private theorem mixedCanonicalErrorConstant_le :
    mixedCanonicalErrorConstant explicitSourceBudget ≤
      (2 : ℝ) ^ (800000200 : ℕ) := by
  unfold mixedCanonicalErrorConstant
  have hAB :
      mixedSourceWeightBase ^ explicitSourceBudget *
          5 ^ mixedCanonicalRegularityExponent ≤
        (2 : ℝ) ^ (800000000 : ℕ) * 32 :=
    mul_le_mul mixedSourceBudgetPower_le
      (five_rpow_mixedRegularity_le.trans (by norm_num))
      (Real.rpow_nonneg (by norm_num) _)
      (by positivity)
  calc
    9 * (mixedSourceWeightBase ^ explicitSourceBudget *
          5 ^ mixedCanonicalRegularityExponent) *
          mixedCanonicalResidualConstant ≤
        16 * ((2 : ℝ) ^ (800000000 : ℕ) * 32) *
          (2 : ℝ) ^ (150 : ℕ) := by
      have h1 := mul_le_mul_of_nonneg_left hAB (by norm_num : (0 : ℝ) ≤ 9)
      have hfront : (9 : ℝ) ≤ 16 := by norm_num
      have h2 := h1.trans
        (mul_le_mul_of_nonneg_right hfront (by positivity))
      exact mul_le_mul h2 mixedCanonicalResidualConstant_le
        mixedCanonicalResidualConstant_pos.le (by positivity)
    _ = (2 : ℝ) ^ (800000159 : ℕ) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
        show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num,
        ← pow_add, ← pow_add, ← pow_add]
    _ ≤ (2 : ℝ) ^ (800000200 : ℕ) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)

private theorem mixedScheduleLogConstant_le :
    mixedScheduleLogConstant ≤ (2 : ℝ) ^ (32 : ℕ) := by
  have hlogPos : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hsq : (1 / 4 : ℝ) ≤ log (2 : ℝ) ^ 2 := by
    nlinarith [log_two_lower_half,
      sq_nonneg (log (2 : ℝ) - 1 / 2)]
  have hquot : 4 / log (2 : ℝ) ^ 2 ≤ (16 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hlogPos)).2
    nlinarith
  unfold mixedScheduleLogConstant
  calc
    (4096 : ℝ) ^ 2 * (4 / log (2 : ℝ) ^ 2) ^ 2 ≤
        (4096 : ℝ) ^ 2 * (16 : ℝ) ^ 2 := by
      gcongr
    _ = (2 : ℝ) ^ (32 : ℕ) := by norm_num

private theorem mixedCanonicalCrossExponent_gt_neg_four :
    (-4 : ℝ) < mixedCanonicalCrossExponent := by
  have hsource :
      0 ≤ sourceAnatomySlope * log mixedSourceWeightBase :=
    mul_nonneg sourceAnatomySlope_nonneg
      (log_pos mixedSourceWeightBase_gt_one).le
  have hodd :
      0 ≤ oddAnatomySlope * log mixedOddWeightBase :=
    mul_nonneg oddAnatomySlope_nonneg
      (log_pos mixedOddWeightBase_gt_one).le
  have hα : 0 < mixedSourceWeightBase⁻¹ := by
    positivity [mixedSourceWeightBase_gt_one]
  have hβ : 0 < mixedOddWeightBase⁻¹ := by
    positivity [mixedOddWeightBase_gt_one]
  have hs : 0 < (mixedSourceWeightBase * mixedOddWeightBase)⁻¹ := by
    positivity [mixedSourceWeightBase_gt_one, mixedOddWeightBase_gt_one]
  unfold mixedCanonicalCrossExponent
  nlinarith

private theorem mixedDyadicIndexConstant_le :
    mixedDyadicIndexConstant ≤ (2 : ℝ) ^ (8 : ℕ) := by
  have hlogPos : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hbase0 : 0 ≤ 2 / log (2 : ℝ) := by positivity
  have hbase : 2 / log (2 : ℝ) ≤ (4 : ℝ) := by
    apply (div_le_iff₀ hlogPos).2
    nlinarith [log_two_lower_half]
  have hexp0 : 0 ≤ -mixedCanonicalCrossExponent := by
    linarith [mixedCanonicalCrossExponent_lt_neg_one]
  have hexp4 : -mixedCanonicalCrossExponent ≤ 4 := by
    linarith [mixedCanonicalCrossExponent_gt_neg_four]
  unfold mixedDyadicIndexConstant
  calc
    (2 / log (2 : ℝ)) ^ (-mixedCanonicalCrossExponent) ≤
        (4 : ℝ) ^ (-mixedCanonicalCrossExponent) :=
      Real.rpow_le_rpow hbase0 hbase hexp0
    _ ≤ (4 : ℝ) ^ (4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp4
    _ = (2 : ℝ) ^ (8 : ℕ) := by
      norm_num [Real.rpow_natCast]

private theorem mixedCanonicalBulkProfileConstant_le :
    mixedCanonicalBulkProfileConstant ≤ (2 : ℝ) ^ (40 : ℕ) := by
  unfold mixedCanonicalBulkProfileConstant
  calc
    mixedDyadicIndexConstant * mixedScheduleLogConstant ≤
        (2 : ℝ) ^ (8 : ℕ) * (2 : ℝ) ^ (32 : ℕ) :=
      mul_le_mul mixedDyadicIndexConstant_le mixedScheduleLogConstant_le
        mixedScheduleLogConstant_pos.le (by positivity)
    _ = (2 : ℝ) ^ (40 : ℕ) := by rw [← pow_add]

private theorem mixedCrossTail_gap :
    (1 / 5000 : ℝ) ≤
      -(mixedCanonicalCrossExponent + mixedBulkLogAbsorption + 1) := by
  unfold mixedCanonicalCrossExponent mixedBulkLogAbsorption
    sourceAnatomySlope oddAnatomySlope
    mixedSourceWeightBase mixedOddWeightBase
  norm_num at ⊢
  nlinarith [Erdos327.log_qb_upper, Erdos327.log_qo_upper]

private theorem mixedBulkPowerTailConstant_le :
    powerTailConstant
        (mixedCanonicalCrossExponent + mixedBulkLogAbsorption) ≤
      (8192 : ℝ) := by
  have hden :
      0 < -(mixedCanonicalCrossExponent + mixedBulkLogAbsorption + 1) :=
    (by norm_num : (0 : ℝ) < 1 / 5000).trans_le mixedCrossTail_gap
  unfold powerTailConstant
  calc
    (-(mixedCanonicalCrossExponent + mixedBulkLogAbsorption + 1))⁻¹ =
        1 / (-(mixedCanonicalCrossExponent + mixedBulkLogAbsorption + 1)) := by
      rw [one_div]
    _ ≤ 1 / (1 / 5000 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) mixedCrossTail_gap
    _ = 5000 := by norm_num
    _ ≤ 8192 := by norm_num

private theorem mixedInverseLogFactor_le :
    (1 / (2 * log 2) : ℝ) ^
        (mixedCanonicalCrossExponent + mixedBulkLogAbsorption + 1) ≤
      (16 : ℝ) := by
  let e : ℝ :=
    mixedCanonicalCrossExponent + mixedBulkLogAbsorption + 1
  have hlogPos : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hbaseLower : (1 / 2 : ℝ) ≤ 1 / (2 * log 2) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hlogPos)).2
    nlinarith [Real.log_two_lt_d9]
  have he0 : e ≤ 0 := by
    dsimp [e]
    linarith [mixedCanonicalCross_add_absorption_lt_neg_one]
  have heLower : (-4 : ℝ) ≤ e := by
    dsimp [e, mixedBulkLogAbsorption]
    linarith [mixedCanonicalCrossExponent_gt_neg_four]
  have hbaseStep :
      (1 / (2 * log 2) : ℝ) ^ e ≤ (1 / 2 : ℝ) ^ e :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hbaseLower he0
  calc
    (1 / (2 * log 2) : ℝ) ^
          (mixedCanonicalCrossExponent + mixedBulkLogAbsorption + 1) =
        (1 / (2 * log 2) : ℝ) ^ e := by rfl
    _ ≤ (1 / 2 : ℝ) ^ e := hbaseStep
    _ ≤ (1 / 2 : ℝ) ^ (-4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) heLower
    _ = 16 := by
      rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num [Real.rpow_natCast]

private theorem mixedBulkMovingTailConstant_le :
    mixedBulkMovingTailConstant ≤ (2 : ℝ) ^ (60 : ℕ) := by
  unfold mixedBulkMovingTailConstant
  have htail :
      powerTailConstant
          (mixedCanonicalCrossExponent + mixedBulkLogAbsorption) ≤
        (2 : ℝ) ^ (13 : ℕ) :=
    mixedBulkPowerTailConstant_le.trans (by norm_num)
  have hinverse :
      (1 / (2 * log 2)) ^
          (mixedCanonicalCrossExponent + mixedBulkLogAbsorption + 1) ≤
        (2 : ℝ) ^ (4 : ℕ) :=
    mixedInverseLogFactor_le.trans_eq (by norm_num)
  calc
    mixedCanonicalBulkProfileConstant *
          powerTailConstant
            (mixedCanonicalCrossExponent + mixedBulkLogAbsorption) *
          (1 / (2 * log 2)) ^
            (mixedCanonicalCrossExponent + mixedBulkLogAbsorption + 1) ≤
        (2 : ℝ) ^ (40 : ℕ) * (2 : ℝ) ^ (13 : ℕ) *
          (2 : ℝ) ^ (4 : ℕ) := by
      have h1 := mul_le_mul mixedCanonicalBulkProfileConstant_le
        htail
        (powerTailConstant_pos
          mixedCanonicalCross_add_absorption_lt_neg_one).le
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (40 : ℕ))
      exact mul_le_mul h1 hinverse
        (Real.rpow_nonneg (by positivity) _)
        (by positivity)
    _ = (2 : ℝ) ^ (57 : ℕ) := by
      rw [← pow_add, ← pow_add]
    _ ≤ (2 : ℝ) ^ (60 : ℕ) := by norm_num

private theorem mixedMainMovingConstant_le :
    mixedCanonicalMainConstant explicitSourceBudget *
        mixedBulkMovingTailConstant ≤
      (2 : ℝ) ^ (800000360 : ℕ) := by
  calc
    mixedCanonicalMainConstant explicitSourceBudget *
          mixedBulkMovingTailConstant ≤
        (2 : ℝ) ^ (800000300 : ℕ) * (2 : ℝ) ^ (60 : ℕ) :=
      mul_le_mul mixedCanonicalMainConstant_le
        mixedBulkMovingTailConstant_le mixedBulkMovingTailConstant_pos.le
        (by positivity)
    _ = (2 : ℝ) ^ (800000360 : ℕ) := by rw [← pow_add]

private theorem mixedMainMovingConstant_le_scale :
    mixedCanonicalMainConstant explicitSourceBudget *
        mixedBulkMovingTailConstant ≤
      (2 : ℝ) ^ (explicitScale / 2) :=
  mixedMainMovingConstant_le.trans
    (pow_le_pow_right₀ (by norm_num) (by norm_num [explicitScale]))

private theorem mixedErrorConstant_le_scale :
    mixedCanonicalErrorConstant explicitSourceBudget ≤
      (2 : ℝ) ^ (explicitScale / 2) :=
  mixedCanonicalErrorConstant_le.trans
    (pow_le_pow_right₀ (by norm_num) (by norm_num [explicitScale]))

private theorem mixedBulkCoefficient_gap :
    (1 / 10000 : ℝ) ≤
      (2 - oddBudgetSlope * log mixedOddWeightBase -
        mixedBulkLogAbsorption) - 1 := by
  unfold oddBudgetSlope mixedOddWeightBase mixedBulkLogAbsorption
  norm_num at ⊢
  nlinarith [Erdos327.log_qo_upper]

private theorem mixedErrorCoefficient_gap :
    (1 / 10000 : ℝ) ≤
      (mixedCanonicalRegularityExponent + 1 -
        oddBudgetSlope * log mixedOddWeightBase) - 1 := by
  have hqb :
      log (2 : ℝ) < log mixedSourceWeightBase :=
    Real.strictMonoOn_log (by norm_num)
      (by
        simpa only [Set.mem_Ioi] using
          (show (0 : ℝ) < mixedSourceWeightBase by
            norm_num [mixedSourceWeightBase]))
      (by norm_num [mixedSourceWeightBase])
  unfold mixedCanonicalRegularityExponent sourceAnatomySlope
    oddAnatomySlope oddBudgetSlope mixedOddWeightBase
  norm_num at ⊢
  nlinarith [Real.log_two_gt_d9, Erdos327.log_qo_upper]

private theorem explicit_sum_mixedCanonicalBulkMain_le_moving
    (N M : ℕ) :
    (∑ j ∈ range M,
      mixedCanonicalBulkMainContribution
        explicitL N explicitSourceBudget (oddBudget explicitL) j) ≤
      mixedCanonicalMainConstant explicitSourceBudget *
        mixedOddWeightBase ^ oddBudget explicitL * (N : ℝ) *
        mixedBulkMovingTailConstant *
        log (explicitL : ℝ) ^ (-2 + mixedBulkLogAbsorption) := by
  have hL : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  have hlogNat : 9 ≤ Nat.log 2 explicitL := by
    rw [natLog_two_explicitL]
    have hJ : 64 ≤ explicitJ := explicitJ_ge_sixty_four
    omega
  have hstart1 : 1 ≤ mixedBulkMovingStart explicitL := by
    rw [mixedBulkMovingStart_explicitL]
    have hJ : 64 ≤ explicitJ := explicitJ_ge_sixty_four
    omega
  let C : ℝ :=
    mixedCanonicalMainConstant explicitSourceBudget *
      mixedOddWeightBase ^ oddBudget explicitL * (N : ℝ) *
      log (explicitL : ℝ) ^ mixedCanonicalOuterExponent
  have hlogL : 0 < log (explicitL : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < explicitL by omega))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mixedCanonicalMainConstant_pos explicitSourceBudget).le
          (Real.rpow_nonneg
            (by linarith [mixedOddWeightBase_gt_one]) _))
        (Nat.cast_nonneg N))
      (Real.rpow_nonneg hlogL.le _)
  have hpoint :
      ∀ j : ℕ,
        mixedCanonicalBulkMainContribution
            explicitL N explicitSourceBudget (oddBudget explicitL) j ≤
          if explicitL ≤ 16 * dyadicScale j then
            C * mixedCanonicalBulkProfileConstant *
              ((((j + 1 : ℕ) : ℝ) ^
                  mixedCanonicalCrossExponent) *
                log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ))
          else 0 := by
    intro j
    by_cases hnear : explicitL ≤ 16 * dyadicScale j
    · rw [if_pos hnear]
      unfold mixedCanonicalBulkMainContribution
      split_ifs with hj
      · rcases hj with ⟨hdom, _hnear, hgood, hbulk⟩
        simpa [C, mul_assoc] using
          (mixedCanonicalGoodBulkMainBlock_le_profile
            (Kb := explicitSourceBudget) (Ko := oddBudget explicitL)
            hL hdom hnear hgood hbulk)
      · exact mul_nonneg
          (mul_nonneg hC0 mixedCanonicalBulkProfileConstant_pos.le)
          (mul_nonneg
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
            (Real.rpow_nonneg (Real.log_natCast_nonneg _) _))
    · rw [if_neg hnear]
      unfold mixedCanonicalBulkMainContribution
      rw [if_neg (by
        intro hj
        exact hnear hj.2.1)]
  have hprofile :
      (∑ j ∈ range M,
          if explicitL ≤ 16 * dyadicScale j then
            (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)
          else 0) ≤
        ∑ j ∈ Ico (mixedBulkMovingStart explicitL) M,
          (((j + 1 : ℕ) : ℝ) ^
            (mixedCanonicalCrossExponent + mixedBulkLogAbsorption)) := by
    calc
      _ =
          ∑ j ∈ (range M).filter
              (fun j ↦ explicitL ≤ 16 * dyadicScale j),
            (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) := by
          rw [sum_filter]
      _ ≤
          ∑ j ∈ (range M).filter
              (fun j ↦ explicitL ≤ 16 * dyadicScale j),
            (((j + 1 : ℕ) : ℝ) ^
              (mixedCanonicalCrossExponent + mixedBulkLogAbsorption)) := by
          apply sum_le_sum
          intro j hj
          exact explicit_mixedBulkProfile_absorbed
            (mixedBulkMovingStart_le_of_near
              (mem_filter.mp hj).2)
      _ ≤
          ∑ j ∈ Ico (mixedBulkMovingStart explicitL) M,
            (((j + 1 : ℕ) : ℝ) ^
              (mixedCanonicalCrossExponent + mixedBulkLogAbsorption)) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro j hj
            rw [mem_filter] at hj
            exact mem_Ico.mpr
              ⟨mixedBulkMovingStart_le_of_near hj.2,
                mem_range.mp hj.1⟩
          · intro j hjIco hjNot
            exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have htail :=
    sum_Ico_add_one_rpow_le
      mixedCanonicalCross_add_absorption_lt_neg_one hstart1
      (M := M)
  have hlogStart :=
    log_div_le_mixedBulkMovingStart hL hlogNat
  have hexpNeg :
      mixedCanonicalCrossExponent +
          mixedBulkLogAbsorption + 1 < 0 := by
    linarith [mixedCanonicalCross_add_absorption_lt_neg_one]
  have hlogRatio :
      0 < log (explicitL : ℝ) / (2 * log 2) := by
    positivity [log_pos (by norm_num : (1 : ℝ) < 2)]
  have hinvLogTwoPos :
      0 < (1 / (2 * log 2) : ℝ) := by
    positivity [log_pos (by norm_num : (1 : ℝ) < 2)]
  have hstartPower :
      (mixedBulkMovingStart explicitL : ℝ) ^
          (mixedCanonicalCrossExponent +
            mixedBulkLogAbsorption + 1) ≤
        (1 / (2 * log 2)) ^
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1) *
          log (explicitL : ℝ) ^
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1) := by
    have hanti :=
      Real.rpow_le_rpow_of_nonpos
        hlogRatio hlogStart hexpNeg.le
    calc
      (mixedBulkMovingStart explicitL : ℝ) ^
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1)
          ≤
        (log (explicitL : ℝ) / (2 * log 2)) ^
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1) := hanti
      _ =
        (1 / (2 * log 2)) ^
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1) *
          log (explicitL : ℝ) ^
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1) := by
        rw [show log (explicitL : ℝ) / (2 * log 2) =
            (1 / (2 * log 2)) * log (explicitL : ℝ) by ring,
          Real.mul_rpow hinvLogTwoPos.le hlogL.le]
  have hout :
      mixedCanonicalOuterExponent +
          (mixedCanonicalCrossExponent +
            mixedBulkLogAbsorption + 1) =
        -2 + mixedBulkLogAbsorption := by
    calc
      mixedCanonicalOuterExponent +
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1) =
          (mixedCanonicalOuterExponent +
            (mixedCanonicalDyadicExponent +
              mixedCanonicalResidualExponent + 1)) +
            mixedBulkLogAbsorption := by
              rw [← mixedCanonicalDyadic_add_residualExponent]
              ring
      _ = -2 + mixedBulkLogAbsorption := by
        rw [mixedCanonicalExponent_ledger]
  calc
    (∑ j ∈ range M,
        mixedCanonicalBulkMainContribution
          explicitL N explicitSourceBudget (oddBudget explicitL) j)
        ≤
      ∑ j ∈ range M,
        if explicitL ≤ 16 * dyadicScale j then
          C * mixedCanonicalBulkProfileConstant *
            ((((j + 1 : ℕ) : ℝ) ^
                mixedCanonicalCrossExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ))
        else 0 := by
          apply sum_le_sum
          intro j hj
          exact hpoint j
    _ =
      (C * mixedCanonicalBulkProfileConstant) *
        (∑ j ∈ range M,
          if explicitL ≤ 16 * dyadicScale j then
            (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)
          else 0) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        split_ifs <;> ring
    _ ≤
      (C * mixedCanonicalBulkProfileConstant) *
        (∑ j ∈ Ico (mixedBulkMovingStart explicitL) M,
          (((j + 1 : ℕ) : ℝ) ^
            (mixedCanonicalCrossExponent + mixedBulkLogAbsorption))) :=
      mul_le_mul_of_nonneg_left hprofile
        (mul_nonneg hC0 mixedCanonicalBulkProfileConstant_pos.le)
    _ ≤
      (C * mixedCanonicalBulkProfileConstant) *
        (powerTailConstant
            (mixedCanonicalCrossExponent + mixedBulkLogAbsorption) *
          (mixedBulkMovingStart explicitL : ℝ) ^
            (mixedCanonicalCrossExponent +
              mixedBulkLogAbsorption + 1)) :=
      mul_le_mul_of_nonneg_left htail
        (mul_nonneg hC0 mixedCanonicalBulkProfileConstant_pos.le)
    _ ≤
      (C * mixedCanonicalBulkProfileConstant) *
        (powerTailConstant
            (mixedCanonicalCrossExponent + mixedBulkLogAbsorption) *
          ((1 / (2 * log 2)) ^
              (mixedCanonicalCrossExponent +
                mixedBulkLogAbsorption + 1) *
            log (explicitL : ℝ) ^
              (mixedCanonicalCrossExponent +
                mixedBulkLogAbsorption + 1))) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg hC0 mixedCanonicalBulkProfileConstant_pos.le)
      exact mul_le_mul_of_nonneg_left hstartPower
        (powerTailConstant_pos
          mixedCanonicalCross_add_absorption_lt_neg_one).le
    _ =
      mixedCanonicalMainConstant explicitSourceBudget *
          mixedOddWeightBase ^ oddBudget explicitL * (N : ℝ) *
          mixedBulkMovingTailConstant *
          log (explicitL : ℝ) ^ (-2 + mixedBulkLogAbsorption) := by
      unfold C mixedBulkMovingTailConstant
      have hlogCombine :
          log (explicitL : ℝ) ^ mixedCanonicalOuterExponent *
              log (explicitL : ℝ) ^
                (mixedCanonicalCrossExponent +
                  mixedBulkLogAbsorption + 1) =
            log (explicitL : ℝ) ^ (-2 + mixedBulkLogAbsorption) := by
        rw [← Real.rpow_add hlogL, hout]
      rw [show
        mixedCanonicalMainConstant explicitSourceBudget *
              mixedOddWeightBase ^ oddBudget explicitL * (N : ℝ) *
              log (explicitL : ℝ) ^ mixedCanonicalOuterExponent *
              mixedCanonicalBulkProfileConstant *
              (powerTailConstant
                  (mixedCanonicalCrossExponent +
                    mixedBulkLogAbsorption) *
                ((1 / (2 * log 2)) ^
                    (mixedCanonicalCrossExponent +
                      mixedBulkLogAbsorption + 1) *
                  log (explicitL : ℝ) ^
                    (mixedCanonicalCrossExponent +
                      mixedBulkLogAbsorption + 1))) =
            (mixedCanonicalMainConstant explicitSourceBudget *
              mixedOddWeightBase ^ oddBudget explicitL * (N : ℝ) *
              mixedCanonicalBulkProfileConstant *
              powerTailConstant
                (mixedCanonicalCrossExponent +
                  mixedBulkLogAbsorption) *
              (1 / (2 * log 2)) ^
                (mixedCanonicalCrossExponent +
                  mixedBulkLogAbsorption + 1)) *
              (log (explicitL : ℝ) ^ mixedCanonicalOuterExponent *
                log (explicitL : ℝ) ^
                  (mixedCanonicalCrossExponent +
                    mixedBulkLogAbsorption + 1)) by ring,
        hlogCombine]
      ring


private theorem explicit_mixedBulkMovingCoefficient_le :
    mixedCanonicalMainConstant explicitSourceBudget *
        mixedBulkMovingTailConstant *
        mixedOddWeightBase ^ oddBudget explicitL *
        log (explicitL : ℝ) ^ (-2 + mixedBulkLogAbsorption) ≤
      roughDensity explicitL / 512 := by
  let η : ℝ :=
    2 - oddBudgetSlope * log mixedOddWeightBase -
      mixedBulkLogAbsorption
  have hC0 :
      0 ≤ mixedCanonicalMainConstant explicitSourceBudget *
        mixedBulkMovingTailConstant :=
    mul_nonneg (mixedCanonicalMainConstant_pos _).le
      mixedBulkMovingTailConstant_pos.le
  have hbase := explicit_const_mul_log_rpow_le_roughDensity
    (C := mixedCanonicalMainConstant explicitSourceBudget *
      mixedBulkMovingTailConstant)
    (D := (512 : ℝ)) (η := η) hC0 mixedMainMovingConstant_le_scale
    (by norm_num) (by norm_num) (by
      dsimp [η]
      exact mixedBulkCoefficient_gap)
  have hL : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  have hLreal : (1 : ℝ) < explicitL :=
    (by norm_num : (1 : ℝ) < 3).trans_le (Nat.cast_le.2 hL)
  have hlogL : 0 < log (explicitL : ℝ) := log_pos hLreal
  rw [oddBudget, base_rpow_mul_loglog
    (by linarith [mixedOddWeightBase_gt_one]) hLreal]
  have hcombine :
      log (explicitL : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (explicitL : ℝ) ^ (-2 + mixedBulkLogAbsorption) =
        log (explicitL : ℝ) ^ (-η) := by
    rw [← Real.rpow_add hlogL]
    congr 1
    dsimp [η]
    ring
  calc
    mixedCanonicalMainConstant explicitSourceBudget *
          mixedBulkMovingTailConstant *
          log (explicitL : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (explicitL : ℝ) ^ (-2 + mixedBulkLogAbsorption) =
        (mixedCanonicalMainConstant explicitSourceBudget *
          mixedBulkMovingTailConstant) *
          (log (explicitL : ℝ) ^
              (oddBudgetSlope * log mixedOddWeightBase) *
            log (explicitL : ℝ) ^
              (-2 + mixedBulkLogAbsorption)) := by ring
    _ = (mixedCanonicalMainConstant explicitSourceBudget *
          mixedBulkMovingTailConstant) *
        log (explicitL : ℝ) ^ (-η) := by rw [hcombine]
    _ ≤ roughDensity explicitL / 512 := hbase

theorem explicit_sum_mixedCanonicalBulkMain_le_roughDensity
    (N M : ℕ) :
    (∑ j ∈ range M,
      mixedCanonicalBulkMainContribution
        explicitL N explicitSourceBudget (oddBudget explicitL) j) ≤
      (N : ℝ) * roughDensity explicitL / 512 := by
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  calc
    _ ≤ mixedCanonicalMainConstant explicitSourceBudget *
          mixedOddWeightBase ^ oddBudget explicitL * (N : ℝ) *
          mixedBulkMovingTailConstant *
          log (explicitL : ℝ) ^ (-2 + mixedBulkLogAbsorption) :=
      explicit_sum_mixedCanonicalBulkMain_le_moving N M
    _ = (N : ℝ) *
        (mixedCanonicalMainConstant explicitSourceBudget *
          mixedBulkMovingTailConstant *
          mixedOddWeightBase ^ oddBudget explicitL *
          log (explicitL : ℝ) ^
            (-2 + mixedBulkLogAbsorption)) := by ring
    _ ≤ (N : ℝ) * (roughDensity explicitL / 512) :=
      mul_le_mul_of_nonneg_left explicit_mixedBulkMovingCoefficient_le hN0
    _ = (N : ℝ) * roughDensity explicitL / 512 := by ring

private theorem explicit_mixedErrorCoefficient_le :
    mixedCanonicalErrorConstant explicitSourceBudget *
        mixedOddWeightBase ^ oddBudget explicitL *
        log (explicitL : ℝ) ^ mixedCanonicalErrorOuterExponent ≤
      roughDensity explicitL / 512 := by
  let η : ℝ :=
    mixedCanonicalRegularityExponent + 1 -
      oddBudgetSlope * log mixedOddWeightBase
  have hC0 : 0 ≤ mixedCanonicalErrorConstant explicitSourceBudget :=
    (mixedCanonicalErrorConstant_pos _).le
  have hbase := explicit_const_mul_log_rpow_le_roughDensity
    (C := mixedCanonicalErrorConstant explicitSourceBudget)
    (D := (512 : ℝ)) (η := η) hC0 mixedErrorConstant_le_scale
    (by norm_num) (by norm_num) (by
      dsimp [η]
      exact mixedErrorCoefficient_gap)
  have hL : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  have hLreal : (1 : ℝ) < explicitL :=
    (by norm_num : (1 : ℝ) < 3).trans_le (Nat.cast_le.2 hL)
  have hlogL : 0 < log (explicitL : ℝ) := log_pos hLreal
  rw [oddBudget, base_rpow_mul_loglog
    (by linarith [mixedOddWeightBase_gt_one]) hLreal]
  have hcombine :
      log (explicitL : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (explicitL : ℝ) ^ mixedCanonicalErrorOuterExponent =
        log (explicitL : ℝ) ^ (-η) := by
    rw [← Real.rpow_add hlogL]
    congr 1
    unfold mixedCanonicalErrorOuterExponent
    dsimp [η]
    ring
  calc
    mixedCanonicalErrorConstant explicitSourceBudget *
          log (explicitL : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (explicitL : ℝ) ^ mixedCanonicalErrorOuterExponent =
        mixedCanonicalErrorConstant explicitSourceBudget *
          (log (explicitL : ℝ) ^
              (oddBudgetSlope * log mixedOddWeightBase) *
            log (explicitL : ℝ) ^ mixedCanonicalErrorOuterExponent) := by
      ring
    _ = mixedCanonicalErrorConstant explicitSourceBudget *
        log (explicitL : ℝ) ^ (-η) := by rw [hcombine]
    _ ≤ roughDensity explicitL / 512 := hbase

private theorem dyadicScale_pred_lt_sourceCoupledCutoff
    (J : ℕ) (hJ : 1 ≤ J) :
    dyadicScale (J - 1) < sourceCoupledCutoff J := by
  have hmono : dyadicScale (J - 1) ≤ dyadicScale J :=
    dyadicScale_mono (Nat.sub_le J 1)
  have hpos : 0 < dyadicScale J := by
    unfold dyadicScale
    positivity
  have hlt : dyadicScale J < 8 * dyadicScale J := by omega
  exact hmono.trans_lt <|
    hlt.trans (eight_dyadicScale_lt_sourceCoupledCutoff J)

private theorem explicit_mixedErrorProfile_tail_le_one (M : ℕ) :
    (∑ j ∈ Ico (mixedBulkMovingStart explicitL) M,
      (((j + 1 : ℕ) : ℝ) ^ 2) /
        (((j + 1 : ℕ) : ℝ) ^ 8)) ≤ 1 := by
  have hstart1 : 1 ≤ mixedBulkMovingStart explicitL := by
    rw [mixedBulkMovingStart_explicitL]
    have hJ : 64 ≤ explicitJ := explicitJ_ge_sixty_four
    omega
  have htail := sum_Ico_add_one_rpow_le
    (r := (-6 : ℝ)) (by norm_num) hstart1 (M := M)
  have hstartReal :
      (1 : ℝ) ≤ (mixedBulkMovingStart explicitL : ℝ) := by
    exact_mod_cast hstart1
  have hpower :
      (mixedBulkMovingStart explicitL : ℝ) ^ (-6 + 1 : ℝ) ≤ 1 := by
    calc
      (mixedBulkMovingStart explicitL : ℝ) ^ (-6 + 1 : ℝ) ≤
          (1 : ℝ) ^ (-6 + 1 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hstartReal (by norm_num)
      _ = 1 := by norm_num
  calc
    (∑ j ∈ Ico (mixedBulkMovingStart explicitL) M,
        (((j + 1 : ℕ) : ℝ) ^ 2) /
          (((j + 1 : ℕ) : ℝ) ^ 8)) =
      ∑ j ∈ Ico (mixedBulkMovingStart explicitL) M,
        (((j + 1 : ℕ) : ℝ) ^ (-6 : ℝ)) := by
      apply sum_congr rfl
      intro j hj
      simpa using (mixedCanonicalErrorProfile_eq j).symm
    _ ≤ powerTailConstant (-6 : ℝ) *
        (mixedBulkMovingStart explicitL : ℝ) ^ (-6 + 1 : ℝ) := htail
    _ ≤ powerTailConstant (-6 : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hpower
        (powerTailConstant_pos (by norm_num)).le
    _ ≤ 1 := by norm_num [powerTailConstant]

theorem explicit_sum_mixedCanonicalGoodSieveError_le_roughDensity
    (N M : ℕ) :
    (∑ j ∈ range M,
      mixedCanonicalGoodSieveErrorContribution
        explicitL N explicitSourceBudget (oddBudget explicitL) j) ≤
      (N : ℝ) * roughDensity explicitL / 512 := by
  have hL : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  have hstart1 : 1 ≤ mixedBulkMovingStart explicitL := by
    rw [mixedBulkMovingStart_explicitL]
    have hJ : 64 ≤ explicitJ := explicitJ_ge_sixty_four
    omega
  have hfar :
      dyadicScale (mixedBulkMovingStart explicitL) < explicitL := by
    rw [mixedBulkMovingStart_explicitL]
    exact dyadicScale_pred_lt_sourceCoupledCutoff explicitJ
      ((by omega : 1 ≤ 64).trans explicitJ_ge_sixty_four)
  let C : ℝ :=
    mixedCanonicalErrorConstant explicitSourceBudget *
      mixedOddWeightBase ^ oddBudget explicitL * (N : ℝ) *
      log (explicitL : ℝ) ^ mixedCanonicalErrorOuterExponent
  have hlogL : 0 < log (explicitL : ℝ) :=
    log_pos ((by norm_num : (1 : ℝ) < 3).trans_le (Nat.cast_le.2 hL))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mixedCanonicalErrorConstant_pos _).le
          (Real.rpow_nonneg
            (by linarith [mixedOddWeightBase_gt_one]) _))
        (Nat.cast_nonneg N))
      (Real.rpow_nonneg hlogL.le _)
  have hpoint :
      ∀ j : ℕ,
        mixedCanonicalGoodSieveErrorContribution
            explicitL N explicitSourceBudget (oddBudget explicitL) j ≤
          C * ((((j + 1 : ℕ) : ℝ) ^ 2) /
            (((j + 1 : ℕ) : ℝ) ^ 8)) := by
    intro j
    unfold mixedCanonicalGoodSieveErrorContribution
    split_ifs with hgood
    · simpa [C, mul_assoc] using
        (mixedCanonicalGoodSieveErrorBlock_le_profile
          (Kb := explicitSourceBudget) (Ko := oddBudget explicitL)
          hL hgood)
    · exact mul_nonneg hC0
        (div_nonneg (sq_nonneg _)
          (pow_nonneg (Nat.cast_nonneg _) _))
  have htail :
      (∑ j ∈ Ico (mixedBulkMovingStart explicitL) M,
        mixedCanonicalGoodSieveErrorContribution
          explicitL N explicitSourceBudget (oddBudget explicitL) j) ≤ C := by
    calc
      _ ≤ ∑ j ∈ Ico (mixedBulkMovingStart explicitL) M,
          C * ((((j + 1 : ℕ) : ℝ) ^ 2) /
            (((j + 1 : ℕ) : ℝ) ^ 8)) := by
        apply sum_le_sum
        intro j hj
        exact hpoint j
      _ = C * (∑ j ∈ Ico (mixedBulkMovingStart explicitL) M,
          (((j + 1 : ℕ) : ℝ) ^ 2) /
            (((j + 1 : ℕ) : ℝ) ^ 8)) := by rw [mul_sum]
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left
        (explicit_mixedErrorProfile_tail_le_one M) hC0
      _ = C := by ring
  have hsum :
      (∑ j ∈ range M,
        mixedCanonicalGoodSieveErrorContribution
          explicitL N explicitSourceBudget (oddBudget explicitL) j) ≤ C := by
    by_cases hstartM : mixedBulkMovingStart explicitL ≤ M
    · have hprefix := mixedCanonicalGoodSieveError_prefix_eq_zero
        (L := explicitL) (N := N) (J := mixedBulkMovingStart explicitL)
        (Kb := explicitSourceBudget) hfar
      calc
        _ = (∑ j ∈ range (mixedBulkMovingStart explicitL),
              mixedCanonicalGoodSieveErrorContribution
                explicitL N explicitSourceBudget (oddBudget explicitL) j) +
            ∑ j ∈ Ico (mixedBulkMovingStart explicitL) M,
              mixedCanonicalGoodSieveErrorContribution
                explicitL N explicitSourceBudget (oddBudget explicitL) j :=
          (sum_range_add_sum_Ico _ hstartM).symm
        _ = ∑ j ∈ Ico (mixedBulkMovingStart explicitL) M,
              mixedCanonicalGoodSieveErrorContribution
                explicitL N explicitSourceBudget (oddBudget explicitL) j := by
          rw [hprefix, zero_add]
        _ ≤ C := htail
    · have hzero :
          (∑ j ∈ range M,
            mixedCanonicalGoodSieveErrorContribution
              explicitL N explicitSourceBudget (oddBudget explicitL) j) = 0 := by
        apply sum_eq_zero
        intro j hj
        unfold mixedCanonicalGoodSieveErrorContribution
        rw [if_neg]
        intro hgood
        have hjStart : j ≤ mixedBulkMovingStart explicitL := by
          have hjM := mem_range.mp hj
          omega
        have hscale :
            dyadicScale j ≤ dyadicScale (mixedBulkMovingStart explicitL) :=
          dyadicScale_mono hjStart
        exact (Nat.not_le_of_gt (hscale.trans_lt hfar)) hgood.2.1
      rw [hzero]
      exact hC0
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  calc
    _ ≤ C := hsum
    _ = (N : ℝ) *
        (mixedCanonicalErrorConstant explicitSourceBudget *
          mixedOddWeightBase ^ oddBudget explicitL *
          log (explicitL : ℝ) ^ mixedCanonicalErrorOuterExponent) := by
      dsimp [C]
      ring
    _ ≤ (N : ℝ) * (roughDensity explicitL / 512) :=
      mul_le_mul_of_nonneg_left explicit_mixedErrorCoefficient_le hN0
    _ = (N : ℝ) * roughDensity explicitL / 512 := by ring

private theorem tiny_le_mixedTerminalLogAbsorption :
    (1 / 10000 : ℝ) ≤ mixedTerminalLogAbsorption := by
  unfold mixedTerminalLogAbsorption
  have hgap := mixedCrossTail_gap
  have habs := mixedBulkLogAbsorption_pos
  nlinarith

private theorem explicit_mixedTerminalProfile_absorbed
    {j : ℕ} (hj : mixedBulkMovingStart explicitL ≤ j) :
    (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) *
        log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) ≤
      (((j + 1 : ℕ) : ℝ) ^
        mixedTerminalAbsorbedDyadicExponent) := by
  have hJsucc : explicitJ ≤ j + 1 := by
    rw [mixedBulkMovingStart_explicitL] at hj
    have hJ1 : 1 ≤ explicitJ :=
      (by omega : 1 ≤ 64).trans explicitJ_ge_sixty_four
    omega
  have hlog := explicit_log_rpow_le_tiny_of_succ hJsucc
    (m := (4 : ℝ)) (by norm_num) (by norm_num)
  have hx : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos j
  calc
    _ ≤ (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) *
        (((j + 1 : ℕ) : ℝ) ^ mixedTerminalLogAbsorption) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
      exact hlog.trans <|
        Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))
          tiny_le_mixedTerminalLogAbsorption
    _ = _ := by
      rw [← Real.rpow_add hx]
      rfl

theorem explicit_exists_forall_sum_mixedCanonicalTerminalMain_le_roughDensity :
    ∃ Nt : ℕ, ∀ N ≥ Nt, ∀ M : ℕ,
      (∑ j ∈ range M,
        mixedCanonicalTerminalMainContribution
          explicitL N explicitSourceBudget (oddBudget explicitL) j) ≤
        (N : ℝ) * roughDensity explicitL / 512 := by
  have hL : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  have hstart :
      mixedBulkMovingStart explicitL ≤ mixedBulkMovingStart explicitL :=
    le_rfl
  have hH :
      ∀ j ≥ mixedBulkMovingStart explicitL,
        (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) ≤
          (((j + 1 : ℕ) : ℝ) ^
            mixedTerminalAbsorbedDyadicExponent) :=
    fun j hj ↦ explicit_mixedTerminalProfile_absorbed hj
  let C₀ : ℝ :=
    mixedCanonicalMainConstant explicitSourceBudget *
      mixedOddWeightBase ^ oddBudget explicitL *
      log (explicitL : ℝ) ^ mixedCanonicalOuterExponent *
      mixedCanonicalTerminalProfileConstant *
      mixedTerminalConvolutionConstant
  have hpower := tendsto_mixedTerminalConvolutionPower_zero
  have hscaled :
      Tendsto
        (fun N : ℕ ↦
          C₀ * (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
            (mixedTerminalAbsorbedDyadicExponent +
              mixedCanonicalResidualExponent + 1)))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hpower)
  have htarget :
      0 < roughDensity explicitL / 512 :=
    div_pos (roughDensity_pos hL) (by norm_num)
  have hevent :=
    (tendsto_order.1 hscaled).2
      (roughDensity explicitL / 512) htarget
  rcases eventually_atTop.1 hevent with ⟨Nt, hNt⟩
  refine ⟨Nt, ?_⟩
  intro N hNN M
  have hN := hNt N hNN
  let C : ℝ :=
    mixedCanonicalMainConstant explicitSourceBudget *
      mixedOddWeightBase ^ oddBudget explicitL * (N : ℝ) *
      log (explicitL : ℝ) ^ mixedCanonicalOuterExponent *
      mixedCanonicalTerminalProfileConstant
  have hC0 : 0 ≤ C := by
    dsimp [C]
    have hlogL :
        0 < log (explicitL : ℝ) :=
      log_pos (by exact_mod_cast (show 1 < explicitL by omega))
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mixedCanonicalMainConstant_pos explicitSourceBudget).le
            (Real.rpow_nonneg
              (by linarith [mixedOddWeightBase_gt_one]) _))
          (Nat.cast_nonneg N))
        (Real.rpow_nonneg hlogL.le _))
      mixedCanonicalTerminalProfileConstant_pos.le
  have hsumEq :
      (∑ j ∈ range M,
          mixedCanonicalTerminalMainContribution
            explicitL N explicitSourceBudget (oddBudget explicitL) j) =
        ∑ j ∈ mixedCanonicalTerminalIndexSet explicitL N M,
          mixedCanonicalTerminalMainContribution
            explicitL N explicitSourceBudget (oddBudget explicitL) j := by
    unfold mixedCanonicalTerminalIndexSet
      mixedCanonicalTerminalMainContribution
    rw [sum_filter]
    apply sum_congr rfl
    intro j hj
    by_cases hp :
        32 * sieveRadius j ≤ j ∧
          explicitL ≤ 16 * dyadicScale j ∧
          mixedScheduledGoodIndex explicitL N j ∧
          N / (dyadicScale j * dyadicScale j) < dyadicScale j
    · rw [if_pos hp, if_pos hp]
    · rw [if_neg hp, if_neg hp]
  have hpoint :
      ∀ j : ℕ,
        mixedCanonicalTerminalMainContribution
            explicitL N explicitSourceBudget (oddBudget explicitL) j ≤
          C *
            ((((j + 1 : ℕ) : ℝ) ^
                mixedCanonicalDyadicExponent) *
              (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
                mixedCanonicalResidualExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
    intro j
    simpa [C, mul_assoc] using
      (mixedCanonicalTerminalMainContribution_le_profile
        (L := explicitL) (N := N) (j := j)
        (Kb := explicitSourceBudget) (Ko := oddBudget explicitL) hL)
  have hprofile :=
    sum_mixedTerminalIndexSet_profile_le
      (L := explicitL) (N := N) (M := M) hL hstart hH
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  calc
    (∑ j ∈ range M,
        mixedCanonicalTerminalMainContribution
          explicitL N explicitSourceBudget (oddBudget explicitL) j) =
      ∑ j ∈ mixedCanonicalTerminalIndexSet explicitL N M,
        mixedCanonicalTerminalMainContribution
          explicitL N explicitSourceBudget (oddBudget explicitL) j := hsumEq
    _ ≤
      ∑ j ∈ mixedCanonicalTerminalIndexSet explicitL N M,
        C *
          ((((j + 1 : ℕ) : ℝ) ^
              mixedCanonicalDyadicExponent) *
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
      apply sum_le_sum
      intro j hj
      exact hpoint j
    _ =
      C *
        (∑ j ∈ mixedCanonicalTerminalIndexSet explicitL N M,
          (((j + 1 : ℕ) : ℝ) ^
              mixedCanonicalDyadicExponent) *
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
      rw [mul_sum]
    _ ≤
      C * (mixedTerminalConvolutionConstant *
        (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
          (mixedTerminalAbsorbedDyadicExponent +
            mixedCanonicalResidualExponent + 1))) :=
      mul_le_mul_of_nonneg_left hprofile hC0
    _ =
      (N : ℝ) *
        (C₀ * (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
          (mixedTerminalAbsorbedDyadicExponent +
            mixedCanonicalResidualExponent + 1))) := by
      dsimp [C, C₀]
      ring
    _ ≤
      (N : ℝ) * (Erdos327.roughDensity explicitL / 512) :=
      mul_le_mul_of_nonneg_left hN.le hN0
    _ = (N : ℝ) * Erdos327.roughDensity explicitL / 512 := by
      ring

private theorem sourceCoupledCutoff_le_sixteen_dyadic_implies
    {J j : ℕ} (hJ : 1 ≤ J)
    (hnear : sourceCoupledCutoff J ≤ 16 * dyadicScale j) :
    J ≤ j := by
  by_contra hnot
  have hj : j ≤ J - 1 := by omega
  have hmono :
      16 * dyadicScale j ≤ 16 * dyadicScale (J - 1) :=
    Nat.mul_le_mul_left 16 (dyadicScale_mono hj)
  have hidentity :
      16 * dyadicScale (J - 1) = 8 * dyadicScale J := by
    unfold dyadicScale
    have hpred : J - 1 + 1 = J := by omega
    conv_rhs => rw [← hpred, pow_succ]
    ring
  have hbad : sourceCoupledCutoff J ≤ 8 * dyadicScale J :=
    hnear.trans (hmono.trans_eq hidentity)
  exact (not_le_of_gt (eight_dyadicScale_lt_sourceCoupledCutoff J)) hbad

private theorem explicitJ_le_of_mixed_near
    {j : ℕ} (hnear : explicitL ≤ 16 * dyadicScale j) :
    explicitJ ≤ j :=
  sourceCoupledCutoff_le_sixteen_dyadic_implies
    ((by omega : 1 ≤ 64).trans explicitJ_ge_sixty_four) hnear

private theorem explicit_mixedScheduleErrorsHold
    {j : ℕ} (hj : explicitJ ≤ j) :
    mixedCanonicalScheduleErrorsHold j :=
  ⟨explicit_scheduledFactorialTail_le hj,
    explicit_scheduledPolynomialBoundary_le hj⟩

private theorem explicit_mixedBoundaryMainProfile_absorbed
    {j : ℕ} (hj : explicitJ ≤ j) :
    log (dyadicScale j : ℝ) ^ mixedCanonicalDyadicExponent *
        scheduledLogLoss j ^ (2 : ℝ) ≤
      mixedBoundaryProfileConstant *
        (((j + 1 : ℕ) : ℝ) ^
          (mixedCanonicalDyadicExponent + mixedBulkLogAbsorption)) := by
  have hj1 : 1 ≤ j :=
    ((by omega : 1 ≤ 64).trans explicitJ_ge_sixty_four).trans hj
  have habs := explicit_log_rpow_le_tiny hj
    (m := (4 : ℝ)) (by norm_num) (by norm_num)
  have hdyadic := log_dyadicScale_rpow_terminal_le_index (j := j) hj1
  have hloss := scheduledLogLoss_sq_le_log_four hj1
  have hindex0 :
      0 ≤ (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlog0 :
      0 ≤ log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) :=
    Real.rpow_nonneg (Real.log_natCast_nonneg _) _
  calc
    log (dyadicScale j : ℝ) ^ mixedCanonicalDyadicExponent *
          scheduledLogLoss j ^ (2 : ℝ) ≤
      (mixedTerminalDyadicIndexConstant *
          (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent)) *
        (mixedScheduleLogConstant *
          log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) :=
      mul_le_mul hdyadic hloss
        (Real.rpow_nonneg
          (zero_le_one.trans (scheduledLogLoss_one_le j)) _)
        (mul_nonneg mixedTerminalDyadicIndexConstant_pos.le hindex0)
    _ ≤ (mixedTerminalDyadicIndexConstant * mixedScheduleLogConstant) *
        ((((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) *
          (((j + 1 : ℕ) : ℝ) ^ mixedBulkLogAbsorption)) := by
      have habs' :
          log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) ≤
            (((j + 1 : ℕ) : ℝ) ^ mixedBulkLogAbsorption) := by
        simpa [mixedBulkLogAbsorption] using habs
      have hmul := mul_le_mul_of_nonneg_left habs' hindex0
      calc
        _ = (mixedTerminalDyadicIndexConstant * mixedScheduleLogConstant) *
            ((((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hmul
          (mul_nonneg mixedTerminalDyadicIndexConstant_pos.le
            mixedScheduleLogConstant_pos.le)
    _ = _ := by
      unfold mixedBoundaryProfileConstant
      rw [← Real.rpow_add (by exact_mod_cast Nat.succ_pos j)]

private theorem mixedTerminalDyadicIndexConstant_le :
    mixedTerminalDyadicIndexConstant ≤ (2 : ℝ) ^ (2 : ℕ) := by
  have hlogPos : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hbase0 : 0 ≤ 2 / log (2 : ℝ) := by positivity
  have hbase : 2 / log (2 : ℝ) ≤ (4 : ℝ) := by
    apply (div_le_iff₀ hlogPos).2
    nlinarith [log_two_lower_half]
  have hexp0 : 0 ≤ -mixedCanonicalDyadicExponent := by
    linarith [mixedCanonicalDyadicExponent_lt_zero]
  have hexp1 : -mixedCanonicalDyadicExponent ≤ 1 := by
    linarith [mixedCanonicalDyadicExponent_gt_neg_one]
  unfold mixedTerminalDyadicIndexConstant
  calc
    (2 / log (2 : ℝ)) ^ (-mixedCanonicalDyadicExponent) ≤
        (4 : ℝ) ^ (-mixedCanonicalDyadicExponent) :=
      Real.rpow_le_rpow hbase0 hbase hexp0
    _ ≤ (4 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp1
    _ = (2 : ℝ) ^ (2 : ℕ) := by norm_num

private theorem mixedBoundaryProfileConstant_le :
    mixedBoundaryProfileConstant ≤ (2 : ℝ) ^ (34 : ℕ) := by
  unfold mixedBoundaryProfileConstant
  calc
    mixedTerminalDyadicIndexConstant * mixedScheduleLogConstant ≤
        (2 : ℝ) ^ (2 : ℕ) * (2 : ℝ) ^ (32 : ℕ) :=
      mul_le_mul mixedTerminalDyadicIndexConstant_le
        mixedScheduleLogConstant_le mixedScheduleLogConstant_pos.le
        (by positivity)
    _ = (2 : ℝ) ^ (34 : ℕ) := by rw [← pow_add]

private theorem mixedBoundaryMainFixedConstant_le :
    mixedBoundaryMainFixedConstant explicitSourceBudget ≤
      (2 : ℝ) ^ (800000130 : ℕ) := by
  unfold mixedBoundaryMainFixedConstant
  have hAB :
      mixedSourceWeightBase ^ explicitSourceBudget *
          5 ^ mixedCanonicalRegularityExponent ≤
        (2 : ℝ) ^ (800000000 : ℕ) * 32 :=
    mul_le_mul mixedSourceBudgetPower_le
      (five_rpow_mixedRegularity_le.trans (by norm_num))
      (Real.rpow_nonneg (by norm_num) _)
      (by positivity)
  calc
    8 * (mixedSourceWeightBase ^ explicitSourceBudget *
          5 ^ mixedCanonicalRegularityExponent) *
          mixedCanonicalScheduledProductConstant ≤
        8 * ((2 : ℝ) ^ (800000000 : ℕ) * 32) *
          (2 : ℝ) ^ (120 : ℕ) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hAB (by norm_num))
        mixedCanonicalScheduledProductConstant_le
        mixedCanonicalScheduledProductConstant_pos.le (by positivity)
    _ = (2 : ℝ) ^ (800000128 : ℕ) := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num,
        show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num,
        ← pow_add, ← pow_add, ← pow_add]
    _ ≤ (2 : ℝ) ^ (800000130 : ℕ) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)

private theorem mixedBoundaryErrorFixedConstant_le :
    mixedBoundaryErrorFixedConstant explicitSourceBudget ≤
      (2 : ℝ) ^ (800000010 : ℕ) := by
  unfold mixedBoundaryErrorFixedConstant
  have hAB :
      mixedSourceWeightBase ^ explicitSourceBudget *
          5 ^ mixedCanonicalRegularityExponent ≤
        (2 : ℝ) ^ (800000000 : ℕ) * 32 :=
    mul_le_mul mixedSourceBudgetPower_le
      (five_rpow_mixedRegularity_le.trans (by norm_num))
      (Real.rpow_nonneg (by norm_num) _)
      (by positivity)
  calc
    9 * (mixedSourceWeightBase ^ explicitSourceBudget *
          5 ^ mixedCanonicalRegularityExponent) ≤
        16 * ((2 : ℝ) ^ (800000000 : ℕ) * 32) := by
      exact (mul_le_mul_of_nonneg_left hAB (by norm_num)).trans
        (mul_le_mul_of_nonneg_right (by norm_num : (9 : ℝ) ≤ 16)
          (by positivity))
    _ = (2 : ℝ) ^ (800000009 : ℕ) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
        show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num,
        ← pow_add, ← pow_add]
    _ ≤ (2 : ℝ) ^ (800000010 : ℕ) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)

private theorem mixedBoundaryInverseFactor_le :
    (1 / (2 * log 2) : ℝ) ^
        (mixedCanonicalDyadicExponent + mixedBulkLogAbsorption) ≤
      (2 : ℝ) := by
  let r : ℝ := mixedCanonicalDyadicExponent + mixedBulkLogAbsorption
  have hlogPos : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hbaseLower : (1 / 2 : ℝ) ≤ 1 / (2 * log 2) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hlogPos)).2
    nlinarith [Real.log_two_lt_d9]
  have hr0 : r ≤ 0 := by
    dsimp [r]
    exact mixedBoundaryAbsorbedExponent_lt_zero.le
  have hrLower : (-1 : ℝ) ≤ r := by
    dsimp [r]
    linarith [mixedCanonicalDyadicExponent_gt_neg_one,
      mixedBulkLogAbsorption_pos]
  calc
    (1 / (2 * log 2) : ℝ) ^
          (mixedCanonicalDyadicExponent + mixedBulkLogAbsorption) =
        (1 / (2 * log 2) : ℝ) ^ r := by rfl
    _ ≤ (1 / 2 : ℝ) ^ r :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hbaseLower hr0
    _ ≤ (1 / 2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hrLower
    _ = 2 := by
      rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num

private theorem mixedInverseLogSix_le :
    (1 / (2 * log 2) : ℝ) ^ (-6 : ℝ) ≤ (64 : ℝ) := by
  have hlogPos : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hbaseLower : (1 / 2 : ℝ) ≤ 1 / (2 * log 2) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hlogPos)).2
    nlinarith [Real.log_two_lt_d9]
  calc
    (1 / (2 * log 2) : ℝ) ^ (-6 : ℝ) ≤
        (1 / 2 : ℝ) ^ (-6 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hbaseLower (by norm_num)
    _ = 64 := by
      rw [show (-6 : ℝ) = -(6 : ℝ) by norm_num,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num [Real.rpow_natCast]

private theorem mixedTransitionMainAsymptoticConstant_le :
    mixedTransitionMainAsymptoticConstant explicitSourceBudget ≤
      (2 : ℝ) ^ (800000170 : ℕ) := by
  unfold mixedTransitionMainAsymptoticConstant
  calc
    mixedBoundaryMainFixedConstant explicitSourceBudget *
          mixedBoundaryProfileConstant *
          (1 / (2 * log 2)) ^
            (mixedCanonicalDyadicExponent + mixedBulkLogAbsorption) ≤
        (2 : ℝ) ^ (800000130 : ℕ) * (2 : ℝ) ^ (34 : ℕ) *
          (2 : ℝ) ^ (1 : ℕ) := by
      have h1 := mul_le_mul mixedBoundaryMainFixedConstant_le
        mixedBoundaryProfileConstant_le mixedBoundaryProfileConstant_pos.le
        (by positivity)
      exact mul_le_mul h1
        (mixedBoundaryInverseFactor_le.trans_eq (by norm_num))
        (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = (2 : ℝ) ^ (800000165 : ℕ) := by
      rw [← pow_add, ← pow_add]
    _ ≤ (2 : ℝ) ^ (800000170 : ℕ) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)

private theorem mixedTransitionErrorAsymptoticConstant_le :
    mixedTransitionErrorAsymptoticConstant explicitSourceBudget ≤
      (2 : ℝ) ^ (800000020 : ℕ) := by
  unfold mixedTransitionErrorAsymptoticConstant
  calc
    mixedBoundaryErrorFixedConstant explicitSourceBudget *
          (1 / (2 * log 2)) ^ (-6 : ℝ) ≤
        (2 : ℝ) ^ (800000010 : ℕ) * (2 : ℝ) ^ (6 : ℕ) :=
      mul_le_mul mixedBoundaryErrorFixedConstant_le
        (mixedInverseLogSix_le.trans_eq (by norm_num))
        (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = (2 : ℝ) ^ (800000016 : ℕ) := by rw [← pow_add]
    _ ≤ (2 : ℝ) ^ (800000020 : ℕ) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)

private theorem mixedTransitionMainConstant_le_scale :
    mixedTransitionMainAsymptoticConstant explicitSourceBudget ≤
      (2 : ℝ) ^ (explicitScale / 2) :=
  mixedTransitionMainAsymptoticConstant_le.trans
    (pow_le_pow_right₀ (by norm_num) (by norm_num [explicitScale]))

private theorem mixedTransitionErrorConstant_le_scale :
    mixedTransitionErrorAsymptoticConstant explicitSourceBudget ≤
      (2 : ℝ) ^ (explicitScale / 2) :=
  mixedTransitionErrorAsymptoticConstant_le.trans
    (pow_le_pow_right₀ (by norm_num) (by norm_num [explicitScale]))

private theorem mixedTransitionErrorCoefficient_gap :
    (1 / 10000 : ℝ) ≤
      (mixedCanonicalRegularityExponent + 6 -
        oddBudgetSlope * log mixedOddWeightBase) - 1 := by
  linarith [mixedErrorCoefficient_gap]

private theorem explicit_mixedTransitionMainCoefficient_le :
    mixedTransitionMainAsymptoticConstant explicitSourceBudget *
        mixedOddWeightBase ^ oddBudget explicitL *
        log (explicitL : ℝ) ^ (-2 + mixedBulkLogAbsorption) ≤
      roughDensity explicitL / 8192 := by
  let η : ℝ :=
    2 - oddBudgetSlope * log mixedOddWeightBase -
      mixedBulkLogAbsorption
  have hC0 :
      0 ≤ mixedTransitionMainAsymptoticConstant explicitSourceBudget :=
    (mixedTransitionMainAsymptoticConstant_pos _).le
  have hbase := explicit_const_mul_log_rpow_le_roughDensity
    (C := mixedTransitionMainAsymptoticConstant explicitSourceBudget)
    (D := (8192 : ℝ)) (η := η) hC0
    mixedTransitionMainConstant_le_scale
    (by norm_num) (by norm_num) (by
      dsimp [η]
      exact mixedBulkCoefficient_gap)
  have hL : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  have hLreal : (1 : ℝ) < explicitL :=
    (by norm_num : (1 : ℝ) < 3).trans_le (Nat.cast_le.2 hL)
  have hlogL : 0 < log (explicitL : ℝ) := log_pos hLreal
  rw [oddBudget, base_rpow_mul_loglog
    (by linarith [mixedOddWeightBase_gt_one]) hLreal]
  have hcombine :
      log (explicitL : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (explicitL : ℝ) ^ (-2 + mixedBulkLogAbsorption) =
        log (explicitL : ℝ) ^ (-η) := by
    rw [← Real.rpow_add hlogL]
    congr 1
    dsimp [η]
    ring
  calc
    _ = mixedTransitionMainAsymptoticConstant explicitSourceBudget *
        (log (explicitL : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (explicitL : ℝ) ^ (-2 + mixedBulkLogAbsorption)) := by
      ring
    _ = mixedTransitionMainAsymptoticConstant explicitSourceBudget *
        log (explicitL : ℝ) ^ (-η) := by rw [hcombine]
    _ ≤ roughDensity explicitL / 8192 := hbase

private theorem explicit_mixedTransitionErrorCoefficient_le :
    mixedTransitionErrorAsymptoticConstant explicitSourceBudget *
        mixedOddWeightBase ^ oddBudget explicitL *
        log (explicitL : ℝ) ^
          (-mixedCanonicalRegularityExponent - 6) ≤
      roughDensity explicitL / 8192 := by
  let η : ℝ :=
    mixedCanonicalRegularityExponent + 6 -
      oddBudgetSlope * log mixedOddWeightBase
  have hC0 :
      0 ≤ mixedTransitionErrorAsymptoticConstant explicitSourceBudget :=
    (mixedTransitionErrorAsymptoticConstant_pos _).le
  have hbase := explicit_const_mul_log_rpow_le_roughDensity
    (C := mixedTransitionErrorAsymptoticConstant explicitSourceBudget)
    (D := (8192 : ℝ)) (η := η) hC0
    mixedTransitionErrorConstant_le_scale
    (by norm_num) (by norm_num) (by
      dsimp [η]
      exact mixedTransitionErrorCoefficient_gap)
  have hL : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  have hLreal : (1 : ℝ) < explicitL :=
    (by norm_num : (1 : ℝ) < 3).trans_le (Nat.cast_le.2 hL)
  have hlogL : 0 < log (explicitL : ℝ) := log_pos hLreal
  rw [oddBudget, base_rpow_mul_loglog
    (by linarith [mixedOddWeightBase_gt_one]) hLreal]
  have hcombine :
      log (explicitL : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (explicitL : ℝ) ^
            (-mixedCanonicalRegularityExponent - 6) =
        log (explicitL : ℝ) ^ (-η) := by
    rw [← Real.rpow_add hlogL]
    congr 1
    dsimp [η]
    ring
  calc
    _ = mixedTransitionErrorAsymptoticConstant explicitSourceBudget *
        (log (explicitL : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (explicitL : ℝ) ^
            (-mixedCanonicalRegularityExponent - 6)) := by ring
    _ = mixedTransitionErrorAsymptoticConstant explicitSourceBudget *
        log (explicitL : ℝ) ^ (-η) := by rw [hcombine]
    _ ≤ roughDensity explicitL / 8192 := hbase


theorem explicit_sum_mixedTransitionBoundary_le
    (N M : ℕ) :
    (∑ j ∈ mixedTransitionBoundaryIndexSet explicitL M,
      mixedCanonicalBoundaryBlock
        explicitL N explicitSourceBudget (oddBudget explicitL) j) ≤
      (N : ℝ) * roughDensity explicitL / (2 * 512) := by
  have hmainCoef :
      mixedTransitionMainAsymptoticConstant explicitSourceBudget *
          mixedOddWeightBase ^ oddBudget explicitL *
          log (explicitL : ℝ) ^ (-2 + mixedBulkLogAbsorption) ≤
        roughDensity explicitL / (16 * 512) := by
    simpa only [show (16 : ℝ) * 512 = 8192 by norm_num] using
      explicit_mixedTransitionMainCoefficient_le
  have herrorCoef :
      mixedTransitionErrorAsymptoticConstant explicitSourceBudget *
          mixedOddWeightBase ^ oddBudget explicitL *
          log (explicitL : ℝ) ^
            (-mixedCanonicalRegularityExponent - 6) ≤
        roughDensity explicitL / (16 * 512) := by
    simpa only [show (16 : ℝ) * 512 = 8192 by norm_num] using
      explicit_mixedTransitionErrorCoefficient_le
  have hL3 : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  have hlogNat : 9 ≤ Nat.log 2 explicitL := by
    rw [natLog_two_explicitL]
    have hJ : 64 ≤ explicitJ := explicitJ_ge_sixty_four
    omega
  have hstart1 : 1 ≤ mixedBulkMovingStart explicitL := by
    rw [mixedBulkMovingStart_explicitL]
    have hJ : 64 ≤ explicitJ := explicitJ_ge_sixty_four
    omega
  have hlogStart :=
    log_div_le_mixedBulkMovingStart hL3 hlogNat
  have hlogL : 0 < log (explicitL : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < explicitL by omega))
  have hratioPos :
      0 < log (explicitL : ℝ) / (2 * log 2) := by
    positivity [log_pos (by norm_num : (1 : ℝ) < 2)]
  have hinvPos : 0 < (1 / (2 * log 2) : ℝ) := by
    positivity [log_pos (by norm_num : (1 : ℝ) < 2)]
  let s := mixedTransitionBoundaryIndexSet explicitL M
  have hpoint :
      ∀ j ∈ s,
        mixedCanonicalBoundaryBlock
            explicitL N explicitSourceBudget (oddBudget explicitL) j ≤
          (N : ℝ) *
              (Erdos327.roughDensity explicitL / (16 * 512)) +
            (N : ℝ) *
              (Erdos327.roughDensity explicitL / (16 * 512)) := by
    intro j hj
    have hj' := hj
    dsimp [s] at hj'
    rw [mixedTransitionBoundaryIndexSet, mem_filter] at hj'
    have hnear := hj'.2.2
    have hstartj :
        mixedBulkMovingStart explicitL ≤ j :=
      mixedBulkMovingStart_le_of_near hnear
    have hJj : explicitJ ≤ j := explicitJ_le_of_mixed_near hnear
    have hj1 : 1 ≤ j :=
      ((by omega : 1 ≤ 64).trans explicitJ_ge_sixty_four).trans hJj
    have hraw :=
      mixedCanonicalBoundaryBlock_le_mainRaw_add_errorRaw
        (L := explicitL) (N := N) (j := j)
        (Kb := explicitSourceBudget) (Ko := oddBudget explicitL)
        hL3 hj1 (explicit_sieveSchedule_dominates hJj)
        (explicit_mixedScheduleErrorsHold hJj)
    let r : ℝ :=
      mixedCanonicalDyadicExponent + mixedBulkLogAbsorption
    have hr : r < 0 := by
      dsimp [r]
      exact mixedBoundaryAbsorbedExponent_lt_zero
    have hstartReal :
        (0 : ℝ) < mixedBulkMovingStart explicitL := by
      exact_mod_cast (show 0 < mixedBulkMovingStart explicitL by omega)
    have hstartLe :
        (mixedBulkMovingStart explicitL : ℝ) ≤
          (((j + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (show mixedBulkMovingStart explicitL ≤ j + 1 by omega)
    have hjpow :
        (((j + 1 : ℕ) : ℝ) ^ r) ≤
          (mixedBulkMovingStart explicitL : ℝ) ^ r :=
      Real.rpow_le_rpow_of_nonpos hstartReal hstartLe hr.le
    have hstartPow :
        (mixedBulkMovingStart explicitL : ℝ) ^ r ≤
          (1 / (2 * log 2)) ^ r *
            log (explicitL : ℝ) ^ r := by
      have hanti :=
        Real.rpow_le_rpow_of_nonpos
          hratioPos hlogStart hr.le
      calc
        _ ≤ (log (explicitL : ℝ) / (2 * log 2)) ^ r := hanti
        _ =
            (1 / (2 * log 2)) ^ r *
              log (explicitL : ℝ) ^ r := by
          rw [show log (explicitL : ℝ) / (2 * log 2) =
              (1 / (2 * log 2)) * log (explicitL : ℝ) by ring,
            Real.mul_rpow hinvPos.le hlogL.le]
    have hprofile :
        log (dyadicScale j : ℝ) ^ mixedCanonicalDyadicExponent *
            scheduledLogLoss j ^ (2 : ℝ) ≤
          mixedBoundaryProfileConstant *
            ((1 / (2 * log 2)) ^ r *
              log (explicitL : ℝ) ^ r) := by
      calc
        _ ≤ mixedBoundaryProfileConstant *
            (((j + 1 : ℕ) : ℝ) ^ r) := by
          simpa [r] using
            (explicit_mixedBoundaryMainProfile_absorbed hJj)
        _ ≤ mixedBoundaryProfileConstant *
            ((mixedBulkMovingStart explicitL : ℝ) ^ r) :=
          mul_le_mul_of_nonneg_left hjpow
            mixedBoundaryProfileConstant_pos.le
        _ ≤ mixedBoundaryProfileConstant *
            ((1 / (2 * log 2)) ^ r *
              log (explicitL : ℝ) ^ r) :=
          mul_le_mul_of_nonneg_left hstartPow
            mixedBoundaryProfileConstant_pos.le
    have herrorProfile :
        ((((j + 1 : ℕ) : ℝ) ^ 2) /
            (((j + 1 : ℕ) : ℝ) ^ 8)) ≤
          (1 / (2 * log 2)) ^ (-6 : ℝ) *
            log (explicitL : ℝ) ^ (-6 : ℝ) := by
      have hjpow6 :
          (((j + 1 : ℕ) : ℝ) ^ (-6 : ℝ)) ≤
            (mixedBulkMovingStart explicitL : ℝ) ^ (-6 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hstartReal hstartLe (by norm_num)
      have hstartPow6 :
          (mixedBulkMovingStart explicitL : ℝ) ^ (-6 : ℝ) ≤
            (1 / (2 * log 2)) ^ (-6 : ℝ) *
              log (explicitL : ℝ) ^ (-6 : ℝ) := by
        have hanti :=
          Real.rpow_le_rpow_of_nonpos
            hratioPos hlogStart (by norm_num : (-6 : ℝ) ≤ 0)
        calc
          _ ≤ (log (explicitL : ℝ) / (2 * log 2)) ^ (-6 : ℝ) := hanti
          _ =
              (1 / (2 * log 2)) ^ (-6 : ℝ) *
                log (explicitL : ℝ) ^ (-6 : ℝ) := by
            rw [show log (explicitL : ℝ) / (2 * log 2) =
                (1 / (2 * log 2)) * log (explicitL : ℝ) by ring,
              Real.mul_rpow hinvPos.le hlogL.le]
      calc
        _ = (((j + 1 : ℕ) : ℝ) ^ (-6 : ℝ)) := by
          simpa using (mixedCanonicalErrorProfile_eq j).symm
        _ ≤ _ := hjpow6.trans hstartPow6
    have hmain :
        mixedBoundaryMainRaw explicitL N explicitSourceBudget (oddBudget explicitL) j ≤
          (N : ℝ) *
            (mixedTransitionMainAsymptoticConstant explicitSourceBudget *
              mixedOddWeightBase ^ oddBudget explicitL *
              log (explicitL : ℝ) ^
                (-2 + mixedBulkLogAbsorption)) := by
      calc
        _ =
          (mixedBoundaryMainConstant explicitSourceBudget (oddBudget explicitL) * (N : ℝ) *
            log (explicitL : ℝ) ^
              (-mixedCanonicalRegularityExponent +
                mixedCanonicalRoughnessExponent)) *
            (log (dyadicScale j : ℝ) ^
                mixedCanonicalDyadicExponent *
              scheduledLogLoss j ^ (2 : ℝ)) := by
          unfold mixedBoundaryMainRaw
          ring
        _ ≤
          (mixedBoundaryMainConstant explicitSourceBudget (oddBudget explicitL) * (N : ℝ) *
            log (explicitL : ℝ) ^
              (-mixedCanonicalRegularityExponent +
                mixedCanonicalRoughnessExponent)) *
            (mixedBoundaryProfileConstant *
              ((1 / (2 * log 2)) ^ r *
                log (explicitL : ℝ) ^ r)) := by
          apply mul_le_mul_of_nonneg_left hprofile
          exact mul_nonneg
            (mul_nonneg
              (mixedBoundaryMainConstant_pos _ _).le
              (Nat.cast_nonneg N))
            (Real.rpow_nonneg hlogL.le _)
        _ =
          mixedBoundaryMainConstant explicitSourceBudget (oddBudget explicitL) * (N : ℝ) *
            log (explicitL : ℝ) ^
              (-mixedCanonicalRegularityExponent +
                mixedCanonicalRoughnessExponent) *
            (mixedBoundaryProfileConstant *
              ((1 / (2 * log 2)) ^ r *
                log (explicitL : ℝ) ^ r)) := by
          ring
        _ = _ := by
          rw [mixedBoundaryMainConstant_eq_fixed]
          unfold mixedTransitionMainAsymptoticConstant
          dsimp [r]
          have hout :
              -mixedCanonicalRegularityExponent +
                    mixedCanonicalRoughnessExponent +
                  (mixedCanonicalDyadicExponent +
                    mixedBulkLogAbsorption) =
                -2 + mixedBulkLogAbsorption := by
            unfold mixedCanonicalDyadicExponent
            calc
              _ =
                  mixedCanonicalProductExponent +
                    mixedCanonicalRoughnessExponent +
                    mixedBulkLogAbsorption := by ring
              _ = -2 + mixedBulkLogAbsorption := by
                rw [mixedCanonicalProduct_add_roughnessExponent]
          have hlogCombine :
              log (explicitL : ℝ) ^
                    (-mixedCanonicalRegularityExponent +
                      mixedCanonicalRoughnessExponent) *
                  log (explicitL : ℝ) ^
                    (mixedCanonicalDyadicExponent +
                      mixedBulkLogAbsorption) =
                log (explicitL : ℝ) ^
                  (-2 + mixedBulkLogAbsorption) := by
            rw [← Real.rpow_add hlogL, hout]
          rw [show
            mixedBoundaryMainFixedConstant explicitSourceBudget *
                  mixedOddWeightBase ^ oddBudget explicitL * (N : ℝ) *
                  log (explicitL : ℝ) ^
                    (-mixedCanonicalRegularityExponent +
                      mixedCanonicalRoughnessExponent) *
                  (mixedBoundaryProfileConstant *
                    ((1 / (2 * log 2)) ^
                        (mixedCanonicalDyadicExponent +
                          mixedBulkLogAbsorption) *
                      log (explicitL : ℝ) ^
                        (mixedCanonicalDyadicExponent +
                          mixedBulkLogAbsorption))) =
                (mixedBoundaryMainFixedConstant explicitSourceBudget *
                  mixedOddWeightBase ^ oddBudget explicitL * (N : ℝ) *
                  mixedBoundaryProfileConstant *
                  (1 / (2 * log 2)) ^
                    (mixedCanonicalDyadicExponent +
                      mixedBulkLogAbsorption)) *
                  (log (explicitL : ℝ) ^
                      (-mixedCanonicalRegularityExponent +
                        mixedCanonicalRoughnessExponent) *
                    log (explicitL : ℝ) ^
                      (mixedCanonicalDyadicExponent +
                        mixedBulkLogAbsorption)) by ring,
            hlogCombine]
          ring
    have herror :
        mixedBoundaryErrorRaw explicitL N explicitSourceBudget (oddBudget explicitL) j ≤
          (N : ℝ) *
            (mixedTransitionErrorAsymptoticConstant explicitSourceBudget *
              mixedOddWeightBase ^ oddBudget explicitL *
              log (explicitL : ℝ) ^
                (-mixedCanonicalRegularityExponent - 6)) := by
      calc
        _ ≤
          mixedBoundaryErrorConstant explicitSourceBudget (oddBudget explicitL) * (N : ℝ) *
            log (explicitL : ℝ) ^ (-mixedCanonicalRegularityExponent) *
            ((1 / (2 * log 2)) ^ (-6 : ℝ) *
              log (explicitL : ℝ) ^ (-6 : ℝ)) := by
          unfold mixedBoundaryErrorRaw
          apply mul_le_mul_of_nonneg_left herrorProfile
          exact mul_nonneg
            (mul_nonneg
              (mixedBoundaryErrorConstant_pos _ _).le
              (Nat.cast_nonneg N))
            (Real.rpow_nonneg hlogL.le _)
        _ = _ := by
          rw [mixedBoundaryErrorConstant_eq_fixed]
          unfold mixedTransitionErrorAsymptoticConstant
          have hlogCombine :
              log (explicitL : ℝ) ^ (-mixedCanonicalRegularityExponent) *
                  log (explicitL : ℝ) ^ (-6 : ℝ) =
                log (explicitL : ℝ) ^
                  (-mixedCanonicalRegularityExponent - 6) := by
            rw [← Real.rpow_add hlogL]
            congr 1
          rw [show
            mixedBoundaryErrorFixedConstant explicitSourceBudget *
                  mixedOddWeightBase ^ oddBudget explicitL * (N : ℝ) *
                  log (explicitL : ℝ) ^
                    (-mixedCanonicalRegularityExponent) *
                  ((1 / (2 * log 2)) ^ (-6 : ℝ) *
                    log (explicitL : ℝ) ^ (-6 : ℝ)) =
                (mixedBoundaryErrorFixedConstant explicitSourceBudget *
                  mixedOddWeightBase ^ oddBudget explicitL * (N : ℝ) *
                  (1 / (2 * log 2)) ^ (-6 : ℝ)) *
                  (log (explicitL : ℝ) ^
                      (-mixedCanonicalRegularityExponent) *
                    log (explicitL : ℝ) ^ (-6 : ℝ)) by ring,
            hlogCombine]
          ring
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    calc
      _ ≤ mixedBoundaryMainRaw explicitL N explicitSourceBudget (oddBudget explicitL) j +
          mixedBoundaryErrorRaw explicitL N explicitSourceBudget (oddBudget explicitL) j := hraw
      _ ≤
          (N : ℝ) *
              (mixedTransitionMainAsymptoticConstant explicitSourceBudget *
                mixedOddWeightBase ^ oddBudget explicitL *
                log (explicitL : ℝ) ^
                  (-2 + mixedBulkLogAbsorption)) +
            (N : ℝ) *
              (mixedTransitionErrorAsymptoticConstant explicitSourceBudget *
                mixedOddWeightBase ^ oddBudget explicitL *
                log (explicitL : ℝ) ^
                  (-mixedCanonicalRegularityExponent - 6)) :=
        add_le_add hmain herror
      _ ≤
          (N : ℝ) *
              (Erdos327.roughDensity explicitL / (16 * 512)) +
            (N : ℝ) *
              (Erdos327.roughDensity explicitL / (16 * 512)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hmainCoef hN0)
          (mul_le_mul_of_nonneg_left herrorCoef hN0)
  have hsumCard :=
    Finset.sum_le_card_nsmul s _
      ((N : ℝ) * (Erdos327.roughDensity explicitL / (16 * 512)) +
        (N : ℝ) * (Erdos327.roughDensity explicitL / (16 * 512))) hpoint
  have hcard : s.card ≤ 4 := by
    dsimp [s]
    exact card_mixedTransitionBoundaryIndexSet_le_four explicitL M
  have htarget0 :
      0 ≤
        (N : ℝ) * (Erdos327.roughDensity explicitL / (16 * 512)) +
          (N : ℝ) * (Erdos327.roughDensity explicitL / (16 * 512)) := by
    have hterm :
        0 ≤ (N : ℝ) * (roughDensity explicitL / (16 * 512)) :=
      mul_nonneg (Nat.cast_nonneg N)
        (div_nonneg (roughDensity_pos hL3).le (by norm_num))
    exact add_nonneg hterm hterm
  calc
    (∑ j ∈ mixedTransitionBoundaryIndexSet explicitL M,
        mixedCanonicalBoundaryBlock explicitL N explicitSourceBudget (oddBudget explicitL) j)
        ≤ s.card •
          ((N : ℝ) * (Erdos327.roughDensity explicitL / (16 * 512)) +
            (N : ℝ) * (Erdos327.roughDensity explicitL / (16 * 512))) :=
      hsumCard
    _ = (s.card : ℝ) *
          ((N : ℝ) * (Erdos327.roughDensity explicitL / (16 * 512)) +
            (N : ℝ) * (Erdos327.roughDensity explicitL / (16 * 512))) := by
      simp only [nsmul_eq_mul]
    _ ≤ (4 : ℝ) *
          ((N : ℝ) * (Erdos327.roughDensity explicitL / (16 * 512)) +
            (N : ℝ) * (Erdos327.roughDensity explicitL / (16 * 512))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) htarget0
    _ = (N : ℝ) * Erdos327.roughDensity explicitL / (2 * 512) := by
      norm_num
      <;> ring

private theorem seventeen_le_sourceCoupledCutoff
    {J : ℕ} (hJ : 1 ≤ J) : 17 ≤ sourceCoupledCutoff J := by
  have hpow : 2 ^ (1 : ℕ) ≤ 2 ^ J :=
    Nat.pow_le_pow_right (by norm_num) hJ
  unfold sourceCoupledCutoff dyadicScale
  norm_num at hpow ⊢
  omega

theorem explicit_exists_forall_sum_mixedCanonicalBoundaryBlock_le_roughDensity :
    ∃ Nb : ℕ, ∀ N ≥ Nb, ∀ M : ℕ,
      (∑ j ∈ range M,
        mixedCanonicalBoundaryBlock
          explicitL N explicitSourceBudget (oddBudget explicitL) j) ≤
        (N : ℝ) * roughDensity explicitL / 512 := by
  have hL17 : 17 ≤ explicitL :=
    seventeen_le_sourceCoupledCutoff
      ((by omega : 1 ≤ 64).trans explicitJ_ge_sixty_four)
  have hL3 : 3 ≤ explicitL := by omega
  have hε : 0 < roughDensity explicitL / (2 * 512) :=
    div_pos (roughDensity_pos hL3) (by norm_num)
  have hevent := eventually_sum_mixedPositiveResidualBoundary_le
    explicitL explicitSourceBudget hL17 hε
  rcases eventually_atTop.1 hevent with ⟨Nb, hNb⟩
  refine ⟨Nb, ?_⟩
  intro N hN M
  have hresidual := hNb N hN M
  rw [sum_mixedCanonicalBoundaryBlock_eq_transition_add_residual hL17]
  calc
    (∑ j ∈ mixedTransitionBoundaryIndexSet explicitL M,
        mixedCanonicalBoundaryBlock
          explicitL N explicitSourceBudget (oddBudget explicitL) j) +
        ∑ j ∈ mixedPositiveResidualBoundaryIndexSet explicitL N M,
          mixedCanonicalBoundaryBlock
            explicitL N explicitSourceBudget (oddBudget explicitL) j ≤
      (N : ℝ) * roughDensity explicitL / (2 * 512) +
        (roughDensity explicitL / (2 * 512)) * (N : ℝ) :=
      add_le_add (explicit_sum_mixedTransitionBoundary_le N M) hresidual
    _ = (N : ℝ) * roughDensity explicitL / 512 := by ring


private theorem explicit_mixedCanonicalUnresolved_eq_terminal_add_boundary
    {L N j : ℕ} (hj : explicitJ ≤ j) (Kb Ko : ℝ) :
    mixedCanonicalUnresolvedBlock L N Kb Ko j =
      mixedCanonicalTerminalMainContribution L N Kb Ko j +
        mixedCanonicalBoundaryBlock L N Kb Ko j := by
  have herrors : mixedCanonicalScheduleErrorsHold j :=
    explicit_mixedScheduleErrorsHold hj
  have hdom : 32 * sieveRadius j ≤ j :=
    explicit_sieveSchedule_dominates hj
  by_cases hnear : L ≤ 16 * dyadicScale j
  · by_cases hgood : mixedScheduledGoodIndex L N j
    · by_cases hterminal :
          N / (dyadicScale j * dyadicScale j) < dyadicScale j
      · have hnotbulk :
            ¬dyadicScale j ≤
              N / (dyadicScale j * dyadicScale j) := by omega
        have hnoboundary :
            ¬(L ≤ 16 * dyadicScale j ∧
              (dyadicScale j < L ∨
                N / (dyadicScale j * dyadicScale j) < L)) := by
          intro hb
          rcases hb.2 with hbX | hbY
          · exact (Nat.not_lt_of_ge hgood.2.1) hbX
          · exact (Nat.not_lt_of_ge hgood.2.2.2) hbY
        unfold mixedCanonicalUnresolvedBlock
          mixedCanonicalTerminalMainContribution
          mixedCanonicalBoundaryBlock
        rw [if_pos ⟨herrors, hdom, hnear, hgood⟩,
          if_neg hnotbulk,
          if_pos ⟨hdom, hnear, hgood, hterminal⟩,
          if_neg hnoboundary]
        simp
      · have hbulk :
            dyadicScale j ≤
              N / (dyadicScale j * dyadicScale j) := by omega
        have hnoboundary :
            ¬(L ≤ 16 * dyadicScale j ∧
              (dyadicScale j < L ∨
                N / (dyadicScale j * dyadicScale j) < L)) := by
          intro hb
          rcases hb.2 with hbX | hbY
          · exact (Nat.not_lt_of_ge hgood.2.1) hbX
          · exact (Nat.not_lt_of_ge hgood.2.2.2) hbY
        unfold mixedCanonicalUnresolvedBlock
          mixedCanonicalTerminalMainContribution
          mixedCanonicalBoundaryBlock
        rw [if_pos ⟨herrors, hdom, hnear, hgood⟩,
          if_pos hbulk,
          if_neg (by
            intro ht
            exact hterminal ht.2.2.2),
          if_neg hnoboundary]
        simp
    · have hboundary :=
        mixedScheduled_not_good_boundary hdom hgood
      unfold mixedCanonicalUnresolvedBlock
        mixedCanonicalTerminalMainContribution
        mixedCanonicalBoundaryBlock
      rw [if_neg (by
          intro h
          exact hgood h.2.2.2),
        if_neg (by
          intro h
          exact hgood h.2.2.1),
        if_pos ⟨hnear, hboundary⟩]
      simp
  · have hempty : 16 * dyadicScale j < L := by omega
    unfold mixedCanonicalUnresolvedBlock
      mixedCanonicalTerminalMainContribution
      mixedCanonicalBoundaryBlock
    rw [if_neg (by
        intro h
        exact hnear h.2.2.1),
      if_neg (by
        intro h
        exact hnear h.2.1),
      if_neg (by
        intro h
        exact hnear h.1),
      mixedRefinedScheduledBlockBound, if_pos hempty]
    simp

private theorem sixteen_dyadic_lt_sourceCoupledCutoff_of_lt
    {J j : ℕ} (hJ : 1 ≤ J) (hj : j < J) :
    16 * dyadicScale j < sourceCoupledCutoff J := by
  have hnot : ¬sourceCoupledCutoff J ≤ 16 * dyadicScale j := by
    intro hnear
    exact (not_le_of_gt hj)
      (sourceCoupledCutoff_le_sixteen_dyadic_implies hJ hnear)
  omega

private theorem explicit_mixedCanonicalUnresolved_prefix_eq_zero
    (N : ℕ) :
    (∑ j ∈ range explicitJ,
      mixedCanonicalUnresolvedBlock explicitL N explicitSourceBudget
        (oddBudget explicitL) j) = 0 := by
  apply sum_eq_zero
  intro j hj
  have hfar : 16 * dyadicScale j < explicitL :=
    sixteen_dyadic_lt_sourceCoupledCutoff_of_lt
      ((by omega : 1 ≤ 64).trans explicitJ_ge_sixty_four)
      (mem_range.mp hj)
  have hnear : ¬explicitL ≤ 16 * dyadicScale j := by omega
  unfold mixedCanonicalUnresolvedBlock
  rw [if_neg (by
      intro h
      exact hnear h.2.2.1)]
  rw [mixedRefinedScheduledBlockBound, if_pos hfar]

private theorem explicit_sum_mixedCanonicalUnresolved_eq_terminal_add_boundary
    (L N M : ℕ) (Kb Ko : ℝ) :
    (∑ j ∈ Ico explicitJ M,
      mixedCanonicalUnresolvedBlock L N Kb Ko j) =
      (∑ j ∈ Ico explicitJ M,
        mixedCanonicalTerminalMainContribution L N Kb Ko j) +
      ∑ j ∈ Ico explicitJ M,
        mixedCanonicalBoundaryBlock L N Kb Ko j := by
  calc
    _ = ∑ j ∈ Ico explicitJ M,
        (mixedCanonicalTerminalMainContribution L N Kb Ko j +
          mixedCanonicalBoundaryBlock L N Kb Ko j) := by
      apply sum_congr rfl
      intro j hj
      exact explicit_mixedCanonicalUnresolved_eq_terminal_add_boundary
        (mem_Ico.mp hj).1 Kb Ko
    _ = _ := by rw [sum_add_distrib]

theorem explicit_exists_forall_sum_mixedRefined_add_one_le_roughDensity :
    ∃ Nm : ℕ, ∀ N ≥ Nm,
      (∑ j ∈ range (Nat.log 2 N + 1),
        mixedRefinedScheduledBlockBound
          explicitL N sourceAnatomySlope explicitSourceBudget
            oddAnatomySlope (oddBudget explicitL)
            mixedSourceWeightBase mixedOddWeightBase j) + 1 ≤
        (N : ℝ) * roughDensity explicitL / 64 := by
  have hL3 : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  rcases explicit_exists_forall_sum_mixedCanonicalTerminalMain_le_roughDensity with
    ⟨Nt, hNt⟩
  rcases explicit_exists_forall_sum_mixedCanonicalBoundaryBlock_le_roughDensity with
    ⟨Nb, hNb⟩
  have hbulk := explicit_sum_mixedCanonicalBulkMain_le_roughDensity
  have herror := explicit_sum_mixedCanonicalGoodSieveError_le_roughDensity
  have hprefix := explicit_mixedCanonicalUnresolved_prefix_eq_zero
  obtain ⟨No, hNo⟩ :=
    exists_nat_forall_one_le_nat_mul_roughDensity_div
      hL3 (D := (512 : ℝ)) (by norm_num)
  let N₀ : ℕ := max Nt (max Nb (max No (max (2 ^ explicitJ) 2)))
  refine ⟨N₀, ?_⟩
  intro N hN
  have hNtN : Nt ≤ N :=
    (le_max_left Nt (max Nb (max No (max (2 ^ explicitJ) 2)))).trans hN
  have hNbN : Nb ≤ N :=
    (le_trans (le_max_left Nb (max No (max (2 ^ explicitJ) 2)))
      (le_max_right Nt (max Nb (max No (max (2 ^ explicitJ) 2))))).trans hN
  have hNoN : No ≤ N :=
    (le_trans (le_max_left No (max (2 ^ explicitJ) 2))
      (le_trans (le_max_right Nb (max No (max (2 ^ explicitJ) 2)))
        (le_max_right Nt
          (max Nb (max No (max (2 ^ explicitJ) 2)))))).trans hN
  have hpowN : 2 ^ explicitJ ≤ N :=
    (le_trans (le_max_left (2 ^ explicitJ) 2)
      (le_trans (le_max_right No (max (2 ^ explicitJ) 2))
        (le_trans (le_max_right Nb (max No (max (2 ^ explicitJ) 2)))
          (le_max_right Nt
            (max Nb (max No (max (2 ^ explicitJ) 2))))))).trans hN
  let M : ℕ := Nat.log 2 N + 1
  have hJM : explicitJ ≤ M := by
    dsimp [M]
    exact index_le_log_two_add_one_of_pow_le hpowN
  have hunresolved :
      (∑ j ∈ range M,
        mixedCanonicalUnresolvedBlock
          explicitL N explicitSourceBudget (oddBudget explicitL) j) ≤
        (∑ j ∈ range M,
          mixedCanonicalTerminalMainContribution
            explicitL N explicitSourceBudget (oddBudget explicitL) j) +
        ∑ j ∈ range M,
          mixedCanonicalBoundaryBlock
            explicitL N explicitSourceBudget (oddBudget explicitL) j := by
    have hsplit :
        (∑ j ∈ range M,
          mixedCanonicalUnresolvedBlock
            explicitL N explicitSourceBudget (oddBudget explicitL) j) =
          (∑ j ∈ range explicitJ,
            mixedCanonicalUnresolvedBlock
              explicitL N explicitSourceBudget (oddBudget explicitL) j) +
          ∑ j ∈ Ico explicitJ M,
            mixedCanonicalUnresolvedBlock
              explicitL N explicitSourceBudget (oddBudget explicitL) j :=
      (sum_range_add_sum_Ico _ hJM).symm
    have htail :=
      explicit_sum_mixedCanonicalUnresolved_eq_terminal_add_boundary
        explicitL N M explicitSourceBudget (oddBudget explicitL)
    have hterminalTail :
        (∑ j ∈ Ico explicitJ M,
          mixedCanonicalTerminalMainContribution
            explicitL N explicitSourceBudget (oddBudget explicitL) j) ≤
          ∑ j ∈ range M,
            mixedCanonicalTerminalMainContribution
              explicitL N explicitSourceBudget (oddBudget explicitL) j := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact mem_range.mpr (mem_Ico.mp hj).2
      · intro j hjBig hjSmall
        exact mixedCanonicalTerminalMainContribution_nonneg hL3
    have hboundaryTail :
        (∑ j ∈ Ico explicitJ M,
          mixedCanonicalBoundaryBlock
            explicitL N explicitSourceBudget (oddBudget explicitL) j) ≤
          ∑ j ∈ range M,
            mixedCanonicalBoundaryBlock
              explicitL N explicitSourceBudget (oddBudget explicitL) j := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact mem_range.mpr (mem_Ico.mp hj).2
      · intro j hjBig hjSmall
        exact mixedCanonicalBoundaryBlock_nonneg hL3
    calc
      (∑ j ∈ range M,
          mixedCanonicalUnresolvedBlock
            explicitL N explicitSourceBudget (oddBudget explicitL) j) =
        (∑ j ∈ range explicitJ,
          mixedCanonicalUnresolvedBlock
            explicitL N explicitSourceBudget (oddBudget explicitL) j) +
        ∑ j ∈ Ico explicitJ M,
          mixedCanonicalUnresolvedBlock
            explicitL N explicitSourceBudget (oddBudget explicitL) j := hsplit
      _ =
        ∑ j ∈ Ico explicitJ M,
          mixedCanonicalUnresolvedBlock
            explicitL N explicitSourceBudget (oddBudget explicitL) j := by
          rw [hprefix N, zero_add]
      _ =
        (∑ j ∈ Ico explicitJ M,
          mixedCanonicalTerminalMainContribution
            explicitL N explicitSourceBudget (oddBudget explicitL) j) +
        ∑ j ∈ Ico explicitJ M,
          mixedCanonicalBoundaryBlock
            explicitL N explicitSourceBudget (oddBudget explicitL) j := htail
      _ ≤
        (∑ j ∈ range M,
          mixedCanonicalTerminalMainContribution
            explicitL N explicitSourceBudget (oddBudget explicitL) j) +
        ∑ j ∈ range M,
          mixedCanonicalBoundaryBlock
            explicitL N explicitSourceBudget (oddBudget explicitL) j :=
        add_le_add hterminalTail hboundaryTail
  have hrefined :=
    sum_mixedRefinedScheduledBlockBound_le_resolved_add_unresolved
      (L := explicitL) (N := N) (M := M)
      (Kb := explicitSourceBudget) (Ko := oddBudget explicitL) hL3
  have hterminalN := hNt N hNtN M
  have hboundaryN := hNb N hNbN M
  have hone := hNo N hNoN
  have hρ0 : 0 ≤ Erdos327.roughDensity explicitL :=
    (Erdos327.roughDensity_pos hL3).le
  calc
    (∑ j ∈ range (Nat.log 2 N + 1),
        mixedRefinedScheduledBlockBound
          explicitL N sourceAnatomySlope explicitSourceBudget
            oddAnatomySlope (oddBudget explicitL)
            mixedSourceWeightBase mixedOddWeightBase j) + 1 =
      (∑ j ∈ range M,
        mixedRefinedScheduledBlockBound
          explicitL N sourceAnatomySlope explicitSourceBudget
            oddAnatomySlope (oddBudget explicitL)
            mixedSourceWeightBase mixedOddWeightBase j) + 1 := by
        rfl
    _ ≤
      ((∑ j ∈ range M,
          mixedCanonicalBulkMainContribution
            explicitL N explicitSourceBudget (oddBudget explicitL) j) +
        (∑ j ∈ range M,
          mixedCanonicalGoodSieveErrorContribution
            explicitL N explicitSourceBudget (oddBudget explicitL) j) +
        (∑ j ∈ range M,
          mixedCanonicalTerminalMainContribution
            explicitL N explicitSourceBudget (oddBudget explicitL) j) +
        (∑ j ∈ range M,
          mixedCanonicalBoundaryBlock
            explicitL N explicitSourceBudget (oddBudget explicitL) j)) + 1 := by
      gcongr
      exact hrefined.trans (by linarith [hunresolved])
    _ ≤
      ((N : ℝ) * Erdos327.roughDensity explicitL / 512 +
        (N : ℝ) * Erdos327.roughDensity explicitL / 512 +
        (N : ℝ) * Erdos327.roughDensity explicitL / 512 +
        (N : ℝ) * Erdos327.roughDensity explicitL / 512) +
        (N : ℝ) * Erdos327.roughDensity explicitL / 512 := by
      linarith [hbulk N M, herror N M,
        hterminalN, hboundaryN, hone]
    _ ≤ (N : ℝ) * Erdos327.roughDensity explicitL / 64 := by
      have hx :
          0 ≤ (N : ℝ) * Erdos327.roughDensity explicitL :=
        mul_nonneg (Nat.cast_nonneg N) hρ0
      calc
        ((N : ℝ) * roughDensity explicitL / 512 +
            (N : ℝ) * roughDensity explicitL / 512 +
            (N : ℝ) * roughDensity explicitL / 512 +
            (N : ℝ) * roughDensity explicitL / 512) +
            (N : ℝ) * roughDensity explicitL / 512 =
          (5 / 512 : ℝ) * ((N : ℝ) * roughDensity explicitL) := by ring
        _ ≤ (1 / 64 : ℝ) * ((N : ℝ) * roughDensity explicitL) :=
          mul_le_mul_of_nonneg_right (by norm_num) hx
        _ = (N : ℝ) * roughDensity explicitL / 64 := by ring

private theorem erdos327_fixed_gain_of_canonical_estimates
    {L : ℕ} {Ab Kb Ao Ko : ℝ} (hL : 3 ≤ L)
    {N₀ : ℕ}
    (hmodulus : ∀ N ≥ N₀, 4 * roughPrimeModulus L ≤ N)
    (hest :
      ∀ N ≥ N₀,
        ((irregularRoughSource L Ab Kb N).card : ℝ) ≤
            (N : ℝ) * roughDensity L / 8 ∧
        ((Erdos327.rankBad (Erdos327.upto N)
          (regularSource L Ab Kb N)
          ArithmeticFunction.cardFactors).card : ℝ) ≤
            (N : ℝ) * roughDensity L / 16 ∧
        ((irregularOddHost L Ao Ko N).card : ℝ) ≤
            (N : ℝ) * roughDensity L / 64 ∧
        ((Erdos327.mixedEdges
          (regularOddHost L Ao Ko N)
          (Erdos327.rankFilteredSource (Erdos327.upto N)
            (regularSource L Ab Kb N)
            ArithmeticFunction.cardFactors)).card : ℝ) ≤
              (N : ℝ) * roughDensity L / 64) :
    ∃ N₁ : ℕ, ∀ X ≥ N₁,
      ∃ A : Finset ℕ,
        A ⊆ Erdos327.upto X ∧
        Erdos327.OneAdmissible A ∧
        (1 / 2 + roughDensity L / 128) * (X : ℝ) ≤ (A.card : ℝ) := by
  have heven :
      ∀ N ≥ N₀,
        ∃ A : Finset ℕ,
          A ⊆ Erdos327.upto (2 * N) ∧
          Erdos327.OneAdmissible A ∧
          (1 + roughDensity L / 32) * (N : ℝ) ≤ (A.card : ℝ) := by
    intro N hN
    let S := regularSource L Ab Kb N
    let O := regularOddHost L Ao Ko N
    have hmod := hmodulus N hN
    have hN2 : 2 ≤ N := by
      have hmodPos := roughPrimeModulus_pos L
      omega
    rcases hest N hN with
      ⟨hIrregularSource, hSourceBad, hIrregularHost, hMixedEdges⟩
    have hrough := roughSourceInterval_card_lower hmod
    have hsourceCardNat := card_regularSource_add_irregular L Ab Kb N
    have hsourceCardReal :
        ((S.card : ℕ) : ℝ) +
            ((irregularRoughSource L Ab Kb N).card : ℝ) =
          ((roughSourceInterval L N).card : ℝ) := by
      dsimp [S]
      exact_mod_cast hsourceCardNat
    have hrough' :
        (N : ℝ) / 4 * roughDensity L ≤
          ((roughSourceInterval L N).card : ℝ) := by
      convert hrough using 1 <;> unfold roughDensity <;> ring
    have hScard :
        (N : ℝ) * (roughDensity L / 2) / 4 ≤ (S.card : ℝ) := by
      nlinarith
    have hhostCardNat := card_regularOddHost_add_irregular L Ao Ko N
    have hhostCardReal :
        ((O.card : ℕ) : ℝ) +
            ((irregularOddHost L Ao Ko N).card : ℝ) = (N : ℝ) := by
      dsimp [O]
      exact_mod_cast hhostCardNat
    have hOcard :
        (N : ℝ) - (N : ℝ) * (roughDensity L / 2) / 32 ≤
          (O.card : ℝ) := by
      nlinarith
    have hMixedBadNat :=
      Erdos327.card_mixedBad_le_card_mixedEdges O
        (Erdos327.rankFilteredSource (Erdos327.upto N) S
          ArithmeticFunction.cardFactors)
    have hMixedBadReal :
        ((Erdos327.mixedBad O
          (Erdos327.rankFilteredSource (Erdos327.upto N) S
            ArithmeticFunction.cardFactors)).card : ℝ) ≤
          ((Erdos327.mixedEdges O
            (Erdos327.rankFilteredSource (Erdos327.upto N) S
              ArithmeticFunction.cardFactors)).card : ℝ) := by
      exact_mod_cast hMixedBadNat
    let B :=
      Erdos327.rankFilteredSource (Erdos327.upto N) S
        ArithmeticFunction.cardFactors
    have hBsubsetS : B ⊆ S :=
      Erdos327.rankFilteredSource_subset (Erdos327.upto N) S
        ArithmeticFunction.cardFactors
    have hBsubset : B ⊆ Erdos327.upto N :=
      hBsubsetS.trans (regularSource_subset_upto L Ab Kb N hN2)
    have hBadm : Erdos327.TwoAdmissible B :=
      Erdos327.twoAdmissible_rankFilteredSource
        (regularSource_subset_upto L Ab Kb N hN2)
    have hBcard :
        (N : ℝ) * (roughDensity L / 2) / 8 ≤ (B.card : ℝ) := by
      dsimp [B]
      have hfiltered := Erdos327.rankFilteredSource_card_lower
        (U := Erdos327.upto N) (S := S)
        (score := ArithmeticFunction.cardFactors)
        hScard (by
          dsimp [S]
          convert hSourceBad using 1 <;> ring)
      linarith
    have hOsubset : O ⊆ Erdos327.upto (2 * N) :=
      regularOddHost_subset_upto L Ao Ko N
    have hodd : ∀ a ∈ O, Odd a := by
      intro a ha
      exact odd_of_mem_regularOddHost ha
    have hbad :
        ((Erdos327.mixedBad O B).card : ℝ) ≤
          (N : ℝ) * (roughDensity L / 2) / 32 := by
      dsimp [B, S, O] at hMixedEdges hMixedBadReal ⊢
      nlinarith
    refine ⟨Erdos327.assembledSet O B,
      Erdos327.assembledSet_subset_upto hOsubset hBsubset,
      Erdos327.oneAdmissible_assembledSet hodd hBadm, ?_⟩
    have hdensity := Erdos327.assembly_density_bound
      (ρ := roughDensity L / 2) hodd hOcard hbad hBcard
    convert hdensity using 1 <;> ring
  let η : ℝ := roughDensity L / 32
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (roughDensity_pos hL) (by norm_num)
  obtain ⟨K, hK⟩ := exists_nat_ge (4 * (1 + η) / η)
  refine ⟨max (2 * N₀) K, ?_⟩
  intro X hX
  have htwoN₀ : 2 * N₀ ≤ X :=
    (le_max_left (2 * N₀) K).trans hX
  have hhalfN₀ : N₀ ≤ X / 2 := by omega
  rcases heven (X / 2) hhalfN₀ with ⟨A, hA, hAdm, hcard⟩
  refine ⟨A, ?_, hAdm, ?_⟩
  · intro a ha
    have ha' := Erdos327.mem_upto.mp (hA ha)
    apply Erdos327.mem_upto.mpr
    constructor
    · exact ha'.1
    · exact ha'.2.trans (by omega)
  · have hKX_nat : K ≤ X := (le_max_right (2 * N₀) K).trans hX
    have hKX : (K : ℝ) ≤ (X : ℝ) := by exact_mod_cast hKX_nat
    have hscale : 4 * (1 + η) ≤ η * (X : ℝ) := by
      have hdiv : 4 * (1 + η) / η ≤ (X : ℝ) := hK.trans hKX
      simpa [mul_comm] using (div_le_iff₀ hη).mp hdiv
    have hfloorNat : X ≤ 2 * (X / 2) + 1 := by omega
    have hfloorCast :
        (X : ℝ) / 2 - 1 ≤ ((X / 2 : ℕ) : ℝ) := by
      have hfloorCast' :
          (X : ℝ) ≤ 2 * ((X / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast hfloorNat
      linarith
    have hcard' :
        (1 + η) * ((X / 2 : ℕ) : ℝ) ≤ (A.card : ℝ) := by
      dsimp [η]
      convert hcard using 1 <;> ring
    calc
      (1 / 2 + roughDensity L / 128) * (X : ℝ) =
          (1 / 2 + η / 4) * (X : ℝ) := by
        dsimp [η]
        ring
      _ ≤ (1 + η) * ((X : ℝ) / 2 - 1) := by nlinarith
      _ ≤ (1 + η) * ((X / 2 : ℕ) : ℝ) := by gcongr
      _ ≤ (A.card : ℝ) := hcard'

/-- The existing construction, at the concrete cutoff above, certifies the
explicit rational gain `explicitEpsilon`.  The ambient threshold remains a
finite existential because the terminal and positive-residual limits are
not effectivized in this Level-1 certificate. -/
theorem erdos327Conclusion_explicit :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ A : Finset ℕ,
        A ⊆ Erdos327.upto N ∧
        Erdos327.OneAdmissible A ∧
        (1 / 2 + explicitEpsilon) * (N : ℝ) ≤ (A.card : ℝ) := by
  rcases explicit_exists_forall_card_rankBad_le_roughDensity with
    ⟨Ns, hsource⟩
  rcases explicit_exists_forall_sum_mixedRefined_add_one_le_roughDensity with
    ⟨Nm, hmixed⟩
  let Nbase : ℕ :=
    max Ns (max Nm (max explicitL (4 * roughPrimeModulus explicitL)))
  have hL : 3 ≤ explicitL := three_le_sourceCoupledCutoff explicitJ
  have hmodulus :
      ∀ N ≥ Nbase, 4 * roughPrimeModulus explicitL ≤ N := by
    intro N hN
    exact
      (le_trans
        (le_max_right explicitL (4 * roughPrimeModulus explicitL))
        (le_trans
          (le_max_right Nm
            (max explicitL (4 * roughPrimeModulus explicitL)))
          (le_max_right Ns
            (max Nm
              (max explicitL
                (4 * roughPrimeModulus explicitL)))))).trans hN
  have hest :
      ∀ N ≥ Nbase,
        ((irregularRoughSource explicitL sourceAnatomySlope
          explicitSourceBudget N).card : ℝ) ≤
            (N : ℝ) * roughDensity explicitL / 8 ∧
        ((Erdos327.rankBad (Erdos327.upto N)
          (regularSource explicitL sourceAnatomySlope
            explicitSourceBudget N)
          ArithmeticFunction.cardFactors).card : ℝ) ≤
            (N : ℝ) * roughDensity explicitL / 16 ∧
        ((irregularOddHost explicitL oddAnatomySlope
          (oddBudget explicitL) N).card : ℝ) ≤
            (N : ℝ) * roughDensity explicitL / 64 ∧
        ((Erdos327.mixedEdges
          (regularOddHost explicitL oddAnatomySlope
            (oddBudget explicitL) N)
          (Erdos327.rankFilteredSource (Erdos327.upto N)
            (regularSource explicitL sourceAnatomySlope
              explicitSourceBudget N)
            ArithmeticFunction.cardFactors)).card : ℝ) ≤
              (N : ℝ) * roughDensity explicitL / 64 := by
    intro N hN
    have hNs : Ns ≤ N :=
      (le_max_left Ns
        (max Nm
          (max explicitL (4 * roughPrimeModulus explicitL)))).trans hN
    have hNm : Nm ≤ N :=
      (le_trans
        (le_max_left Nm
          (max explicitL (4 * roughPrimeModulus explicitL)))
        (le_max_right Ns
          (max Nm
            (max explicitL (4 * roughPrimeModulus explicitL))))).trans hN
    have hLN : explicitL ≤ N :=
      (le_trans
        (le_max_left explicitL (4 * roughPrimeModulus explicitL))
        (le_trans
          (le_max_right Nm
            (max explicitL (4 * roughPrimeModulus explicitL)))
          (le_max_right Ns
            (max Nm
              (max explicitL
                (4 * roughPrimeModulus explicitL)))))).trans hN
    have hN2 : 2 ≤ N := by omega
    have hsourceN := hsource N hNs
    have hoddL := explicit_oddBudget_meets_tail
    have hmixedSum := hmixed N hNm
    have hmixedCard :=
      card_mixedEdges_le_refinedScheduled_sum_add_one
        (L := explicitL) (N := N)
        (Ab := sourceAnatomySlope) (Kb := explicitSourceBudget)
        (Ao := oddAnatomySlope) (Ko := oddBudget explicitL)
        (qb := mixedSourceWeightBase) (qo := mixedOddWeightBase)
        hL hN2 mixedSourceWeightBase_gt_one
        mixedOddWeightBase_gt_one mixedRegularityExponent_nonneg
    exact
      ⟨irregularRoughSource_le_one_eighth
          hL hLN hN2 explicitSourceBudget_spec,
        hsourceN,
        irregularOddHost_le_one_sixty_fourth
          hL (by omega) (by omega) hoddL,
        hmixedCard.trans hmixedSum⟩
  rcases erdos327_fixed_gain_of_canonical_estimates
      (L := explicitL) (Ab := sourceAnatomySlope)
      (Kb := explicitSourceBudget) (Ao := oddAnatomySlope)
      (Ko := oddBudget explicitL) hL hmodulus hest with
    ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro N hN
  rcases hN₀ N hN with ⟨A, hA, hAdm, hcard⟩
  refine ⟨A, hA, hAdm, ?_⟩
  have hgain :
      (1 / 2 + explicitEpsilon) * (N : ℝ) ≤
        (1 / 2 + roughDensity explicitL / 128) * (N : ℝ) :=
    mul_le_mul_of_nonneg_right
      (by
        simpa only [add_comm] using
          add_le_add_left explicitEpsilon_le_final_gain (1 / 2))
      (Nat.cast_nonneg N)
  exact hgain.trans hcard

theorem erdos327Conclusion_with_explicitEpsilon :
    Erdos327.Erdos327Conclusion := by
  refine ⟨explicitEpsilon, explicitEpsilon_pos, ?_⟩
  exact erdos327Conclusion_explicit


end Analytic

end

end Erdos327.EffectiveAudit

#print axioms Erdos327.EffectiveAudit.Analytic.erdos327Conclusion_explicit
#print axioms Erdos327.EffectiveAudit.Analytic.erdos327Conclusion_with_explicitEpsilon
