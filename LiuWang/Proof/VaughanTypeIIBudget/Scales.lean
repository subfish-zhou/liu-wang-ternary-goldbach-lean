import LiuWang.Proof.VaughanTypeIIBudget.Definitions

/-! 真实二进个数、几何和及原参数的实幂恒等式。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeIIBudget

open Interfaces Parameters VaughanTypeII

theorem kappa_le : kappa ≤ (0.436 : ℝ) := by
  unfold kappa
  apply Real.sqrt_le_iff.mpr
  norm_num

theorem sqrt_three_le : Real.sqrt 3 ≤ (7 / 4 : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  norm_num

theorem geometric_constant_le : 2 + Real.sqrt 2 ≤ (7 / 2 : ℝ) := by
  have h : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  linarith

theorem log_le_div_thirty_two {x : ℝ} (hx : 2048 ≤ x) :
    Real.log x ≤ x / 32 := by
  have hx0 : 0 ≤ x := by linarith
  apply (Real.log_le_iff_le_exp (by linarith : 0 < x)).mpr
  have hquad := Real.quadratic_le_exp_of_nonneg (x := x / 32) (by positivity)
  nlinarith [mul_nonneg hx0 (show 0 ≤ x - 2048 by linarith)]

theorem log_Y_bounds {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    0 ≤ Real.log ((N : ℝ) / sourceVaughanV N) ∧
      Real.log ((N : ℝ) / sourceVaughanV N) ≤ (3 / 5 : ℝ) * sourceL N := by
  have hn := exp_2000_le_of_exp_3100_le hN
  constructor
  · exact Real.log_nonneg ((one_le_div (sourceVaughanV_pos hn)).mpr
      (sourceVaughanV_lt_natCast hn).le)
  · rw [Real.log_div (natCast_pos_of_exp_le hN).ne' (sourceVaughanV_pos hn).ne',
      log_sourceVaughanV hn]
    change sourceL N - (2 * sourceL N + Real.log (sourceL N)) / 5 ≤ _
    linarith [Real.log_nonneg (one_le_sourceL hn)]

theorem dyadicCount_le_L_third {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (dyadicCount N : ℝ) ≤ sourceL N / 3 := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_ge_3100 hN
  have hlog := log_le_div_thirty_two (show 2048 ≤ sourceL N by linarith)
  have htwo : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have htwo0 : 0 < 5 * Real.log 2 := by positivity
  have hnum : 0 ≤ sourceL N + 3 * Real.log (sourceL N) := by
    positivity [sourceL_pos hn, Real.log_nonneg (one_le_sourceL hn)]
  have hdiv :
      (sourceL N + 3 * Real.log (sourceL N)) / (5 * Real.log 2) ≤
        (sourceL N + 3 * Real.log (sourceL N)) / (10 / 3) :=
    div_le_div_of_nonneg_left hnum (by norm_num) (by linarith)
  have hcount := dyadicCount_lt_sourceL_bound hn
  linarith

theorem sqrt_upper_identity {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    Real.sqrt (N : ℝ) * sourceL N * Real.sqrt ((N : ℝ) / sourceVaughanU N) =
      termB N := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hNp := natCast_pos_of_exp_le hN
  have hLp := sourceL_pos hn
  have hUp := sourceVaughanU_pos hn
  apply Real.log_injOn_pos (by change (0 : ℝ) < _; positivity)
    (show 0 < termB N from by unfold termB; positivity)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    hLp.ne', Real.log_sqrt hNp.le, Real.log_sqrt (div_pos hNp hUp).le,
    Real.log_div hNp.ne' hUp.ne', log_sourceVaughanU hn]
  unfold termB
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hNp,
    Real.log_rpow hLp]
  change sourceL N / 2 + Real.log (sourceL N) +
    (sourceL N - (2 * sourceL N - 4 * Real.log (sourceL N)) / 5) / 2 =
      (4 / 5 : ℝ) * sourceL N + (7 / 5 : ℝ) * Real.log (sourceL N)
  ring

theorem inv_sqrt_V_identity {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (N : ℝ) * sourceL N * Real.sqrt (sourceL N) / Real.sqrt (sourceVaughanV N) =
      termB N := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hNp := natCast_pos_of_exp_le hN
  have hLp := sourceL_pos hn
  have hVp := sourceVaughanV_pos hn
  apply Real.log_injOn_pos (by change (0 : ℝ) < _; positivity)
    (show 0 < termB N from by unfold termB; positivity)
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul hNp.ne' hLp.ne',
    Real.log_sqrt hLp.le, Real.log_sqrt hVp.le, log_sourceVaughanV hn]
  unfold termB
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hNp,
    Real.log_rpow hLp]
  change sourceL N + Real.log (sourceL N) + Real.log (sourceL N) / 2 -
    (2 * sourceL N + Real.log (sourceL N)) / 5 / 2 =
      (4 / 5 : ℝ) * sourceL N + (7 / 5 : ℝ) * Real.log (sourceL N)
  ring

theorem termA_eq_sqrt (N q : ℕ) :
    termA N q = (N : ℝ) / Real.sqrt q * sourceL N ^ (2 : ℕ) := by
  unfold termA
  rw [show (-1 : ℝ) / 2 = -(1 / 2) by norm_num,
    Real.rpow_neg (Nat.cast_nonneg q), ← Real.sqrt_eq_rpow]
  ring

theorem termC_eq_sqrt {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (q : ℕ) :
    termC N q = Real.sqrt (N : ℝ) * Real.sqrt q *
      sourceL N ^ (2 : ℕ) * Real.sqrt (sourceL N) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  unfold termC
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_eq_rpow (sourceL N),
    mul_assoc (Real.sqrt (N : ℝ) * Real.sqrt q),
    ← Real.rpow_natCast, ← Real.rpow_add hL]
  norm_num

end LiuWang.Proof.VaughanTypeIIBudget
