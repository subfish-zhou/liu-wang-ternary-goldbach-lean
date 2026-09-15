import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.Nu

set_option autoImplicit false
noncomputable section

open Set

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1

private theorem gamma_lower : (0.569 : ℝ) ≤ Real.eulerMascheroniConstant := by
  have hlog : Real.log (65 : ℝ) ≤ 6 * Real.log 2 + 1 / 64 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 65 / 64)
    rw [Real.log_div (by norm_num) (by norm_num),
      show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow] at h
    linarith
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 64
  norm_num [Real.eulerMascheroniSeq] at h
  linarith [Real.log_two_lt_d9]

private theorem exp_gamma_lower : (1.766 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
  apply le_trans _ (Real.exp_le_exp.mpr gamma_lower)
  apply le_trans _ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.569) 6)
  norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem loglog_27_lower : (1.192 : ℝ) ≤ Real.log (Real.log 27) := by
  have hlog3 : (1.098 : ℝ) ≤ Real.log 3 := by
    have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) 5
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hlog27 : (3.294 : ℝ) ≤ Real.log 27 := by
    rw [show (27 : ℝ) = 3 ^ (3 : ℕ) by norm_num, Real.log_pow]
    linarith
  have he : Real.exp (0.192 : ℝ) ≤ 1.211671 := by
    apply (Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.192)
      (by norm_num : (0.192 : ℝ) ≤ 1) (n := 10) (by norm_num)).trans
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have he' : Real.exp (1.192 : ℝ) ≤ 3.294 := by
    rw [show (1.192 : ℝ) = 1 + 0.192 by norm_num, Real.exp_add]
    calc
      _ ≤ 2.718281829 * 1.211671 :=
        mul_le_mul (by linarith [Real.exp_one_lt_d9]) he
          (Real.exp_pos _).le (by norm_num)
      _ ≤ _ := by norm_num
  exact (Real.le_log_iff_exp_le (by linarith : 0 < Real.log 27)).mpr
    (he'.trans hlog27)

theorem loglog_pos_of_three_le {x : ℝ} (hx : 3 ≤ x) :
    0 < Real.log (Real.log x) := by
  apply Real.log_pos
  apply (Real.lt_log_iff_exp_lt (by linarith : 0 < x)).mpr
  linarith [Real.exp_one_lt_d9]

theorem two_le_nu {x : ℝ} (hx : 3 ≤ x) : 2 ≤ nu x := by
  have hu := loglog_pos_of_three_le hx
  have he := mul_le_mul_of_nonneg_right exp_gamma_ge_one hu.le
  unfold nu
  apply (mul_le_mul_iff_right₀ hu).mp
  field_simp
  nlinarith [sq_nonneg (Real.log (Real.log x) - 1),
    mul_le_mul_of_nonneg_right he hu.le]

theorem nu_pos_of_three_le {x : ℝ} (hx : 3 ≤ x) : 0 < nu x :=
  lt_of_lt_of_le (by norm_num) (two_le_nu hx)

theorem nu_monotone_27 : MonotoneOn nu (Ici 27) := by
  intro x hx y _ hxy
  have hx0 : 0 < x := by have := hx; change 27 ≤ x at this; linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by
    have := hx; change 27 ≤ x at this; linarith)
  have hu : (1.192 : ℝ) ≤ Real.log (Real.log x) :=
    loglog_27_lower.trans (Real.log_le_log
      (Real.log_pos (by norm_num : (1 : ℝ) < 27))
      (Real.log_le_log (by norm_num) hx))
  have huv := Real.log_le_log hlogx (Real.log_le_log hx0 hxy)
  have hv := hu.trans huv
  have hu0 : 0 < Real.log (Real.log x) := by linarith
  have hv0 : 0 < Real.log (Real.log y) := by linarith
  have hprod : (2.50637 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant *
      (Real.log (Real.log x) * Real.log (Real.log y)) := by
    calc
      _ ≤ 1.766 * (1.192 * 1.192) := by norm_num
      _ ≤ _ := mul_le_mul exp_gamma_lower
        (mul_le_mul hu hv (by norm_num) hu0.le) (by norm_num) (Real.exp_pos _).le
  have hdiff := mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hprod)
  unfold nu
  apply (mul_le_mul_iff_left₀ (mul_pos hu0 hv0)).mp
  field_simp
  nlinarith [hdiff]

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1
