import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.FiveFourthsBudget
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ShiftQuadrature

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

def negativeEighthBound (x l : ℝ) (k : ℕ) : ℝ :=
  1 / (x ^ (k / 8) * l ^ (k % 8))

theorem rpow_negative_eighth_bound {x l : ℝ} (hx : 0 < x) (hl : 0 < l)
    (hl8 : l ^ 8 ≤ x) (k : ℕ) :
    x ^ (-(k : ℝ) / 8) ≤ negativeEighthBound x l k := by
  have hp : l ^ (8 : ℝ) ≤ x := by simpa only [Real.rpow_ofNat] using! hl8
  have hr := (Real.le_rpow_inv_iff_of_pos hl.le hx.le (by norm_num : (0 : ℝ) < 8)).mpr hp
  norm_num at hr
  have he : (k : ℝ) / 8 = ((k / 8 : ℕ) : ℝ) + (1 / 8 : ℝ) * (k % 8 : ℕ) := by
    have h : ((k % 8 : ℕ) : ℝ) + 8 * (k / 8 : ℕ) = k := by
      exact_mod_cast Nat.mod_add_div k 8
    linarith
  unfold negativeEighthBound
  rw [neg_div, Real.rpow_neg hx.le, inv_eq_one_div]
  apply one_div_le_one_div_of_le (by positivity)
  rw [he, Real.rpow_add hx, Real.rpow_natCast, Real.rpow_mul_natCast hx.le]
  gcongr

def eighthZetaUpper (k : ℕ) : ℝ :=
  1 + negativeEighthBound 2 (1090507 / 1000000) k +
    negativeEighthBound 3 (573601 / 500000) k +
    8 / ((k : ℝ) - 8) * negativeEighthBound (7 / 2) (584761 / 500000) (k - 8)

theorem one_le_eighthZetaUpper {k : ℕ} (hk : 10 ≤ k) : 1 ≤ eighthZetaUpper k := by
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hk8 : 0 < (k : ℝ) - 8 := by linarith
  have h2 : 0 ≤ negativeEighthBound 2 (1090507 / 1000000) k := by
    unfold negativeEighthBound
    positivity
  have h3 : 0 ≤ negativeEighthBound 3 (573601 / 500000) k := by
    unfold negativeEighthBound
    positivity
  have h7 : 0 ≤ 8 / ((k : ℝ) - 8) *
      negativeEighthBound (7 / 2) (584761 / 500000) (k - 8) := by
    unfold negativeEighthBound
    positivity
  unfold eighthZetaUpper
  linarith

theorem norm_zeta_eighth_grid_upper {k : ℕ} (hk : 10 ≤ k) :
    ‖riemannZeta (((k : ℝ) / 8 : ℝ) : ℂ)‖ ≤ eighthZetaUpper k := by
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : 1 < (k : ℝ) / 8 := by linarith
  have h := norm_zeta_real_midpoint_upper hs 3
  have h2 := rpow_negative_eighth_bound (x := 2) (l := 1090507 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) k
  have h3 := rpow_negative_eighth_bound (x := 3) (l := 573601 / 500000)
    (by norm_num) (by norm_num) (by norm_num) k
  have h7 := rpow_negative_eighth_bound (x := 7 / 2) (l := 584761 / 500000)
    (by norm_num) (by norm_num) (by norm_num) (k - 8)
  have he : (1 : ℝ) - (k : ℝ) / 8 = -((k - 8 : ℕ) : ℝ) / 8 := by
    rw [Nat.cast_sub (by omega : 8 ≤ k)]
    push_cast
    ring
  have hzero : -((k : ℝ) / 8) ≠ 0 := by linarith
  norm_num [Finset.sum_range_succ, Real.zero_rpow hzero] at h
  rw [he] at h
  simp only [neg_div] at h2 h3
  calc
    ‖riemannZeta (((k : ℝ) / 8 : ℝ) : ℂ)‖ ≤
        1 + 2 ^ (-((k : ℝ) / 8)) + 3 ^ (-((k : ℝ) / 8)) +
          (7 / 2 : ℝ) ^ (-((k - 8 : ℕ) : ℝ) / 8) / ((k : ℝ) / 8 - 1) := by
      simpa using! h
    _ ≤ 1 + negativeEighthBound 2 (1090507 / 1000000) k +
        negativeEighthBound 3 (573601 / 500000) k +
        negativeEighthBound (7 / 2) (584761 / 500000) (k - 8) / ((k : ℝ) / 8 - 1) := by
      gcongr
    _ = eighthZetaUpper k := by
      unfold eighthZetaUpper
      field_simp

theorem log_real_upper_certificate {x R : ℝ} (hx : 1 ≤ x)
    (hR : 2 * ((∑ i ∈ Finset.range 8,
      ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1)) +
      ((x - 1) / (x + 1)) ^ 17 / (1 - ((x - 1) / (x + 1)) ^ 2)) ≤ R) :
    Real.log x ≤ R := by
  have hd : 0 < x + 1 := by linarith
  have h0 : 0 ≤ (x - 1) / (x + 1) := by positivity
  have h1 : (x - 1) / (x + 1) < 1 := by
    rw [div_lt_one hd]
    linarith
  have h := Real.log_div_le_sum_range_add h0 h1 8
  have he : (1 + (x - 1) / (x + 1)) / (1 - (x - 1) / (x + 1)) = x := by
    field_simp
    ring
  rw [he] at h
  norm_num only [show (2 * 8 + 1 : ℕ) = 17 by norm_num] at h
  linarith

theorem eighth_grid_log_certificate {k : ℕ} (hk : 10 ≤ k) (R : ℝ)
    (hR : 2 * ((∑ i ∈ Finset.range 8,
      ((eighthZetaUpper k - 1) / (eighthZetaUpper k + 1)) ^ (2 * i + 1) / (2 * i + 1)) +
      ((eighthZetaUpper k - 1) / (eighthZetaUpper k + 1)) ^ 17 /
        (1 - ((eighthZetaUpper k - 1) / (eighthZetaUpper k + 1)) ^ 2)) ≤ R) :
    realLogZeta ((k : ℝ) / 8) ≤ R := by
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hz := one_le_norm_zeta_real (x := (k : ℝ) / 8) (by linarith)
  have h := Real.log_le_log (by linarith) (norm_zeta_eighth_grid_upper hk)
  exact h.trans (log_real_upper_certificate (one_le_eighthZetaUpper hk) hR)

#print axioms norm_zeta_eighth_grid_upper
#print axioms eighth_grid_log_certificate

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
