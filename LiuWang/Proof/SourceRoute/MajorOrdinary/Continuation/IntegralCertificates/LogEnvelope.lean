import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.NuPower
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
noncomputable section

open Set

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates

def logNu (u : ℝ) : ℝ := 1.781076 * Real.log u + 2.50637 / Real.log u

def logNuD1 (u : ℝ) : ℝ := (1.781076 - 2.50637 / Real.log u ^ 2) / u

def logNuD2 (u : ℝ) : ℝ :=
  (-1.781076 + 2.50637 / Real.log u ^ 2 + 2 * 2.50637 / Real.log u ^ 3) / u ^ 2

def logNuD3 (u : ℝ) : ℝ :=
  (2 * 1.781076 - 2.50637 *
    (2 / Real.log u ^ 2 + 6 / Real.log u ^ 3 + 6 / Real.log u ^ 4)) / u ^ 3

def logNuD4 (u : ℝ) : ℝ :=
  (-6 * 1.781076 + 2.50637 *
    (6 / Real.log u ^ 2 + 22 / Real.log u ^ 3 +
      36 / Real.log u ^ 4 + 24 / Real.log u ^ 5)) / u ^ 4

theorem logNu_deriv {u : ℝ} (hu : 1 < u) : HasDerivAt logNu (logNuD1 u) u := by
  have h := (Real.hasDerivAt_log (by linarith : u ≠ 0))
  convert! (h.const_mul 1.781076).add
    ((hasDerivAt_const u 2.50637).div h (Real.log_pos hu).ne') using 1
  dsimp [logNuD1]
  field_simp
  ring

theorem logNuD1_deriv {u : ℝ} (hu : 1 < u) : HasDerivAt logNuD1 (logNuD2 u) u := by
  have h := Real.hasDerivAt_log (by linarith : u ≠ 0)
  convert! (((hasDerivAt_const u 2.50637).div (h.pow 2)
    (pow_ne_zero _ (Real.log_pos hu).ne')).const_sub
    1.781076).div (hasDerivAt_id u) (by linarith : u ≠ 0) using 1
  dsimp [logNuD2, Pi.pow_apply]
  field_simp
  ring

theorem logNuD2_deriv {u : ℝ} (hu : 1 < u) : HasDerivAt logNuD2 (logNuD3 u) u := by
  have h := Real.hasDerivAt_log (by linarith : u ≠ 0)
  have hn := (Real.log_pos hu).ne'
  convert! (((hasDerivAt_const u 2.50637).div (h.pow 2) (pow_ne_zero _ hn)).const_add
    (-1.781076) |>.add
    ((hasDerivAt_const u (2 * 2.50637)).div (h.pow 3) (pow_ne_zero _ hn))).div
      ((hasDerivAt_id u).pow 2) (pow_ne_zero _ (by linarith : u ≠ 0)) using 1
  dsimp [logNuD3, Pi.pow_apply]
  field_simp
  ring

theorem logNuD3_deriv {u : ℝ} (hu : 1 < u) : HasDerivAt logNuD3 (logNuD4 u) u := by
  have h := Real.hasDerivAt_log (by linarith : u ≠ 0)
  have hn := (Real.log_pos hu).ne'
  convert! (((((hasDerivAt_const u 2).div (h.pow 2) (pow_ne_zero _ hn)).add
    ((hasDerivAt_const u 6).div (h.pow 3) (pow_ne_zero _ hn)) |>.add
    ((hasDerivAt_const u 6).div (h.pow 4) (pow_ne_zero _ hn))).const_mul 2.50637).const_sub
    (2 * 1.781076)).div ((hasDerivAt_id u).pow 3)
      (pow_ne_zero _ (by linarith : u ≠ 0)) using 1
  dsimp [logNuD4, Pi.pow_apply]
  field_simp
  ring

theorem log_ge_two_point_four {u : ℝ} (hu : 11.5 ≤ u) : 2.4 ≤ Real.log u := by
  apply (Real.le_log_iff_exp_le (by linarith)).mpr
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4)
    (by norm_num : (0.4 : ℝ) ≤ 1) (n := 6) (by norm_num)
  have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
  rw [← Real.exp_nat_mul] at he
  have hp := mul_le_mul he h (Real.exp_pos _).le (by norm_num)
  rw [← Real.exp_add] at hp
  norm_num [Finset.sum_range_succ, Nat.factorial] at hp
  linarith

theorem inv_log_pow_le {u : ℝ} (hu : 11.5 ≤ u) (k : ℕ) :
    1 / Real.log u ^ k ≤ 1 / (2.4 : ℝ) ^ k :=
  one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_left₀ (by norm_num) (log_ge_two_point_four hu) k)

theorem logNuD2_nonpos {u : ℝ} (hu : 11.5 ≤ u) : logNuD2 u ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have h2 := inv_log_pow_le hu 2
  have h3 := inv_log_pow_le hu 3
  simp only [div_eq_mul_inv, one_mul] at h2 h3 ⊢
  norm_num at h2 h3
  linarith

theorem logNuD4_nonpos {u : ℝ} (hu : 11.5 ≤ u) : logNuD4 u ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have h2 := inv_log_pow_le hu 2
  have h3 := inv_log_pow_le hu 3
  have h4 := inv_log_pow_le hu 4
  have h5 := inv_log_pow_le hu 5
  simp only [div_eq_mul_inv, one_mul] at h2 h3 h4 h5 ⊢
  norm_num at h2 h3 h4 h5
  linarith

theorem nu_le_logNu {x : ℝ} (hx : 100000 ≤ x) : nu x ≤ logNu (Real.log x) := by
  unfold nu logNu
  exact add_le_add (mul_le_mul_of_nonneg_right exp_gamma_le_decimal
    (by linarith [(large_log_bounds hx).2] : 0 ≤ Real.log (Real.log x))) le_rfl

theorem log_input_ge {x : ℝ} (hx : 100000 ≤ x) : 11.5 ≤ Real.log x := by
  have h : (11.5 : ℝ) ≤ Real.log 100000 := by
    rw [show (100000 : ℝ) = (2 * 5) ^ 5 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]
    norm_num
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  exact h.trans (Real.log_le_log (by norm_num) hx)

theorem minimum_of_deriv_sign {F D : ℝ → ℝ} {a u t : ℝ} (hu : a ≤ u) (ht : a ≤ t)
    (hder : ∀ z, a ≤ z → HasDerivAt F (D z) z)
    (hleft : ∀ z, a ≤ z → z ≤ u → D z ≤ 0)
    (hright : ∀ z, u ≤ z → 0 ≤ D z) : F u ≤ F t := by
  by_cases htu : t ≤ u
  · have hm : AntitoneOn F (Icc t u) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        (fun z hz => (hder z (ht.trans hz.1)).continuousAt.continuousWithinAt)
        (fun z hz => (hder z (ht.trans (interior_subset hz).1)).hasDerivWithinAt)
        (fun z hz => hleft z (ht.trans (interior_subset hz).1) (interior_subset hz).2)
    exact hm ⟨le_rfl, htu⟩ ⟨htu, le_rfl⟩ htu
  · have hut : u ≤ t := le_of_not_ge htu
    have hm : MonotoneOn F (Icc u t) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
        (fun z hz => (hder z (hu.trans hz.1)).continuousAt.continuousWithinAt)
        (fun z hz => (hder z (hu.trans (interior_subset hz).1)).hasDerivWithinAt)
        (fun z hz => hright z (interior_subset hz).1)
    exact hm ⟨le_rfl, hut⟩ ⟨hut, le_rfl⟩ hut

def tangent (t u : ℝ) : ℝ := logNu t + logNuD1 t * (u - t)

theorem tangent_deriv {t : ℝ} (ht : 1 < t) (u : ℝ) :
    HasDerivAt (fun z => tangent z u) (logNuD2 t * (u - t)) t := by
  convert! (logNu_deriv ht).add
    ((logNuD1_deriv ht).mul ((hasDerivAt_id t).const_sub u)) using 1
  dsimp
  ring

theorem logNu_le_tangent {t u : ℝ} (ht : 11.5 ≤ t) (hu : 11.5 ≤ u) :
    logNu u ≤ tangent t u := by
  have h := minimum_of_deriv_sign hu ht (fun z hz => tangent_deriv (by linarith) u)
    (fun z hz hzu => mul_nonpos_of_nonpos_of_nonneg (logNuD2_nonpos hz) (sub_nonneg.mpr hzu))
    (fun z huz => mul_nonneg_of_nonpos_of_nonpos (logNuD2_nonpos (hu.trans huz))
      (sub_nonpos.mpr huz))
  simpa only [tangent, sub_self, mul_zero, add_zero] using h

def cubic (t u : ℝ) : ℝ :=
  logNu t + logNuD1 t * (u - t) + logNuD2 t * (u - t) ^ 2 / 2 +
    logNuD3 t * (u - t) ^ 3 / 6

theorem cubic_deriv {t : ℝ} (ht : 1 < t) (u : ℝ) :
    HasDerivAt (fun z => cubic z u) (logNuD4 t * (u - t) ^ 3 / 6) t := by
  have hd := (hasDerivAt_id t).const_sub u
  convert! (((logNu_deriv ht).add ((logNuD1_deriv ht).mul hd)).add
    (((logNuD2_deriv ht).mul (hd.pow 2)).div_const 2)).add
      (((logNuD3_deriv ht).mul (hd.pow 3)).div_const 6) using 1
  dsimp
  ring

theorem logNu_le_cubic {t u : ℝ} (ht : 11.5 ≤ t) (hu : 11.5 ≤ u) :
    logNu u ≤ cubic t u := by
  have h := minimum_of_deriv_sign hu ht (fun z hz => cubic_deriv (by linarith) u)
    (fun z hz hzu => div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (logNuD4_nonpos hz) (pow_nonneg (sub_nonneg.mpr hzu) 3))
      (by norm_num))
    (fun z huz => div_nonneg
      (mul_nonneg_of_nonpos_of_nonpos (logNuD4_nonpos (hu.trans huz))
        (show (u - z) ^ 3 ≤ 0 by
          rw [pow_succ]
          exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.mpr huz)))
      (by norm_num))
  simpa only [cubic, sub_self, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), mul_zero, zero_div, add_zero] using h

theorem nu_sq_le_cubic_sq {x t : ℝ} (hx : 100000 ≤ x) (ht : 11.5 ≤ t) :
    nu x ^ 2 ≤ cubic t (Real.log x) ^ 2 :=
  pow_le_pow_left₀ (nu_pos hx).le ((nu_le_logNu hx).trans (logNu_le_cubic ht (log_input_ge hx))) 2

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates
