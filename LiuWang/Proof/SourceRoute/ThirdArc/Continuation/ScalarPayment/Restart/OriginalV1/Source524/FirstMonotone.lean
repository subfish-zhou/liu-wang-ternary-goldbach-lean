import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Scale
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524

def firstPart (s : ℝ) : ℝ :=
  3100 * 1.8771 * logNu s * s ^ (1 / 15 : ℝ) *
    (254231 * densityLog s ^ 5 + 17102 * densityLog s ^ 6) *
    Real.exp (-(9 / 20 : ℝ) * s - 0.478 * 3100 / (s + Real.log lowHeight))

theorem logNu_monotone : MonotoneOn logNu (Set.Ici 24) := by
  intro s hs t ht hst
  change 24 ≤ s at hs
  change 24 ≤ t at ht
  have hslog := log_s_ge_three hs
  have htlog := log_s_ge_three ht
  have hl := Real.log_le_log (by linarith : 0 < s) hst
  have he : 1 ≤ Real.exp Real.eulerMascheroniConstant :=
    Real.one_le_exp_iff.mpr (by linarith [Real.one_half_lt_eulerMascheroniConstant])
  have hp : (1 : ℝ) ≤ Real.log s * Real.log t := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ Real.log s - 3) (by linarith : 0 ≤ Real.log t - 3)]
  have hc : 2.50637 / (Real.log s * Real.log t) ≤ (1 : ℝ) := by
    apply (div_le_one (by linarith : 0 < Real.log s * Real.log t)).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ Real.log s - 3) (by linarith : 0 ≤ Real.log t - 3)]
  have h := mul_nonneg (sub_nonneg.mpr hl) (show
    0 ≤ Real.exp Real.eulerMascheroniConstant - 2.50637 / (Real.log s * Real.log t) by linarith)
  have hid : logNu t - logNu s = (Real.log t - Real.log s) *
      (Real.exp Real.eulerMascheroniConstant - 2.50637 / (Real.log s * Real.log t)) := by
    unfold logNu
    have hs0 : Real.log s ≠ 0 := by linarith
    have ht0 : Real.log t ≠ 0 := by linarith
    field_simp
    ring
  linarith only [h, hid]

private def densityKernel (n : ℕ) (s : ℝ) : ℝ :=
  densityLog s ^ n *
    Real.exp (-(9 / 20 : ℝ) * s - 0.478 * 3100 / (s + Real.log lowHeight))

private theorem densityKernel_deriv (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 24 ≤ s) :
    HasDerivAt (densityKernel n)
      (densityLog s ^ (n - 1) *
        Real.exp (-(9 / 20 : ℝ) * s - 0.478 * 3100 / (s + Real.log lowHeight)) *
        (n * (1 + 1 / s) + densityLog s *
          (-(9 / 20 : ℝ) + 0.478 * 3100 / (s + Real.log lowHeight) ^ 2))) s := by
  have hs0 : s ≠ 0 := by linarith
  have ht0 : s + Real.log lowHeight ≠ 0 := by linarith [lowHeight_log_bounds.1]
  have hd : HasDerivAt densityLog (1 + 1 / s) s := by
    have hh := (((hasDerivAt_id s).const_mul 10000).log (by positivity : 10000 * s ≠ 0))
    have hd := (hasDerivAt_id s).add hh
    apply hd.congr_deriv
    dsimp
    field_simp
  have he : HasDerivAt
      (fun s : ℝ => -(9 / 20 : ℝ) * s - 0.478 * 3100 / (s + Real.log lowHeight))
      (-(9 / 20 : ℝ) + 0.478 * 3100 / (s + Real.log lowHeight) ^ 2) s := by
    have h := ((hasDerivAt_id s).const_mul (-(9 / 20 : ℝ))).sub
      ((hasDerivAt_const s (0.478 * 3100)).div
        ((hasDerivAt_id s).add_const (Real.log lowHeight)) ht0)
    apply h.congr_deriv
    dsimp
    ring
  have h := (hd.pow n).mul he.exp
  apply h.congr_deriv
  have hp : densityLog s ^ n = densityLog s ^ (n - 1) * densityLog s := by
    rw [← pow_succ]
    congr 1
    omega
  rw [Pi.pow_apply, hp]
  ring

theorem densityKernel_monotone (n : ℕ) (hn : 5 ≤ n) :
    MonotoneOn (fun s : ℝ => densityLog s ^ n *
      Real.exp (-(9 / 20 : ℝ) * s - 0.478 * 3100 / (s + Real.log lowHeight)))
      (Set.Icc 24 48.24) := by
  change MonotoneOn (densityKernel n) (Set.Icc 24 48.24)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 24 48.24)
    (fun s hs => (densityKernel_deriv n (by omega) hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (densityKernel_deriv n (by omega) (interior_subset hs).1).hasDerivWithinAt)
  intro s hs
  have hs := interior_subset hs
  have hz := (heightLog_bounds hs.1).2
  have hheight : heightLog s ≤ 14 := by
    apply (Real.log_le_iff_le_exp (by linarith [hs.1] : 0 < 10000 * s)).mpr
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
      (by linarith [Real.exp_one_gt_d9] : (2.7 : ℝ) ≤ Real.exp 1) 14
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith [hs.2]
  have hzup : densityLog s ≤ 63 := by unfold densityLog; linarith [hs.2]
  have ht : 0 < s + Real.log lowHeight ∧ s + Real.log lowHeight ≤ 59 := by
    constructor <;> linarith [hs.1, hs.2, lowHeight_log_bounds.1, lowHeight_log_bounds.2]
  have hden : (s + Real.log lowHeight) ^ 2 ≤ (59 : ℝ) ^ 2 :=
    pow_le_pow_left₀ ht.1.le ht.2 2
  have hdiv : (0.42 : ℝ) ≤ 0.478 * 3100 / (s + Real.log lowHeight) ^ 2 := by
    apply (le_div_iff₀ (pow_pos ht.1 2)).mpr
    nlinarith only [hden]
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hs0 : 0 < s := by linarith [hs.1]
  have hinv : 0 ≤ 1 / s := by positivity
  have h1 : (5 : ℝ) ≤ n * (1 + 1 / s) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n) hinv]
  have h2 := mul_le_mul_of_nonneg_left hdiv (by linarith : 0 ≤ densityLog s)
  have hcore : 0 ≤ (n : ℝ) * (1 + 1 / s) + densityLog s *
      (-(9 / 20 : ℝ) + 0.478 * 3100 / (s + Real.log lowHeight) ^ 2) := by
    nlinarith only [h1, h2, hzup]
  exact mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le) hcore

theorem firstPart_monotone : MonotoneOn firstPart (Set.Icc 24 48.24) := by
  intro s hs t ht hst
  have hnu := (logNu_bounds hs.1).2
  have hnut := (logNu_bounds ht.1).2
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hz := (heightLog_bounds hs.1).2
  have hzt := (heightLog_bounds ht.1).2
  have hp := Real.rpow_le_rpow hs0 hst (by norm_num : (0 : ℝ) ≤ 1 / 15)
  have hk5 := densityKernel_monotone 5 (by norm_num) hs ht hst
  have hk6 := densityKernel_monotone 6 (by norm_num) hs ht hst
  have hk := add_le_add (mul_le_mul_of_nonneg_left hk5 (by norm_num : (0 : ℝ) ≤ 254231))
    (mul_le_mul_of_nonneg_left hk6 (by norm_num : (0 : ℝ) ≤ 17102))
  have h := mul_le_mul (mul_le_mul (logNu_monotone hs.1 ht.1 hst) hp
    (Real.rpow_nonneg hs0 _) hnut) hk (by positivity) (by positivity)
  have h := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 3100 * 1.8771)
  unfold firstPart
  nlinarith only [h]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524
