import LiuWang.Proof.Campaign20260915.RSSection8Scalar.EndpointM

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Set

namespace LiuWang.Proof.Campaign20260915.RSSection8Scalar

theorem logM_lower {t : ℝ} (ht : 0 < t) (a : ℝ) :
    t / (2 * t ^ 2 + 1) - a / t ≤ logM t a := by
  have hlog := Real.one_sub_inv_le_log_of_pos
    (show 0 < 1 + 1 / (2 * t ^ 2) by positivity)
  have he : 1 - (1 + 1 / (2 * t ^ 2))⁻¹ = 1 / (2 * t ^ 2 + 1) := by
    field_simp
    ring
  rw [he] at hlog
  have hh := mul_le_mul_of_nonneg_left hlog ht.le
  rw [mul_one_div] at hh
  unfold logM
  linarith

/-- The `M` side of the last comparison in Lemma 12, uniformly rather than by sampling. -/
theorem M_047_gt_0028 {x : ℝ} (hx : 16 ≤ Real.log x) :
    0.028 / Real.log x < M x 0.47 := by
  let t := Real.log x
  have ht16 : 16 ≤ t := hx
  have ht : 0 < t := by linarith
  have hs : (256 : ℝ) ≤ t ^ 2 := by nlinarith
  have hd : 0 < 2 * t ^ 2 + 1 := by positivity
  have hfrac : (0.028 + 0.47 : ℝ) < t ^ 2 / (2 * t ^ 2 + 1) := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  have hsmall : 0.028 / t < t / (2 * t ^ 2 + 1) - 0.47 / t := by
    apply (div_lt_iff₀ ht).mpr
    have he : (t / (2 * t ^ 2 + 1) - 0.47 / t) * t =
        t ^ 2 / (2 * t ^ 2 + 1) - 0.47 := by
      field_simp
    rw [he]
    linarith
  exact hsmall.trans_le (logM_lower ht 0.47)

theorem M_031_antitoneOn {A : ℝ} (hA : 1 < A) (hlog : 2 ≤ Real.log A) :
    AntitoneOn (fun x => M x 0.31) (Ici A) := by
  apply M_antitoneOn_of_square hA (by norm_num)
  have hs : (4 : ℝ) ≤ Real.log A ^ 2 := by nlinarith
  nlinarith

theorem M_047_antitoneOn {A : ℝ} (hA : 1 < A) (hlog : 5 ≤ Real.log A) :
    AntitoneOn (fun x => M x 0.47) (Ici A) := by
  apply M_antitoneOn_of_square hA (by norm_num)
  have hs : (25 : ℝ) ≤ Real.log A ^ 2 := by nlinarith
  nlinarith

#print axioms M_047_gt_0028
#print axioms M_031_antitoneOn
#print axioms M_047_antitoneOn

end LiuWang.Proof.Campaign20260915.RSSection8Scalar
