import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.HalfStripBoundary
import Mathlib.Analysis.Complex.AbsMax

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set Bornology Metric
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaValidation

def sourceStripDamped (e : ℝ) (s : ℂ) : ℂ :=
  sourceHalfStripQuotient s * Complex.exp (Complex.I * (e : ℂ) * s)

theorem sourceStripDamped_norm (e : ℝ) (s : ℂ) :
    ‖sourceStripDamped e s‖ =
      ‖sourceHalfStripQuotient s‖ * Real.exp (-e * s.im) := by
  simp [sourceStripDamped, Complex.norm_exp, mul_re, mul_im]

theorem sourceStripDamped_norm_le {e : ℝ} (he : 0 ≤ e) {s : ℂ} (hs : 0 ≤ s.im) :
    ‖sourceStripDamped e s‖ ≤ ‖sourceHalfStripQuotient s‖ := by
  rw [sourceStripDamped_norm]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (by nlinarith))

theorem sourceStripDamped_differentiableAt (e : ℝ) {s : ℂ}
    (hs : 0 < s.re) (ht : 0 < s.im) :
    DifferentiableAt ℂ (sourceStripDamped e) s := by
  unfold sourceStripDamped
  exact (sourceHalfStripQuotient_differentiableAt hs ht).mul (by fun_prop)

theorem sourceStripDamped_top {e R : ℝ} (he : 0 < e) (hR : 1 ≤ R)
    (hRe : 20 / e ^ 2 ≤ R) {s : ℂ}
    (hs : s.re ∈ Icc (1 / 2 : ℝ) (5 / 4)) (ht : s.im = R) :
    ‖sourceStripDamped e s‖ ≤ 1 := by
  have hprod := (div_le_iff₀ (sq_pos_of_pos he)).mp hRe
  have hmul := mul_le_mul_of_nonneg_right hprod (by linarith : 0 ≤ R)
  have hp := Real.pow_div_factorial_le_exp (e * R) (by positivity) 2
  norm_num at hp
  have hgrowth : 8 + 2 * R ≤ Real.exp (e * R) := by nlinarith
  have h := sourceHalfStripQuotient_linear_growth hs (by simpa [ht] using hR)
  rw [ht] at h
  rw [sourceStripDamped_norm, ht, neg_mul, Real.exp_neg, ← div_eq_mul_inv]
  exact (div_le_one (Real.exp_pos _)).mpr (h.le.trans hgrowth)

theorem sourceHalfStrip_left_violation {z : ℂ}
    (hz : z.re ∈ Icc (1 / 2 : ℝ) (5 / 4)) (ht : 128 * Real.pi ≤ z.im)
    (hbad : 1 < ‖sourceHalfStripQuotient z‖) :
    ∃ t : ℝ, 128 * Real.pi ≤ t ∧
      1 < ‖sourceHalfStripQuotient (criticalPoint t)‖ := by
  have ht0 : 0 < z.im := lt_of_lt_of_le (by positivity) ht
  have hn0 : 0 < ‖sourceHalfStripQuotient z‖ := by linarith
  let e : ℝ := Real.log ‖sourceHalfStripQuotient z‖ / (2 * z.im)
  have he : 0 < e := div_pos (Real.log_pos hbad) (by positivity)
  have hbad' : 1 < ‖sourceStripDamped e z‖ := by
    rw [sourceStripDamped_norm]
    have hlog : -e * z.im = -(Real.log ‖sourceHalfStripQuotient z‖ / 2) := by
      dsimp [e]
      field_simp
    rw [hlog, ← Real.exp_log hn0, Real.log_exp, ← Real.exp_add]
    exact Real.one_lt_exp_iff.mpr (by linarith [Real.log_pos hbad])
  let R : ℝ := max (z.im + 1) (1 + 20 / e ^ 2)
  have hzR : z.im < R := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hR : 1 ≤ R :=
    le_trans (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ 20 / e ^ 2)) (le_max_right _ _)
  have hRe : 20 / e ^ 2 ≤ R :=
    le_trans (by linarith : 20 / e ^ 2 ≤ 1 + 20 / e ^ 2) (le_max_right _ _)
  have hbR : 128 * Real.pi < R := ht.trans_lt hzR
  let U : Set ℂ := Ioo (1 / 2 : ℝ) (5 / 4) ×ℂ Ioo (128 * Real.pi) R
  have hcl : closure U = Icc (1 / 2 : ℝ) (5 / 4) ×ℂ Icc (128 * Real.pi) R := by
    dsimp only [U]
    rw [closure_reProdIm, closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 5 / 4),
      closure_Ioo hbR.ne]
  have hfront : frontier U =
      (Icc (1 / 2 : ℝ) (5 / 4) ×ℂ {128 * Real.pi, R}) ∪
        ({1 / 2, 5 / 4} ×ℂ Icc (128 * Real.pi) R) := by
    dsimp only [U]
    rw [frontier_reProdIm, closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 5 / 4),
      closure_Ioo hbR.ne, frontier_Ioo (by norm_num : (1 / 2 : ℝ) < 5 / 4),
      frontier_Ioo hbR]
  have hd : DiffContOnCl ℂ (sourceStripDamped e) U := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    rw [hcl] at hw
    exact (sourceStripDamped_differentiableAt e (by linarith [hw.1.1])
      (lt_of_lt_of_le (by positivity) hw.2.1)).differentiableWithinAt
  have hzcl : z ∈ closure U := by rw [hcl]; exact ⟨hz, ht, hzR.le⟩
  have hex : ∃ w : ℂ, w ∈ frontier U ∧ 1 < ‖sourceStripDamped e w‖ := by
    by_contra h
    push Not at h
    have hle := Complex.norm_le_of_forall_mem_frontier_norm_le
      ((isBounded_Ioo _ _).reProdIm (isBounded_Ioo _ _)) hd h hzcl
    exact (not_le_of_gt hbad') hle
  obtain ⟨w, hw, hwbad⟩ := hex
  have hwcl := frontier_subset_closure hw
  rw [hcl] at hwcl
  have hwt : 0 ≤ w.im := le_trans (by positivity) hwcl.2.1
  have hwle := sourceStripDamped_norm_le he.le hwt
  have hwleft : w.re = 1 / 2 := by
    rw [hfront] at hw
    rcases hw with ⟨hwx, hwy⟩ | ⟨hwx, hwy⟩
    · rcases hwy with hbot | htop
      · exact False.elim ((not_le_of_gt hwbad)
          (hwle.trans (sourceHalfStripQuotient_bottom_boundary hwx hbot)))
      · exact False.elim ((not_le_of_gt hwbad)
          (sourceStripDamped_top he hR hRe hwx htop))
    · rcases hwx with hleft | hright
      · exact hleft
      · exact False.elim ((not_le_of_gt hwbad)
          (hwle.trans (sourceHalfStripQuotient_right_boundary hright
            (lt_of_lt_of_le (by positivity) hwy.1))))
  have hwpoint : w = criticalPoint w.im := by
    apply Complex.ext <;> simp [criticalPoint, hwleft]
  refine ⟨w.im, hwcl.2.1, ?_⟩
  rw [← hwpoint]
  exact hwbad.trans_le hwle

#print axioms sourceStripDamped_top
#print axioms sourceHalfStrip_left_violation

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
