import LiuWang.Proof.GlobalZeroDensity.Strip.Growth

/-! Exact-width three-lines interpolation for the actual regularized detector. -/

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped Topology
open Complex.HadamardThreeLines
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.GlobalZeroDensity.Strip

def rightWeight (y σ : ℝ) : ℝ := (σ - 1 / 2) / (1 / 2 + delta y)

theorem regularG_diffContOnCl {y : ℝ} (hy : 10000 ≤ y) :
    DiffContOnCl ℂ (regularG y) (verticalStrip (1 / 2) (1 + delta y)) := by
  apply DifferentiableOn.diffContOnCl
  rw [verticalStrip, Complex.closure_preimage_re,
    closure_Ioo (show (1 / 2 : ℝ) ≠ 1 + delta y by have := delta_bounds hy; linarith)]
  intro s hs
  exact (differentiableAt_regularG (by linarith : 0 < y)
    (closed_strip_safe hy hs)).differentiableWithinAt

theorem weight_bounds {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) :
    0 ≤ rightWeight y σ ∧ rightWeight y σ ≤ 1 := by
  have hd := delta_bounds hy
  unfold rightWeight
  constructor
  · exact div_nonneg (sub_nonneg.mpr hσ.1) (by linarith)
  · apply (div_le_one (by linarith)).mpr
    linarith [hσ.2]

theorem regularG_interpolation {y : ℝ} (hy : 10000 ≤ y) {s : ℂ}
    (hs : s ∈ verticalClosedStrip (1 / 2) (1 + delta y)) :
    ‖regularG y s‖ ^ 2 ≤
      (33 * y ^ 2) ^ (1 - rightWeight y s.re) *
        ((7 / 4) * Real.log y ^ 4) ^ rightWeight y s.re := by
  have hd := delta_bounds hy
  have hdc : DiffContOnCl ℂ (fun s => regularG y s ^ 2)
      (verticalStrip (1 / 2) (1 + delta y)) :=
    ⟨(regularG_diffContOnCl hy).differentiableOn.pow 2,
      (regularG_diffContOnCl hy).continuousOn.pow 2⟩
  obtain ⟨B, hB⟩ := regularG_bounded hy
  have hb : BddAbove ((norm ∘ (fun s => regularG y s ^ 2)) ''
      verticalClosedStrip (1 / 2) (1 + delta y)) := by
    refine ⟨(max B 0) ^ 2, ?_⟩
    rintro v ⟨z, hz, rfl⟩
    rw [Function.comp_apply, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((hB (mem_image_of_mem _ hz)).trans (le_max_left _ _)) 2
  have h := norm_le_interp_of_mem_verticalClosedStrip'
    (show (1 / 2 : ℝ) < 1 + delta y by linarith) hs hdc hb
    (a := 33 * y ^ 2) (b := (7 / 4) * Real.log y ^ 4) ?_ ?_
  · rw [norm_pow] at h
    simpa only [rightWeight, show 1 + delta y - 1 / 2 = 1 / 2 + delta y by ring] using h
  · intro z hz
    have hz' : z.re = 1 / 2 := hz
    have he : z = (1 / 2 : ℂ) + z.im * Complex.I := by
      apply Complex.ext <;> simp [hz']
    rw [norm_pow, he]
    exact regularG_critical_max hy z.im
  · intro z hz
    rw [norm_pow]
    exact regularG_moving_sq hy hz

theorem log_boundary_budget :
    Real.log (7 / 4) + 8 / 3 ≤ Real.log 33 := by
  have he1 : Real.exp 1 ≤ 11 / 4 :=
    le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he1 8
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have he3 : Real.exp (8 / 3) ^ 3 = Real.exp 8 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he : Real.exp (8 / 3) ≤ 18 := by
    by_contra h
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 18) (le_of_lt (lt_of_not_ge h)) 3
    rw [he3] at hh
    norm_num at hh
    linarith
  apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 33)).mpr
  rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 7 / 4)]
  linarith

theorem interpolation_le_source {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) :
    (33 * y ^ 2) ^ (1 - rightWeight y σ) *
        ((7 / 4) * Real.log y ^ 4) ^ rightWeight y σ ≤
      33 * y ^ (4 * (1 - σ)) * (Real.log y) ^ (8 * σ - 4) := by
  have hl := log_ge_nine hy
  have hy0 : 0 < y := by linarith
  have hl0 : 0 < Real.log y := by linarith
  have hll : 0 ≤ Real.log (Real.log y) := Real.log_nonneg (by linarith)
  have hw := weight_bounds hy hσ
  have hd := delta_bounds hy
  have hid : rightWeight y σ * (1 / 2 + delta y) = σ - 1 / 2 := by
    unfold rightWeight
    exact div_mul_cancel₀ _ (ne_of_gt (by linarith : 0 < 1 / 2 + delta y))
  have hdl : delta y * Real.log y = 2 / 3 := by
    unfold delta
    field_simp
  have he : 4 * delta y * Real.log y ≤
      Real.log 33 - Real.log (7 / 4) + 8 * delta y * Real.log (Real.log y) := by
    have hlog := log_boundary_budget
    nlinarith [mul_nonneg hd.1.le hll]
  rw [Real.rpow_def_of_pos (by positivity : 0 < 33 * y ^ 2),
    Real.rpow_def_of_pos (by positivity : 0 < (7 / 4) * Real.log y ^ 4),
    Real.rpow_def_of_pos hy0, Real.rpow_def_of_pos hl0,
    Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_pow, Real.log_pow, ← Real.exp_add]
  have h33 : (33 : ℝ) = Real.exp (Real.log 33) := (Real.exp_log (by norm_num)).symm
  conv_rhs => rw [h33]
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hp := mul_le_mul_of_nonneg_left he hw.1
  have hrel : (1 / 2 + delta y) * rightWeight y σ = σ - 1 / 2 := by linarith
  have hrelL := congrArg (fun x : ℝ => x * Real.log y) hrel
  have hrell := congrArg (fun x : ℝ => x * Real.log (Real.log y)) hrel
  norm_num only [Nat.cast_ofNat] at *
  nlinarith

theorem regularG_strip_source {y : ℝ} (hy : 10000 ≤ y) {s : ℂ}
    (hs : s ∈ verticalClosedStrip (1 / 2) (1 + delta y)) :
    ‖regularG y s‖ ^ 2 ≤
      33 * y ^ (4 * (1 - s.re)) * (Real.log y) ^ (8 * s.re - 4) :=
  (regularG_interpolation hy hs).trans (interpolation_le_source hy hs)

end LiuWang.Proof.GlobalZeroDensity.Strip
