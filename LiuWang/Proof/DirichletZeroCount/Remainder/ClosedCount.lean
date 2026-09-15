import LiuWang.Proof.DirichletZeroCount.Remainder.HorizontalFee

/-! # A genuine closed-height count with an explicit logarithmic remainder -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology Classical
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

def parityShift {q : ℕ} (chi : Character q) : ℝ :=
  if chi.Even then 1 / 2 else 3 / 2

theorem parityShift_pos {q : ℕ} (chi : Character q) : 0 < parityShift chi := by
  unfold parityShift
  split_ifs <;> norm_num

def phaseCountBound (q : ℕ) (a H : ℝ) : ℝ :=
  (H * Real.log ((q : ℝ) / Real.pi) + Real.pi + 2 * horizontalFee q H +
    sourceGammaMain a H) / Real.pi

theorem horizontalFee_continuous (q : ℕ) : Continuous (horizontalFee q) := by
  have hl : Continuous (fun H : ℝ => Real.log (|H| + 2)) :=
    (show Continuous (fun H : ℝ => |H| + 2) by fun_prop).log
      (fun H => ne_of_gt (by positivity : 0 < |H| + 2))
  unfold horizontalFee
  fun_prop

theorem phaseCountBound_continuous (q : ℕ) {a : ℝ} (ha : 0 < a) :
    Continuous (phaseCountBound q a) := by
  have hh := horizontalFee_continuous q
  have hg := sourceGammaMain_continuous ha
  unfold phaseCountBound
  fun_prop

theorem count_primitive_regular_le {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {H : ℝ} (hH : 2 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → chi.LFunction s ≠ 0) :
    (count chi 0 H : ℝ) ≤ phaseCountBound q (parityShift chi) H := by
  have hH0 : 0 ≤ H := by linarith
  have hp := horizontal_L_im_abs_le_regular hchi hprim (H := H)
    (by simpa only [abs_of_nonneg hH0] using hH)
    (fun s h0 h1 he => hreg s h0 h1 (by rw [he, abs_of_nonneg hH0]))
  have hm := horizontal_L_im_abs_le_regular hchi hprim (H := -H)
    (by simpa only [abs_neg, abs_of_nonneg hH0] using hH)
    (fun s h0 h1 he => hreg s h0 h1 (by rw [he, abs_neg, abs_of_nonneg hH0]))
  simp only [horizontalFee, abs_neg] at hm
  change |(HIntegral (logDeriv chi.LFunction) (1 / 2) 2 (-H)).im| ≤ horizontalFee q H at hm
  apply (completed_count_le_horizontal (b := 2) hchi hprim le_rfl hH0 hreg).trans
  unfold phaseCountBound parityShift
  split_ifs <;> apply div_le_div_of_nonneg_right _ Real.pi_pos.le <;>
    linarith [(abs_le.mp hm).2, (abs_le.mp hp).1]

theorem count_primitive_closed_le {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {y : ℝ} (hy : 2 ≤ y) :
    (count chi 0 y : ℝ) ≤ phaseCountBound q (parityShift chi) y := by
  by_contra h
  have hlt : phaseCountBound q (parityShift chi) y < (count chi 0 y : ℝ) := lt_of_not_ge h
  have hmem := (phaseCountBound_continuous q (parityShift_pos chi)).continuousAt.preimage_mem_nhds
    (Iio_mem_nhds hlt)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  obtain ⟨H, hyH, hHr, hplateau, _, hregular⟩ := Applications.exists_common_count_plateau q (y := y) hr
  have hclose : H ∈ Metric.ball y r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hyH)]
    linarith
  have hupper := count_primitive_regular_le hchi hprim (show 2 ≤ H by linarith) (hregular chi)
  rw [hplateau chi 0 H hyH.le le_rfl] at hupper
  exact (not_lt_of_ge hupper) (hsub hclose)

theorem count_primitive_alpha_le {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {alpha y : ℝ} (ha : 0 ≤ alpha) (hy : 2 ≤ y) :
    (count chi alpha y : ℝ) ≤ phaseCountBound q (parityShift chi) y :=
  (Nat.cast_le.mpr (count_antitone_alpha chi y ha)).trans (count_primitive_closed_le hchi hprim hy)

theorem count_conductor_phase_le {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {alpha y : ℝ} (ha : 0 ≤ alpha) (hy : 2 ≤ y) :
    (count chi alpha y : ℝ) ≤ phaseCountBound chi.conductor (parityShift chi.primitiveCharacter) y := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  rw [count_eq_primitive chi hchi]
  exact count_primitive_alpha_le
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi)
    chi.primitiveCharacter_isPrimitive ha hy

end LiuWang.Proof.DirichletZeroCount.Remainder
