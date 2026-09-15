import LiuWang.Proof.DirichletZeroCount.Remainder.UniformHorizontal
import LiuWang.Proof.DirichletZeroCount.Remainder.FamilyPhase

/-! # Sharpened nonprincipal mother bounds at every original closed height -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology Classical
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

def uniformCountBound (q : ℕ) (a y : ℝ) : ℝ :=
  (y * Real.log ((q : ℝ) / Real.pi) + Real.pi + 2 * uniformHorizontalFee q y +
    sourceGammaMain a y) / Real.pi

theorem uniformHorizontalFee_continuous (q : ℕ) : Continuous (uniformHorizontalFee q) := by
  have hl : Continuous (fun H : ℝ => Real.log (|H| + 2)) :=
    (show Continuous (fun H : ℝ => |H| + 2) by fun_prop).log
      (fun H => ne_of_gt (by positivity : 0 < |H| + 2))
  unfold uniformHorizontalFee
  fun_prop

theorem uniformCountBound_continuous (q : ℕ) {a : ℝ} (ha : 0 < a) :
    Continuous (uniformCountBound q a) := by
  have hh := uniformHorizontalFee_continuous q
  have hg := sourceGammaMain_continuous ha
  unfold uniformCountBound
  fun_prop

theorem count_primitive_regular_le_uniform {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {H : ℝ} (hH : 0 < H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → chi.LFunction s ≠ 0) :
    (count chi 0 H : ℝ) ≤ uniformCountBound q (parityShift chi) H := by
  have hp := horizontal_L_im_abs_le_uniform_regular hchi hprim (H := H) (ne_of_gt hH)
    (fun s h0 h1 he => hreg s h0 h1 (by rw [he, abs_of_nonneg hH.le]))
  have hm := horizontal_L_im_abs_le_uniform_regular hchi hprim (H := -H) (neg_ne_zero.mpr hH.ne')
    (fun s h0 h1 he => hreg s h0 h1 (by rw [he, abs_neg, abs_of_nonneg hH.le]))
  simp only [uniformHorizontalFee, abs_neg] at hm
  change |(HIntegral (logDeriv chi.LFunction) (1 / 2) 2 (-H)).im| ≤ uniformHorizontalFee q H at hm
  apply (completed_count_le_horizontal (b := 2) hchi hprim le_rfl hH.le hreg).trans
  unfold uniformCountBound parityShift
  split_ifs <;> apply div_le_div_of_nonneg_right _ Real.pi_pos.le <;>
    linarith [(abs_le.mp hm).2, (abs_le.mp hp).1]

theorem count_primitive_closed_le_uniform {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {y : ℝ} (hy : 0 ≤ y) :
    (count chi 0 y : ℝ) ≤ uniformCountBound q (parityShift chi) y := by
  by_contra h
  have hlt : uniformCountBound q (parityShift chi) y < (count chi 0 y : ℝ) := lt_of_not_ge h
  have hmem := (uniformCountBound_continuous q (parityShift_pos chi)).continuousAt.preimage_mem_nhds
    (Iio_mem_nhds hlt)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  obtain ⟨H, hyH, hHr, hp, _, hreg⟩ := Applications.exists_common_count_plateau q (y := y) hr
  have hclose : H ∈ Metric.ball y r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hyH)]
    linarith
  have hb := count_primitive_regular_le_uniform hchi hprim (hy.trans_lt hyH) (hreg chi)
  rw [hp chi 0 H hyH.le le_rfl] at hb
  exact (not_lt_of_ge hb) (hsub hclose)

theorem count_nonprincipal_uniform_conductor {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {alpha y : ℝ} (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (count chi alpha y : ℝ) ≤ uniformCountBound chi.conductor (parityShift chi) y := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hp := count_primitive_closed_le_uniform
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi)
    chi.primitiveCharacter_isPrimitive hy
  rw [parityShift_primitive] at hp
  rw [count_eq_primitive chi hchi]
  exact (Nat.cast_le.mpr (count_antitone_alpha chi.primitiveCharacter y ha)).trans hp

theorem uniformCountBound_mono_modulus {d q : ℕ} (hd : 0 < d) (hdq : d ≤ q)
    {a y : ℝ} (hy : 0 ≤ y) : uniformCountBound d a y ≤ uniformCountBound q a y := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hdqR : (d : ℝ) ≤ q := Nat.cast_le.mpr hdq
  have hlog := Real.log_le_log hdR hdqR
  have hlogpi := Real.log_le_log (div_pos hdR Real.pi_pos)
    (div_le_div_of_nonneg_right hdqR Real.pi_pos.le)
  unfold uniformCountBound uniformHorizontalFee
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  have h1 := mul_le_mul_of_nonneg_left hlogpi hy
  have h2 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 5 * Real.pi / 2 + 4 by positivity)
  nlinarith

theorem count_nonprincipal_uniform_modulus {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {alpha y : ℝ} (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (count chi alpha y : ℝ) ≤ uniformCountBound q (parityShift chi) y :=
  (count_nonprincipal_uniform_conductor hchi ha hy).trans
    (uniformCountBound_mono_modulus (Nat.pos_of_ne_zero chi.conductor_ne_zero)
      (BombieriVinogradov.DirichletCharacter.conductor_le_level chi) hy)

theorem uniformCountBound_le_previous (q : ℕ) (a y : ℝ) :
    uniformCountBound q a y ≤ phaseCountBound q a y := by
  have hl : 0 ≤ Real.log (|y| + 2) := Real.log_nonneg (by linarith [abs_nonneg y])
  unfold uniformCountBound phaseCountBound uniformHorizontalFee horizontalFee
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  linarith [Real.pi_lt_four]

end LiuWang.Proof.DirichletZeroCount.Remainder
