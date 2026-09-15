import LiuWang.Proof.DirichletZeroCount.Remainder.HorizontalKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Integrating the actual multiplicity-indexed compensated zero series -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology Classical
open LiuWang.Proof.Interfaces (Character CompletedZeroIndex completedZeroValue completedZeroValue_re_mem_Ioo)
open LiuWang.Proof.LocalAnalyticBounds
open LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount.Remainder

theorem exists_separation_of_regular {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {H : ℝ}
    (havoid : ∀ p : CompletedZeroIndex chi, H - (completedZeroValue p).im ≠ 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ p : CompletedZeroIndex chi,
      B⁻¹ ≤ |(completedZeroValue p).im - H| := by
  let S := (finite_closedZeroWindow hchi hprim H).toFinset
  let B : ℝ := 1 + ∑ p ∈ S, |H - (completedZeroValue p).im|⁻¹
  have hb1 : 1 ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (abs_nonneg _)))
  have hb : 0 < B := by linarith
  refine ⟨B, hb, ?_⟩
  intro p
  rw [abs_sub_comm]
  have hp : 0 < |H - (completedZeroValue p).im| := abs_pos.mpr (havoid p)
  have hle : |H - (completedZeroValue p).im|⁻¹ ≤ B := by
    by_cases hm : p ∈ S
    · have hh := Finset.single_le_sum (fun p (_ : p ∈ S) =>
        inv_nonneg.mpr (abs_nonneg (H - (completedZeroValue p).im))) hm
      dsimp [B]
      linarith
    · have hg : 1 < |H - (completedZeroValue p).im| := by
        apply lt_of_not_ge
        intro hh
        exact hm ((finite_closedZeroWindow hchi hprim H).mem_toFinset.mpr hh)
      exact (inv_le_one_of_one_le₀ hg.le).trans hb1
  apply (inv_le_iff_one_le_mul₀ hb).mpr
  have hh := mul_le_mul_of_nonneg_right hle hp.le
  simpa only [inv_mul_cancel₀ hp.ne', mul_comm] using hh

def compensatedImag {q : ℕ} [NeZero q] (chi : Character q) (H : ℝ)
    (p : CompletedZeroIndex chi) (x : ℝ) : ℝ :=
  (1 / ((x : ℂ) + (H : ℂ) * I - completedZeroValue p) -
    1 / (referencePoint H - completedZeroValue p)).im

theorem compensatedImag_integrable {q : ℕ} [NeZero q] {chi : Character q} {H : ℝ}
    {p : CompletedZeroIndex chi} (hp : H - (completedZeroValue p).im ≠ 0) :
    IntervalIntegrable (compensatedImag chi H p) volume (1 / 2) 2 := by
  simpa only [compensatedImag, sub_im] using!
    (reciprocal_im_integrable hp (1 / 2) 2).sub intervalIntegrable_const

theorem compensated_integral_tsum {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {H : ℝ}
    (havoid : ∀ p : CompletedZeroIndex chi, H - (completedZeroValue p).im ≠ 0) :
    (∫ x in (1 / 2 : ℝ)..2, ∑' p : CompletedZeroIndex chi, compensatedImag chi H p x) =
      ∑' p : CompletedZeroIndex chi, ∫ x in (1 / 2 : ℝ)..2, compensatedImag chi H p x := by
  obtain ⟨B, hB, hsep⟩ := exists_separation_of_regular hchi hprim havoid
  let K (p : CompletedZeroIndex chi) := (1 / (referencePoint H - completedZeroValue p)).re
  let C : ℝ := 3 / 2 + (3 / 2) ^ 2 * B
  have hk : Summable K := summable_symmetricCompletedLFunction_zeroKernel_re hchi hprim
    (s := referencePoint H) (by norm_num [referencePoint])
  have hkpos (p : CompletedZeroIndex chi) : 0 < K p := by
    have hp : 0 < (referencePoint H - completedZeroValue p).re := by
      have hr := (completedZeroValue_re_mem_Ioo hchi hprim p).2
      simpa [referencePoint] using (show 0 < 2 - (completedZeroValue p).re by linarith)
    have hn : referencePoint H - completedZeroValue p ≠ 0 := by
      intro he
      simp [he] at hp
    dsimp [K]
    rw [one_div, inv_re]
    exact div_pos hp (normSq_pos.mpr hn)
  let : Countable (CompletedZeroIndex chi) :=
    Set.countable_univ_iff.mp (hk.countable_support.mono (by
      intro p _
      exact (hkpos p).ne'))
  have hab : (1 / 2 : ℝ) ≤ 2 := by norm_num
  have hi (p : CompletedZeroIndex chi) := compensatedImag_integrable (havoid p)
  have hnorm (p : CompletedZeroIndex chi) :
      (∫ x in (1 / 2 : ℝ)..2, ‖compensatedImag chi H p x‖) ≤ (3 / 2) * C * K p := by
    have hp (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
        ‖compensatedImag chi H p x‖ ≤ C * K p := by
      rw [Real.norm_eq_abs]
      apply (abs_im_le_norm _).trans
      exact norm_reciprocal_difference_le_reference_kernel (s := (x : ℂ) + (H : ℂ) * I) hB (hsep p) (by simp)
        (by norm_num : (0 : ℝ) ≤ 3 / 2) (by simp; linarith [hx.1]) (by simpa using hx.2)
        ⟨(completedZeroValue_re_mem_Ioo hchi hprim p).1.le,
          (completedZeroValue_re_mem_Ioo hchi hprim p).2.le⟩
    have hh := intervalIntegral.integral_mono_on (μ := volume) hab (hi p).norm
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C * K p) volume (1 / 2) 2) hp
    rw [intervalIntegral.integral_const] at hh
    simpa only [smul_eq_mul, show 2 - (1 / 2 : ℝ) = 3 / 2 by norm_num, mul_assoc] using hh
  have hsum : Summable (fun p : CompletedZeroIndex chi =>
      ∫ x in (1 / 2 : ℝ)..2, ‖compensatedImag chi H p x‖) :=
    Summable.of_nonneg_of_le (fun p => intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _))
      hnorm (hk.mul_left ((3 / 2) * C))
  simp only [intervalIntegral.integral_of_le hab] at hsum ⊢
  exact (integral_tsum_of_summable_integral_norm
    (fun p => (hi p).1) hsum).symm

theorem compensated_sum_integral_abs_le {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {H : ℝ}
    (havoid : ∀ p : CompletedZeroIndex chi, H - (completedZeroValue p).im ≠ 0) :
    |∫ x in (1 / 2 : ℝ)..2, ∑' p : CompletedZeroIndex chi, compensatedImag chi H p x| ≤
      (5 * Real.pi / 2 + 4) * (Real.log q / 2 + Real.log (|H| + 2) / 2 + 2) := by
  let K (p : CompletedZeroIndex chi) := (1 / (referencePoint H - completedZeroValue p)).re
  have hk : Summable K := summable_symmetricCompletedLFunction_zeroKernel_re hchi hprim
    (s := referencePoint H) (by norm_num [referencePoint])
  have hm (p : CompletedZeroIndex chi) :
      |∫ x in (1 / 2 : ℝ)..2, compensatedImag chi H p x| ≤ (5 * Real.pi / 2 + 4) * K p :=
    compensated_im_integral_le_kernel
      ⟨(completedZeroValue_re_mem_Ioo hchi hprim p).1.le,
        (completedZeroValue_re_mem_Ioo hchi hprim p).2.le⟩ (havoid p)
  have hsum : Summable (fun p : CompletedZeroIndex chi =>
      |∫ x in (1 / 2 : ℝ)..2, compensatedImag chi H p x|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hm (hk.mul_left _)
  rw [compensated_integral_tsum hchi hprim havoid]
  have hh := norm_tsum_le_tsum_norm (f := fun p : CompletedZeroIndex chi =>
    ∫ x in (1 / 2 : ℝ)..2, compensatedImag chi H p x)
    (by simpa only [Real.norm_eq_abs] using hsum)
  rw [Real.norm_eq_abs] at hh
  simp only [Real.norm_eq_abs] at hh
  apply hh.trans
  apply (hsum.tsum_le_tsum hm (hk.mul_left _)).trans
  rw [tsum_mul_left]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [heightKernel_eq] using reference_mass_improved hchi hprim H

end LiuWang.Proof.DirichletZeroCount.Remainder
