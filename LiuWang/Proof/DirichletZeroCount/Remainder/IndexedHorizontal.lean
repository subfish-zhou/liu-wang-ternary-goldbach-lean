import LiuWang.Proof.DirichletZeroCount.Remainder.HorizontalSum

/-! # Integrable compensated phase kernels for actual divisor indices -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped Classical
open LiuWang.Proof.LocalAnalyticBounds
open LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate

namespace LiuWang.Proof.DirichletZeroCount.Remainder

def indexedImag {ι : Type*} (rho : ι → ℂ) (H : ℝ) (p : ι) (x : ℝ) : ℝ :=
  (1 / ((x : ℂ) + (H : ℂ) * I - rho p) - 1 / (referencePoint H - rho p)).im

theorem indexed_separation {ι : Type*} {rho : ι → ℂ} {H : ℝ}
    (hf : {p | |H - (rho p).im| ≤ 1}.Finite)
    (ha : ∀ p, H - (rho p).im ≠ 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ p, B⁻¹ ≤ |(rho p).im - H| := by
  let S := hf.toFinset
  let B : ℝ := 1 + ∑ p ∈ S, |H - (rho p).im|⁻¹
  have hb1 : 1 ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => by positivity))
  refine ⟨B, by linarith, fun p => ?_⟩
  have hp : 0 < |H - (rho p).im| := abs_pos.mpr (ha p)
  have hi : |H - (rho p).im|⁻¹ ≤ B := by
    by_cases hm : p ∈ S
    · have hh := Finset.single_le_sum (fun j (_ : j ∈ S) =>
        inv_nonneg.mpr (abs_nonneg (H - (rho j).im))) hm
      dsimp [B]
      linarith
    · have hh : 1 < |H - (rho p).im| := lt_of_not_ge (fun h => hm (hf.mem_toFinset.mpr h))
      exact (inv_le_one_of_one_le₀ hh.le).trans hb1
  rw [abs_sub_comm]
  apply (inv_le_iff_one_le_mul₀ (by linarith : 0 < B)).mpr
  simpa only [inv_mul_cancel₀ hp.ne', mul_comm] using mul_le_mul_of_nonneg_right hi hp.le

theorem indexed_integral_tsum {ι : Type*} {rho : ι → ℂ} {H : ℝ}
    (hr : ∀ p, (rho p).re ∈ Set.Ioo (0 : ℝ) 1)
    (hf : {p | |H - (rho p).im| ≤ 1}.Finite)
    (hk : Summable (fun p => (1 / (referencePoint H - rho p)).re))
    (ha : ∀ p, H - (rho p).im ≠ 0) :
    (∫ x in (1 / 2 : ℝ)..2, ∑' p, indexedImag rho H p x) =
      ∑' p, ∫ x in (1 / 2 : ℝ)..2, indexedImag rho H p x := by
  obtain ⟨B, hB, hsep⟩ := indexed_separation hf ha
  let K (p : ι) := (1 / (referencePoint H - rho p)).re
  let C : ℝ := 3 / 2 + (3 / 2) ^ 2 * B
  have hkpos (p : ι) : 0 < K p := by
    have hp : 0 < (referencePoint H - rho p).re := by
      simpa [referencePoint] using (show 0 < 2 - (rho p).re by linarith [(hr p).2])
    have hn : referencePoint H - rho p ≠ 0 := by intro he; simp [he] at hp
    dsimp [K]
    rw [one_div, inv_re]
    exact div_pos hp (normSq_pos.mpr hn)
  let : Countable ι := Set.countable_univ_iff.mp (hk.countable_support.mono (by
    intro p _
    exact (hkpos p).ne'))
  have hab : (1 / 2 : ℝ) ≤ 2 := by norm_num
  have hi (p : ι) : IntervalIntegrable (indexedImag rho H p) volume (1 / 2) 2 := by
    simpa only [indexedImag, sub_im] using!
      (reciprocal_im_integrable (ha p) (1 / 2) 2).sub intervalIntegrable_const
  have hnorm (p : ι) :
      (∫ x in (1 / 2 : ℝ)..2, ‖indexedImag rho H p x‖) ≤ (3 / 2) * C * K p := by
    have hp (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) : ‖indexedImag rho H p x‖ ≤ C * K p := by
      rw [Real.norm_eq_abs]
      apply (abs_im_le_norm _).trans
      exact norm_reciprocal_difference_le_reference_kernel (s := (x : ℂ) + (H : ℂ) * I)
        hB (hsep p) (by simp) (by norm_num : (0 : ℝ) ≤ 3 / 2)
        (by simp; linarith [hx.1]) (by simpa using hx.2) ⟨(hr p).1.le, (hr p).2.le⟩
    have hh := intervalIntegral.integral_mono_on (μ := volume) hab (hi p).norm
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C * K p) volume (1 / 2) 2) hp
    rw [intervalIntegral.integral_const] at hh
    simpa only [smul_eq_mul, show 2 - (1 / 2 : ℝ) = 3 / 2 by norm_num, mul_assoc] using hh
  have hsum : Summable (fun p : ι => ∫ x in (1 / 2 : ℝ)..2, ‖indexedImag rho H p x‖) :=
    Summable.of_nonneg_of_le (fun _ => intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _))
      hnorm (hk.mul_left ((3 / 2) * C))
  simp only [intervalIntegral.integral_of_le hab] at hsum ⊢
  exact (integral_tsum_of_summable_integral_norm (fun p => (hi p).1) hsum).symm

theorem indexed_integral_abs_le {ι : Type*} {rho : ι → ℂ} {H : ℝ}
    (hr : ∀ p, (rho p).re ∈ Set.Ioo (0 : ℝ) 1)
    (hf : {p | |H - (rho p).im| ≤ 1}.Finite)
    (hk : Summable (fun p => (1 / (referencePoint H - rho p)).re))
    (ha : ∀ p, H - (rho p).im ≠ 0) :
    |∫ x in (1 / 2 : ℝ)..2, ∑' p, indexedImag rho H p x| ≤
      (5 * Real.pi / 2 + 4) * ∑' p, (1 / (referencePoint H - rho p)).re := by
  have hm (p : ι) : |∫ x in (1 / 2 : ℝ)..2, indexedImag rho H p x| ≤
      (5 * Real.pi / 2 + 4) * (1 / (referencePoint H - rho p)).re :=
    compensated_im_integral_le_kernel ⟨(hr p).1.le, (hr p).2.le⟩ (ha p)
  have hs : Summable (fun p : ι => |∫ x in (1 / 2 : ℝ)..2, indexedImag rho H p x|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hm (hk.mul_left _)
  rw [indexed_integral_tsum hr hf hk ha]
  have hh := norm_tsum_le_tsum_norm (f := fun p : ι => ∫ x in (1 / 2 : ℝ)..2, indexedImag rho H p x)
    (by simpa only [Real.norm_eq_abs] using hs)
  simp only [Real.norm_eq_abs] at hh
  exact hh.trans ((hs.tsum_le_tsum hm (hk.mul_left _)).trans_eq (tsum_mul_left))

end LiuWang.Proof.DirichletZeroCount.Remainder
