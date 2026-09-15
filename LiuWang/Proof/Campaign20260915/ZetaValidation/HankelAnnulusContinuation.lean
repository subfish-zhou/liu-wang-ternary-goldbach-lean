import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelAnnulusResidues

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rsLiftPoleIndices_sum (f : ℤ → ℂ) (M : ℕ) :
    ∑ n ∈ rsLiftPoleIndices M, f n =
      ∑ k ∈ Finset.range M, (f (k + 1) + f (-(k + 1))) := by
  induction M with
  | zero =>
    have he : rsLiftPoleIndices 0 = ∅ := by
      ext n
      simp only [rsLiftPoleIndices, Nat.cast_zero, neg_zero, Finset.mem_erase,
        Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and]
      omega
    simp [he]
  | succ M ih =>
    have he : rsLiftPoleIndices (M + 1) =
        insert ((M : ℤ) + 1) (insert (-((M : ℤ) + 1)) (rsLiftPoleIndices M)) := by
      ext n
      simp only [rsLiftPoleIndices, Nat.cast_add, Nat.cast_one, Finset.mem_erase,
        Finset.mem_Icc, Finset.mem_insert]
      omega
    have hneg : -((M : ℤ) + 1) ∉ rsLiftPoleIndices M := by
      simp only [rsLiftPoleIndices, Finset.mem_erase, Finset.mem_Icc, not_and]
      omega
    have hpos : (M : ℤ) + 1 ∉ insert (-((M : ℤ) + 1)) (rsLiftPoleIndices M) := by
      simp only [rsLiftPoleIndices, Finset.mem_insert, Finset.mem_erase, Finset.mem_Icc,
        not_or, not_and]
      omega
    rw [he, Finset.sum_insert hpos, Finset.sum_insert hneg, ih, Finset.sum_range_succ]
    ring

theorem rsHankelLift_annulus_jump (s : ℂ) (m : ℕ) (M : ℕ) :
    -(2 * Real.pi * I) * (∑ n ∈ rsLiftPoleIndices M, residue (rsHankelKernel s m) n) =
      (exp (Real.pi * I * s) - 1) * ∑ k ∈ Finset.range M, (k + 1 : ℂ) ^ (s - 1) := by
  rw [rsLiftPoleIndices_sum]
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_neg] using
    rsHankel_residue_jump_sum s m M

theorem rsHankelTiltedC1_annulus {m : ℕ} (hm : 0 < m) (s : ℂ)
    {M : ℕ} {u R : ℝ} (hu : u < 0) (hR : (M : ℝ) < R)
    (hR' : R < M + 1) (hM : 0 < M) :
    rsHankelTiltedC1 s m u = rsHankelTiltedC1 s m (Real.log R) +
      (exp (Real.pi * I * s) - 1) * ∑ k ∈ Finset.range M, (k + 1 : ℂ) ^ (s - 1) := by
  have hsR := rsHankel_right_sector_sin
    (θ := -(Real.pi / 4)) ⟨by linarith [Real.pi_pos], le_rfl⟩
  have hsL := rsHankel_left_sector_sin
    (θ := 5 * Real.pi / 4) ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hr := intervalIntegral.integral_Ioi_sub_Ioi'
    (rsHankelRay_integrable hm s u hsR) (rsHankelRay_integrable hm s (Real.log R) hsR)
  have hl := intervalIntegral.integral_Ioi_sub_Ioi'
    (rsHankelRay_integrable hm s u hsL) (rsHankelRay_integrable hm s (Real.log R) hsL)
  change rsHankelRay s m u _ - rsHankelRay s m (Real.log R) _ = _ at hr hl
  have h := rsHankelLift_annulus_residues s m hu hR hR' hM
  change (1 / (2 * Real.pi * I)) * RectangleIntegral (rsHankelLift s m) _ _ = _ at h
  have hc : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
  have hh := congrArg (fun z : ℂ => (2 * Real.pi * I) * z) h
  simp only [← mul_assoc, mul_one_div_cancel hc, one_mul] at hh
  simp [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul] at hh
  simp only [ofReal_neg, ofReal_div, ofReal_mul, ofReal_ofNat, neg_mul] at hr hl
  have hj := rsHankelLift_annulus_jump s m M
  unfold rsHankelTiltedC1 rsHankelArcBetween
  linear_combination -hh - hr + hl + hj

theorem zeta_eq_sum_add_expanded_hankel {m : ℕ} (hm : 0 < m)
    {s : ℂ} (ht : 0 < s.im) {M : ℕ} {R : ℝ}
    (hR : (M : ℝ) < R) (hR' : R < M + 1) (hM : 0 < M) :
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      rsHankelPrefactor s * (exp (Real.pi * I * s) - 1) *
        (∑ k ∈ Finset.range M, (k + 1 : ℂ) ^ (s - 1)) +
      rsHankelPrefactor s * rsHankelTiltedC1 s m (Real.log R) := by
  rw [zeta_eq_sum_add_tilted_hankel hm ht (by norm_num : (-1 : ℝ) < 0),
    rsHankelTiltedC1_annulus hm s (by norm_num : (-1 : ℝ) < 0) hR hR' hM]
  ring

end LiuWang.Proof.Campaign20260915.ZetaValidation
