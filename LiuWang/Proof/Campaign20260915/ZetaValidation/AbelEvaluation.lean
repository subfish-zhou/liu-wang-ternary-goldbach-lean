import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def centeredAbelKernel (s : ℂ) (u : ℝ) : ℂ :=
  ((Int.fract u - 1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)

def abelApprox (s : ℂ) (N : ℕ) : ℂ :=
  zetaPartialSum s N + (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2

theorem centeredAbelKernel_eq (s : ℂ) (u : ℝ) :
    centeredAbelKernel s u =
      zetaAbelFractKernel s u - (1 / 2 : ℂ) * (u : ℂ) ^ (-s - 1) := by
  unfold centeredAbelKernel zetaAbelFractKernel
  push_cast
  ring

theorem norm_centeredAbelKernel_le {u : ℝ} (hu : 0 < u) (s : ℂ) :
    ‖centeredAbelKernel s u‖ ≤ (1 / 2 : ℝ) * u ^ (-s.re - 1) := by
  have hf : |Int.fract u - 1 / 2| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [Int.fract_nonneg u, Int.fract_lt_one u]
  rw [centeredAbelKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hu]
  simpa only [Complex.sub_re, Complex.neg_re, Complex.one_re] using
    mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg hu.le (-s.re - 1))

theorem centeredAbelKernel_integrable {s : ℂ} (hs : 0 < s.re) {a : ℝ}
    (ha : 1 ≤ a) : IntegrableOn (centeredAbelKernel s) (Ioi a) := by
  have hK : IntegrableOn (zetaAbelFractKernel s) (Ioi a) :=
    IntegrableOn.mono_set (ZetaAbelFractKernel.integrableOn_Ioi s hs)
      (Ioi_subset_Ioi ha)
  have hP : IntegrableOn (fun u : ℝ => (1 / 2 : ℂ) * (u : ℂ) ^ (-s - 1))
      (Ioi a) :=
    (integrableOn_Ioi_cpow_of_lt (by simp only [sub_re, neg_re, one_re]; linarith)
      (lt_of_lt_of_le zero_lt_one ha)).const_mul _
  exact (hK.sub hP).congr_fun (fun u _ => (centeredAbelKernel_eq s u).symm)
    measurableSet_Ioi

theorem norm_centeredAbelTail_le {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    ‖∫ u in Ioi a, centeredAbelKernel s u‖ ≤ a ^ (-s.re) / (2 * s.re) := by
  calc
    _ ≤ ∫ u in Ioi a, (1 / 2 : ℝ) * u ^ (-s.re - 1) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) ha).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact norm_centeredAbelKernel_le (ha.trans hu) s
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ha]
      simp only [sub_add_cancel, neg_div_neg_eq]
      ring

theorem zeta_sub_abelApprox {s : ℂ} (hs : 1 / 10 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s - abelApprox s N =
      -s * ∫ u in Ioi (N : ℝ), centeredAbelKernel s u := by
  have hs0 : 0 < s.re := by linarith
  have hsn : s ≠ 0 := by intro h; simp [h] at hs0
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNR
  have hK : IntegrableOn (zetaAbelFractKernel s) (Ioi (N : ℝ)) :=
    IntegrableOn.mono_set (ZetaAbelFractKernel.integrableOn_Ioi s hs0)
      (Ioi_subset_Ioi hNR)
  have hP := integrableOn_Ioi_cpow_of_lt (a := -s - 1)
    (by simp only [sub_re, neg_re, one_re]; linarith) hNp
  have hc :
      (∫ u in Ioi (N : ℝ), centeredAbelKernel s u) =
        (∫ u in Ioi (N : ℝ), zetaAbelFractKernel s u) -
          (1 / 2 : ℂ) * ((N : ℂ) ^ (-s) / s) := by
    simp_rw [centeredAbelKernel_eq]
    rw [integral_sub hK (hP.const_mul _), integral_const_mul,
      integral_Ioi_cpow_of_lt (by simp only [sub_re, neg_re, one_re]; linarith) hNp]
    simp
  have hi := intervalIntegral.integral_Ioi_sub_Ioi
    (ZetaAbelFractKernel.integrableOn_Ioi s hs0) hNR
  have hp := ZetaPartialSum.abel_formula s hs1 N hN
  rw [riemannZeta_eq_zetaAbelContinuationFormula s
    ⟨hs1, by exact hs⟩, zetaAbelContinuationFormula, abelApprox, hp, ← hi, hc]
  field_simp [hsn, sub_ne_zero.mpr hs1, sub_ne_zero.mpr hs1.symm]
  ring

theorem norm_zeta_sub_abelApprox_le {s : ℂ} (hs : 1 / 10 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - abelApprox s N‖ ≤
      ‖s‖ * (N : ℝ) ^ (-s.re) / (2 * s.re) := by
  rw [zeta_sub_abelApprox hs hs1 hN, norm_mul, norm_neg]
  have hb := norm_centeredAbelTail_le (s := s) (by linarith : 0 < s.re)
    (a := N) (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN))
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hb (norm_nonneg s)

#print axioms zeta_sub_abelApprox
#print axioms norm_zeta_sub_abelApprox_le

end LiuWang.Proof.Campaign20260915.ZetaValidation
