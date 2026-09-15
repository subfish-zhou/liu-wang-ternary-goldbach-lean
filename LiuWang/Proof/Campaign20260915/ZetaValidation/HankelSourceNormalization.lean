import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelBanks
import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelRectangle

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rsHankel_jump_ne_zero {s : ℂ} (hs : 0 < s.im) :
    exp (2 * Real.pi * I * s) - 1 ≠ 0 := by
  intro hz
  have hn := congrArg norm (sub_eq_zero.mp hz)
  rw [norm_exp, norm_one] at hn
  have hr : (2 * Real.pi * I * s).re < 0 := by
    simp [mul_re, mul_im]
    have := mul_pos Real.pi_pos hs
    linarith
  exact (ne_of_lt (Real.exp_lt_one_iff.mpr hr)) hn

theorem zeta_eq_sum_add_hankel_banks (m : ℕ) {s : ℂ} (hs : 1 < s.re) (ht : 0 < s.im) :
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      ((2 * Real.pi : ℂ) ^ s * exp (Real.pi * I * s / 2) /
        (Gamma s * (exp (2 * Real.pi * I * s) - 1))) *
        ((∫ y : ℝ in Ioi 0, rsHankelLeftBank s m y) -
          ∫ y : ℝ in Ioi 0, rsHankelRightBank s m y) := by
  rw [rsHankelBanks_actual_zeta m hs, cpow_neg]
  have hphase : exp (-(Real.pi / 2 : ℂ) * I * s) = (exp (Real.pi * I * s / 2))⁻¹ := by
    rw [← exp_neg]
    congr 1
    ring
  rw [hphase]
  have hpow : (2 * Real.pi : ℂ) ^ s ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl
      (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)))
  field_simp [Gamma_ne_zero_of_re_pos (by linarith : 0 < s.re), rsHankel_jump_ne_zero ht,
    exp_ne_zero, hpow]
  ring

theorem rsHankel_residue_pair (s : ℂ) (m : ℕ) {n : ℕ} (hn : 0 < n) :
    (2 * Real.pi * I) *
      (residue (rsHankelKernel s m) n + residue (rsHankelKernel s m) (-(n : ℂ))) =
      (1 - exp (Real.pi * I * s)) * (n : ℂ) ^ (s - 1) := by
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show residue (rsHankelKernel s m) (n : ℂ) =
      rsHankelNumerator s m n / (2 * Real.pi * I) by
        exact rsHankelKernel_residue s m hnZ,
    show residue (rsHankelKernel s m) (-(n : ℂ)) =
      rsHankelNumerator s m (-(n : ℂ)) / (2 * Real.pi * I) by
        simpa only [Int.cast_neg, Int.cast_natCast] using rsHankelKernel_residue s m (neg_ne_zero.mpr hnZ),
    rsHankelNumerator_pos s m hn, rsHankelNumerator_neg s m hn]
  have he : exp (Real.pi * I * (s - 1)) = -exp (Real.pi * I * s) := by
    rw [mul_sub, mul_one, exp_sub, exp_pi_mul_I]
    ring
  rw [he]
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  field_simp
  ring

theorem rsHankel_residue_jump_sum (s : ℂ) (m K : ℕ) :
    -(2 * Real.pi * I) *
      ∑ n ∈ Finset.range K,
        (residue (rsHankelKernel s m) (n + 1 : ℂ) +
          residue (rsHankelKernel s m) (-(n + 1 : ℂ))) =
      (exp (Real.pi * I * s) - 1) *
        ∑ n ∈ Finset.range K, (n + 1 : ℂ) ^ (s - 1) := by
  rw [neg_mul, Finset.mul_sum]
  have he (n : ℕ) :
      2 * Real.pi * I * (residue (rsHankelKernel s m) (n + 1 : ℂ) +
        residue (rsHankelKernel s m) (-(n + 1 : ℂ))) =
      (1 - exp (Real.pi * I * s)) * (n + 1 : ℂ) ^ (s - 1) := by
    simpa only [Nat.cast_succ] using rsHankel_residue_pair s m (Nat.succ_pos n)
  simp_rw [he]
  rw [← Finset.mul_sum]
  ring

end LiuWang.Proof.Campaign20260915.ZetaValidation
