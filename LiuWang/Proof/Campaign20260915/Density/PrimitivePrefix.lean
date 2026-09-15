import LiuWang.Proof.ExceptionalZeroGap.PolyaVinogradov
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLWeakStripDerivative

set_option autoImplicit false
noncomputable section

open Finset Complex
open LiuWang.Proof.ExceptionalZeroGap
open DirichletLWeakStripDerivative

namespace LiuWang.Proof.Campaign20260915.Density

theorem nonprincipal_prefix_half {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, chi (n : ZMod q)‖ ≤ (q : ℝ) / 2 := by
  have hN : N = (N / q) * q + N % q := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod N q).symm
  rw [hN, sum_range_add, sum_mul_period_eq_zero chi hchi, zero_add]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
  have hshort : ‖∑ n ∈ range (N % q), chi (n : ZMod q)‖ ≤ (N % q : ℕ) := by
    apply (norm_sum_le _ _).trans
    simpa using sum_le_sum (s := range (N % q)) (fun n _ => chi.norm_le_one (n : ZMod q))
  have htail : ‖∑ n ∈ Ico (N % q) q, chi (n : ZMod q)‖ ≤ (q - N % q : ℕ) := by
    apply (norm_sum_le _ _).trans
    simpa using sum_le_sum (s := Ico (N % q) q) (fun n _ => chi.norm_le_one (n : ZMod q))
  have hle : N % q ≤ q := (Nat.mod_lt N (NeZero.pos q)).le
  have he := sum_range_add_sum_Ico (fun n : ℕ => chi (n : ZMod q)) hle
  rw [sum_one_period_eq_zero chi hchi, add_eq_zero_iff_eq_neg] at he
  rw [← norm_neg, ← he] at htail
  push_cast [hle] at htail
  linarith

theorem small_modulus_half_le_PV {q : ℕ} (hq : 3 ≤ q) (hq' : q < 12) :
    (q : ℝ) / 2 ≤ Real.sqrt q * Real.log q := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg q)
  have hs0 := Real.sqrt_nonneg q
  have hslog : Real.sqrt q ≤ 2 * Real.log q := by
    by_cases h4 : q ≤ 4
    · have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (Nat.cast_le.mpr hq)
      have hq4 : (q : ℝ) ≤ 4 := Nat.cast_le.mpr h4
      nlinarith [Real.log_three_gt_d9]
    · by_cases h9 : q ≤ 9
      · have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 5)
          (show (5 : ℝ) ≤ q by exact_mod_cast (show 5 ≤ q by omega))
        have hq9 : (q : ℝ) ≤ 9 := Nat.cast_le.mpr h9
        nlinarith [Real.log_five_gt_d9]
      · have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 9)
          (show (9 : ℝ) ≤ q by exact_mod_cast (show 9 ≤ q by omega))
        rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow] at hl
        have hq12 : (q : ℝ) ≤ 12 := Nat.cast_le.mpr hq'.le
        norm_num only [Nat.cast_ofNat] at hl
        nlinarith [Real.log_three_gt_d9]
  nlinarith [mul_le_mul_of_nonneg_left hslog hs0]

theorem primitive_prefix_log {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hchi : chi.IsPrimitive) (hq : 3 ≤ q) (N : ℕ) :
    ‖∑ n ∈ range N, chi (n : ZMod q)‖ ≤ Real.sqrt q * Real.log q := by
  by_cases h12 : 12 ≤ q
  · rw [hchi.sum_range_fourier_completion N, norm_mul, norm_mul,
      norm_inv, Complex.norm_natCast, hchi.norm_gaussSum_stdAddChar (by omega)]
    have hb := weighted_fourier_kernel_le (χ := chi) h12 (0 : ZMod q) N
    simp only [mul_zero, AddChar.map_zero_eq_one, mul_one] at hb
    have h := mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans hb)
      (show 0 ≤ (q : ℝ)⁻¹ * Real.sqrt q by positivity)
    apply h.trans_eq
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    field_simp
  · have hn : chi ≠ 1 := by
      intro he
      have hc := hchi
      change chi.conductor = q at hc
      rw [he, DirichletCharacter.conductor_one] at hc
      omega
    exact (nonprincipal_prefix_half hn N).trans (small_modulus_half_le_PV hq (by omega))

#print axioms primitive_prefix_log

end LiuWang.Proof.Campaign20260915.Density
