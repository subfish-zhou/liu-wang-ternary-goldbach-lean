import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.PVMean

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier

namespace LiuWang.Proof.Campaign20260915.Density

theorem LFunction_critical_PV_sq {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {T t : ℝ} (ht : |t| ≤ T) :
    ‖chi.LFunction ((1 / 2 : ℂ) + t * I)‖ ^ 2 ≤
      256 * Real.sqrt q * (1 + Real.log q) * (1 + T) := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hlog := Real.log_nonneg hq
  have hsqrt : (1 : ℝ) ≤ Real.sqrt q := (Real.le_sqrt (by norm_num) (by positivity)).mpr
    (by simpa using hq)
  have hB : 1 ≤ prefixBudget q := by
    unfold prefixBudget
    apply le_min hq
    nlinarith
  let A : ℝ := prefixBudget q * (1 + T)
  let M : ℕ := ⌈A⌉₊
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hAM : A ≤ (M : ℝ) := Nat.le_ceil A
  have hM : 1 ≤ M := by exact_mod_cast hA.trans hAM
  have hMA : (M : ℝ) ≤ 2 * A := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ A by linarith)
    dsimp [M]
    linarith
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg M)
  have hE : pvError q M (1 / 2) T ≤ 2 * Real.sqrt M := by
    unfold pvError
    rw [Real.rpow_neg (Nat.cast_nonneg M), ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
    apply (div_le_iff₀ hs).mpr
    dsimp [A] at hAM
    nlinarith
  have hL : ‖chi.LFunction ((1 / 2 : ℂ) + t * I)‖ ≤ 4 * Real.sqrt M := by
    have hb := norm_add_le (partialL chi M ((1 / 2 : ℂ) + t * I))
      (chi.LFunction ((1 / 2 : ℂ) + t * I) - partialL chi M ((1 / 2 : ℂ) + t * I))
    rw [add_sub_cancel] at hb
    have hp := partialL_critical_norm_le chi M t
    have he := (LFunction_truncation_PV hchi hM (sigma := 1 / 2) le_rfl ht).trans hE
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at he
    linarith
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hL 2
  rw [mul_pow, hs2] at hsq
  have hP := mul_le_mul_of_nonneg_right
    (min_le_right (q : ℝ) (8 * Real.sqrt q * (1 + Real.log q)))
    (show 0 ≤ 32 * (1 + T) by positivity)
  change prefixBudget q * _ ≤ _ at hP
  dsimp [A] at hMA
  nlinarith only [hsq, hMA, hP]

theorem family_critical_le_Q_integrals (q : ℕ) [NeZero q] (X : ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -T..T,
      ‖NonprincipalDensityAdvance.f chi X ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
      512 * Real.sqrt q * (1 + Real.log q) * (1 + T) *
        (∑ chi ∈ nonprincipalCharacters q, ∫ t in -T..T,
          ‖NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * I)‖ ^ 2) +
      4 * q * T := by
  have hi (chi : Character q) (hc : chi ≠ 1) :
      (∫ t in -T..T, ‖NonprincipalDensityAdvance.f chi X ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        512 * Real.sqrt q * (1 + Real.log q) * (1 + T) *
          (∫ t in -T..T, ‖NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * I)‖ ^ 2) +
        4 * T := by
    have hQ := Q_vertical_integrable chi X (1 / 2) T
    have hf := f_vertical_integrable hc X (1 / 2) T
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hQ hf
    have hR := (hQ.const_mul (512 * Real.sqrt q * (1 + Real.log q) * (1 + T))).add
      (intervalIntegrable_const (c := (2 : ℝ)))
    have h := intervalIntegral.integral_mono_on (by linarith : -T ≤ T) hf hR
      (fun t ht => by
        have hL := mul_le_mul_of_nonneg_right (LFunction_critical_PV_sq hc (abs_le.mpr ht))
          (sq_nonneg ‖NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * I)‖)
        nlinarith only [hL, f_norm_sq_le chi X ((1 / 2 : ℂ) + t * I)])
    rw [intervalIntegral.integral_add (hQ.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at h
    simp only [smul_eq_mul] at h
    convert h using 1
    ring
  have h := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hc => hi chi ((NonprincipalDensityAdvance.mem_nonprincipalCharacters chi).mp hc))
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at h
  have hc : ((nonprincipalCharacters q).card : ℝ) ≤ q := by
    rw [NonprincipalDensityAdvance.card_nonprincipalCharacters]
    exact_mod_cast (Nat.sub_le q.totient 1).trans (Nat.totient_le q)
  have hc' := mul_le_mul_of_nonneg_right hc (show 0 ≤ 4 * T by positivity)
  linarith

#print axioms LFunction_critical_PV_sq
#print axioms family_critical_le_Q_integrals

end LiuWang.Proof.Campaign20260915.Density
