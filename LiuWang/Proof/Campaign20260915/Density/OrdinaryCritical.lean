import LiuWang.Proof.Campaign20260915.Density.OrdinaryPrefix
import LiuWang.Proof.Campaign20260915.Density.CompleteChen24Consumer

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

theorem ordinary_critical_L_sq {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {T t : ℝ} (ht : |t| ≤ T) :
    ‖chi.LFunction ((1 / 2 : ℂ) + t * I)‖ ^ 2 ≤
      16 * ((q : ℝ) * Real.sqrt q * Real.log q / q.totient) * (2 + T) := by
  let B : ℝ := (q : ℝ) * Real.sqrt q * Real.log q / q.totient
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hq : 3 ≤ q := (nonprincipal_conductor_ge_three hchi).trans
    (Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (by omega)
  have hq0 : (0 : ℝ) < q := by positivity
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hlog : 1 ≤ Real.log q := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (Nat.cast_le.mpr hq)
    linarith [Real.log_three_gt_d9]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt q :=
    (Real.le_sqrt (by norm_num) hq0.le).mpr (by simpa using hq1)
  have hB : 1 ≤ B := by
    apply (le_div_iff₀ hphi).mpr
    have hphi' : (q.totient : ℝ) ≤ q := Nat.cast_le.mpr (Nat.totient_le q)
    have hm : 1 ≤ Real.sqrt q * Real.log q := one_le_mul_of_one_le_of_one_le hsqrt hlog
    have h := mul_le_mul_of_nonneg_left hm hq0.le
    nlinarith only [h, hphi']
  let A : ℝ := B * (1 + T)
  let M : ℕ := ⌈A⌉₊
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hAM : A ≤ (M : ℝ) := Nat.le_ceil A
  have hM : 1 ≤ M := by exact_mod_cast hA.trans hAM
  have hMA : (M : ℝ) ≤ A + 1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ A)).le
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg M)
  have htL := DirichletCharacter.norm_LFunction_sub_sum_le_of_prefix_bound chi hchi
    ((1 / 2 : ℂ) + t * I) (by norm_num) B (nonprincipal_prefix_paid q chi hchi) hM
  rw [← partialL_eq_Abel_sum hchi] at htL
  have hre : ((1 / 2 : ℂ) + t * I).re = (1 / 2 : ℝ) := by simp
  rw [hre, Real.rpow_neg (Nat.cast_nonneg M), ← Real.sqrt_eq_rpow, ← div_eq_mul_inv] at htL
  have hnorm : ‖(1 / 2 : ℂ) + t * I‖ ≤ (1 / 2 : ℝ) + T := by
    have h := norm_add_le (1 / 2 : ℂ) ((t : ℂ) * I)
    norm_num only [norm_div, norm_one, Complex.norm_ofNat, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one] at h
    linarith
  have he : B * ((Real.sqrt M)⁻¹ +
      ‖(1 / 2 : ℂ) + t * I‖ / (1 / 2) / Real.sqrt M) ≤ 2 * Real.sqrt M := by
    apply (le_of_mul_le_mul_right ?_ hs)
    have h := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * B by linarith)
    dsimp [A] at hAM
    generalize ‖(1 / 2 : ℂ) + t * I‖ = Z at h ⊢
    field_simp
    nlinarith only [h, hAM, hs2]
  have hL : ‖chi.LFunction ((1 / 2 : ℂ) + t * I)‖ ≤ 4 * Real.sqrt M := by
    have hb := norm_add_le (partialL chi M ((1 / 2 : ℂ) + t * I))
      (chi.LFunction ((1 / 2 : ℂ) + t * I) - partialL chi M ((1 / 2 : ℂ) + t * I))
    rw [add_sub_cancel] at hb
    have hp := partialL_critical_norm_le chi M t
    have htail := htL.trans he
    linarith
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hL 2
  rw [mul_pow, hs2] at hsq
  change _ ≤ 16 * B * (2 + T)
  dsimp [A] at hMA
  nlinarith only [hsq, hMA, hB]

theorem detector_small_young {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ) (s : ℂ) :
    ‖NonprincipalDensityAdvance.f chi X s‖ ^ 2 ≤
      1.001 * ‖chi.LFunction s‖ ^ 2 * ‖NonprincipalDensityAdvance.Q chi X s‖ ^ 2 + 1001 := by
  have h := norm_sub_le (chi.LFunction s * NonprincipalDensityAdvance.Q chi X s) (1 : ℂ)
  rw [norm_mul, norm_one] at h
  change ‖NonprincipalDensityAdvance.f chi X s‖ ≤ _ at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith only [hsq, sq_nonneg
    (‖chi.LFunction s‖ * ‖NonprincipalDensityAdvance.Q chi X s‖ - 1000)]

theorem family_critical_sharp_Q (q : ℕ) [NeZero q] (X : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -T..T,
      ‖NonprincipalDensityAdvance.f chi X ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
      16.016 * ((q : ℝ) * Real.sqrt q * Real.log q / q.totient) * (2 + T) *
        (∑ chi ∈ nonprincipalCharacters q, ∫ t in -T..T,
          ‖NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * I)‖ ^ 2) +
      2002 * q * T := by
  let C : ℝ := 16.016 * ((q : ℝ) * Real.sqrt q * Real.log q / q.totient) * (2 + T)
  have hi (chi : Character q) (hc : chi ≠ 1) :
      (∫ t in -T..T, ‖NonprincipalDensityAdvance.f chi X ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
        C * (∫ t in -T..T, ‖NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * I)‖ ^ 2) +
        2002 * T := by
    have hQ := Q_vertical_integrable chi X (1 / 2) T
    have hf := f_vertical_integrable hc X (1 / 2) T
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hQ hf
    have hR := (hQ.const_mul C).add (intervalIntegrable_const (c := (1001 : ℝ)))
    have h := intervalIntegral.integral_mono_on (by linarith : -T ≤ T) hf hR
      (fun t ht => by
        have hL := mul_le_mul_of_nonneg_right (ordinary_critical_L_sq hc (abs_le.mpr ht))
          (sq_nonneg ‖NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * I)‖)
        dsimp [C]
        nlinarith only [hL, detector_small_young chi X ((1 / 2 : ℂ) + t * I)])
    rw [intervalIntegral.integral_add (hQ.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at h
    simp only [smul_eq_mul] at h
    convert h using 1
    ring
  have h := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hc => hi chi ((mem_nonprincipalCharacters chi).mp hc))
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at h
  have hc : ((nonprincipalCharacters q).card : ℝ) ≤ q := by
    rw [card_nonprincipalCharacters]
    exact_mod_cast (Nat.sub_le q.totient 1).trans (Nat.totient_le q)
  have hc' := mul_le_mul_of_nonneg_right hc (show 0 ≤ 2002 * T by positivity)
  dsimp [C] at h
  linarith

#print axioms ordinary_critical_L_sq
#print axioms family_critical_sharp_Q

end LiuWang.Proof.Campaign20260915.Density
