import LiuWang.Proof.Campaign20260915.OriginalRegion.LecturePolynomial
import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier.LowHeight
import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier.Offset

/-! A separate fourth-order real-axis positivity argument, not the single-zero quartic budget. -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped BigOperators Classical
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure LiuWang.Proof.ZeroRegionFamily.Uniform
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier
open LiuWang.Proof.MultiZeroRepulsion

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem fourth_root_phase_nonneg {z : ℂ} (hz : z ^ 4 = 1) :
    0 ≤ 1 + 2 * z.re + (z ^ 2).re := by
  have hf : (z - 1) * (z + 1) * (z ^ 2 + 1) = 0 := by
    calc
      _ = z ^ 4 - 1 := by ring
      _ = 0 := by rw [hz]; ring
  rcases mul_eq_zero.mp hf with hh | hh
  · rcases mul_eq_zero.mp hh with hh | hh
    · have he : z = 1 := sub_eq_zero.mp hh
      norm_num [he]
    · have he : z = -1 := eq_neg_of_add_eq_zero_left hh
      norm_num [he]
  · have he : z ^ 2 = -1 := eq_neg_of_add_eq_zero_left hh
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    norm_num [pow_two, mul_re, mul_im] at hr hi
    have hre : z.re = 0 := by
      have hp : z.re * z.im = 0 := by nlinarith only [hi]
      rcases mul_eq_zero.mp hp with hp | hp
      · exact hp
      · rw [hp] at hr
        nlinarith [sq_nonneg z.re]
    rw [he, hre]
    norm_num

theorem fourth_order_damped_nonneg {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (h4 : chi ^ 4 = 1)
    {sigma : ℝ} (hs : 1 < sigma) :
    0 ≤ dampedLogDeriv (1 : DirichletCharacter ℂ q) sigma (stechkinSigma sigma) stechkinK 0 +
      2 * dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK 0 +
      dampedLogDeriv (chi ^ 2) sigma (stechkinSigma sigma) stechkinK 0 := by
  have hp (n : ℕ) (_hn : n ≠ 0) (hu : IsUnit (n : ZMod q)) :
      0 ≤ ∑ j : Fin 3, (![1, 2, 1] : Fin 3 → ℝ) j *
        (phase ((![1, chi, chi ^ 2] : Fin 3 → DirichletCharacter ℂ q) j) 0 n).re := by
    have hz := congrArg (fun c : DirichletCharacter ℂ q => c n) h4
    rw [chi.pow_apply' (by norm_num), MulChar.one_apply hu] at hz
    simpa [Fin.sum_univ_succ, phase, MulChar.one_apply hu, add_assoc,
      chi.pow_apply' (by norm_num : (2 : ℕ) ≠ 0)] using fourth_root_phase_nonneg hz
  have hh := damped_polynomial_nonneg Finset.univ
    (![1, chi, chi ^ 2] : Fin 3 → DirichletCharacter ℂ q)
    (fun _ => 0) (![1, 2, 1] : Fin 3 → ℝ) hp hs (stechkinSigma_ge hs) stechkinK_mem
  simpa [Fin.sum_univ_succ, add_assoc] using hh

theorem fourth_order_real_axis_budget {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (h4 : chi ^ 4 = 1) (h2 : chi ^ 2 ≠ 1)
    {rho : ℂ} (hr : 1 / 2 < rho.re) (hz : chi.LFunction rho = 0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    2 * (sigma - rho.re) / ((sigma - rho.re) ^ 2 + rho.im ^ 2) ≤
      1 / (sigma - 1) + 3 * stechkinConductorCoeff * Real.log q +
        2 * rho.im ^ 2 / (sigma - 1 + rho.re) ^ 3 := by
  have hpos := fourth_order_damped_nonneg chi h4 hs
  have hmain := primitive_actual_offset_bound hc hp hr hz hs hs1 0
  have h0 := principal_real_strong (q := q) hs hs1
  have hsquare := (harmonicBound_paid (chi ^ 2) hs hs1 0).trans
    (harmonic_share (chi ^ 2) hs 0)
  simp only [harmonicPole, if_neg h2, zero_add, abs_zero, max_eq_left zero_le_one,
    Real.log_one, add_zero, zero_sub, neg_sq] at hsquare hmain
  have he := principalPrimeCost_nonneg q hs
  have hl := mul_le_mul_of_nonneg_left ChebyshevBound.HighHeight.log_pi_ge_one
    conductorCoeff_bounds.1
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    dsimp [stechkinConductorCoeff]
    linarith [stechkinK_le]
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem fourth_order_low_no_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (h4 : chi ^ 4 = 1) (h2 : chi ^ 2 ≠ 1)
    {rho : ℂ} (hr : 1 - 21 / (200 * Real.log x) < rho.re)
    (ht : Real.log x * |rho.im| ≤ 1 / 8) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hlog := log_scale_ge_34_15 hx
  have hL : 0 < Real.log x := by linarith
  have hw : 21 / (200 * Real.log x) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb : rho.re < 1 := by
    by_contra hh
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt hh) hz
  have hu : 0 < (1 / 4) / Real.log x := by positivity
  have hu1 : (1 / 4) / Real.log x ≤ 3 / 20 := by
    apply (div_le_iff₀ hL).mpr
    linarith
  have hh := fourth_order_real_axis_budget hc hp h4 h2 (by linarith) hz
    (sigma := 1 + (1 / 4) / Real.log x) (by linarith) (by linarith)
  have hinv : 1 / (1 + (1 / 4) / Real.log x - 1) = 4 * Real.log x := by
    field_simp
    ring
  rw [hinv] at hh
  have hl := mul_le_mul_of_nonneg_left
    (Real.log_le_log (by exact_mod_cast NeZero.pos q) hq) conductorCoeff_bounds.1
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_bounds.2 hL.le
  have ht1 : |rho.im| ≤ 1 / 8 := by
    nlinarith [abs_nonneg rho.im]
  have hts : rho.im ^ 2 ≤ 1 / 64 := by
    nlinarith [sq_abs rho.im, mul_nonneg (show 0 ≤ 1 / 8 - |rho.im| by linarith)
      (show 0 ≤ 1 / 8 + |rho.im| by positivity)]
  have hd : 1 / 8 ≤ (1 + (1 / 4) / Real.log x - 1 + rho.re) ^ 3 := by
    have ha : 1 / 2 ≤ 1 + (1 / 4) / Real.log x - 1 + rho.re := by linarith
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) ha 3
    norm_num at hh
    simpa using hh
  have herr : 2 * rho.im ^ 2 /
      (1 + (1 / 4) / Real.log x - 1 + rho.re) ^ 3 ≤ 1 / 4 := by
    apply (div_le_iff₀ (by linarith : 0 < (1 + (1 / 4) / Real.log x - 1 + rho.re) ^ 3)).mpr
    linarith
  have hgap : (1 - rho.re) * Real.log x < 21 / 200 := by
    have hh := (lt_div_iff₀ (show 0 < 200 * Real.log x by positivity)).mp
      (show 1 - rho.re < 21 / (200 * Real.log x) by linarith)
    nlinarith only [hh]
  exact LowOrderClosure.coupled_kernel_contradiction hL
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) < 21 / 200)
    (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (0 : ℝ) ≤ 5)
    hb hgap ht (by norm_num) (by norm_num) (by linarith)

theorem ordinary_fourth_order_low_original {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (h4 : chi ^ 4 = 1) (h2 : chi ^ 2 ≠ 1)
    {rho : ℂ} (hr : 1 - 1 / (9.645908801 * Real.log x) < rho.re)
    (ht : Real.log x * |rho.im| ≤ 1 / 8) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hc : chi ≠ 1 := by intro hh; apply h2; simp [hh]
  have hL : 0 < Real.log x := by linarith [log_scale_ge_34_15 hx]
  have hw : 1 / (9.645908801 * Real.log x) ≤ 21 / (200 * Real.log x) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  have hhalf : 21 / (200 * Real.log x) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [log_scale_ge_34_15 hx]
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hcq : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  exact fourth_order_low_no_zero hx (hcq.trans hq)
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc)
    chi.primitiveCharacter_isPrimitive
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_eq_one_of_pow_eq_one chi h4)
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_ne_one_of_pow_ne_one chi h2)
    (by linarith) ht
    (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc (by linarith) hz)

end LiuWang.Proof.Campaign20260915.OriginalRegion
