import LiuWang.Proof.SourceRoute.Exception.Restart.MixedSources
import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralLcm
import LiuWang.Proof.ZeroRegionFamily.LowOrderClosure.Nonprincipal
import LiuWang.Proof.ZeroRegionFamily.RealClosure.Principal

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.MultiZeroRepulsion.Continuation

namespace LiuWang.Proof.SourceRoute.Exception.Restart

theorem damped_inverse_neg {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    dampedLogDeriv chi⁻¹ sigma (stechkinSigma sigma) stechkinK (-t) =
      dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t := by
  have he (a : ℝ) : eulerTerm chi⁻¹ a (-t) = eulerTerm chi a t := by
    funext n
    by_cases hn : n = 0
    · simp [eulerTerm, hn]
    rw [eulerTerm_phase _ hn, eulerTerm_phase _ hn, phase_inv, Complex.conj_re]
  have hh (a : ℝ) (ha : 1 < a) :
      -(logDeriv chi⁻¹.LFunction ((a : ℂ) + I * (-t))).re =
        -(logDeriv chi.LFunction ((a : ℂ) + I * t)).re := by
    have hh := eulerTerm_hasSum chi⁻¹ ha (-t)
    rw [he] at hh
    simpa only [ofReal_neg] using hh.unique (eulerTerm_hasSum chi ha t)
  have h0 := hh sigma hs
  have h1 := hh (stechkinSigma sigma) (hs.trans_le (stechkinSigma_ge hs))
  dsimp [dampedLogDeriv]
  simp only [ofReal_neg]
  rw [h0, neg_inj.mp h1]

theorem original_gap_scaled {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    (1 - beta) * Real.log x < 21 / 200 := by
  have hL := log_scale_ge hx
  have hh := (le_div_iff₀ (show 0 < 9.645908801 * Real.log x by positivity)).mp
    (show 1 - beta ≤ 1 / (9.645908801 * Real.log x) by linarith)
  nlinarith only [hh]

theorem quadratic_low_original (d : PrimitiveQuadraticDatum)
    {x : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) ≤ rho.re)
    (hi : rho.im ≠ 0) (ht : Real.log x * |rho.im| ≤ 1 / 2) :
    datumL d rho ≠ 0 := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  intro hz
  have hL := log_scale_ge hx
  have hL0 : 0 < Real.log x := by linarith
  have hb : rho.re < 1 := by
    by_contra h
    exact d.character.LFunction_ne_zero_of_one_le_re (Or.inl d.ne_one)
      (le_of_not_gt h) hz
  have hu : 0 < 1 / Real.log x := by positivity
  have hu1 : 1 / Real.log x ≤ 1 := (div_le_one hL0).mpr (by linarith)
  have hh := quadratic_real_axis_pair d.ne_one d.isPrimitive d.square_eq_one
    (by linarith [original_re_half hx hr]) hz hi
    (sigma := 1 + 1 / Real.log x) (by linarith) (by linarith)
  have hinv : 1 / (1 + 1 / Real.log x - 1) = Real.log x := by field_simp; ring
  rw [hinv] at hh
  have hl := Real.log_le_log (Nat.cast_pos.mpr d.modulus_pos) hdx
  exact LowOrderClosure.coupled_kernel_contradiction hL0 (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 21 / 200) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 3 / 2) hb (original_gap_scaled hx hr) ht
    (by norm_num) (by norm_num) (by linarith)

theorem same_source_damped_bound (d : PrimitiveQuadraticDatum)
    {beta : ℝ} {rho : ℂ} (hb : 1 / 2 < beta) (hr : 1 / 2 < rho.re)
    (hzb : datumL d (beta : ℂ) = 0) (hz : datumL d rho = 0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    1 / (sigma - beta) + 1 / (sigma - rho.re) ≤
      1 / (sigma - 1) + poleDifference sigma rho.im +
      2 * stechkinConductorCoeff * (Real.log d.modulus + Real.log (max 1 |rho.im|)) := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  have hpos := pair_euler_nonneg d.character d.character hs 0 rho.im
  simp only [Fin.sum_univ_succ, pairCharacters, pairHeights, pairCoefficients,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
    zero_add, zero_sub, mul_inv_cancel, ← pow_two, d.square_eq_one] at hpos
  have hev := damped_inverse_neg (1 : DirichletCharacter ℂ d.modulus) hs rho.im
  rw [inv_one] at hev
  rw [hev] at hpos
  have hd := primitive_actual_selected_bound d.ne_one d.isPrimitive hb hzb hs hs1
  have he := primitive_actual_selected_bound d.ne_one d.isPrimitive hr hz hs hs1
  have h0 := principal_real_strong (q := d.modulus) hs hs1
  have h1 := principal_all_height (q := d.modulus) hs hs1 rho.im
  simp only [Complex.ofReal_im, abs_zero, max_eq_left zero_le_one, Real.log_one,
    add_zero, Complex.ofReal_re] at hd
  have hp := mul_le_mul_of_nonneg_left ChebyshevBound.HighHeight.log_pi_ge_one
    conductorCoeff_bounds.1
  have hq := mul_nonneg conductorCoeff_bounds.1 (Real.log_natCast_nonneg d.modulus)
  nlinarith [ApplicationScale.conductorCoeff_lower, stechkinK_mem.1]

theorem fixed_source_nonreal_exclusion (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hzb : datumL d (beta : ℂ) = 0) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) ≤ rho.re)
    (ht : |rho.im| ≤ x / d.modulus) (hi : rho.im ≠ 0) : datumL d rho ≠ 0 := by
  by_cases hlo : Real.log x * |rho.im| ≤ 1 / 2
  · exact quadratic_low_original d hx hdx hr hi hlo
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  intro hz
  have hL := log_scale_ge hx
  have hL0 : 0 < Real.log x := by linarith
  have hb1 : beta < 1 := by
    by_contra h
    exact d.character.LFunction_ne_zero_of_one_le_re (Or.inl d.ne_one)
      (by simpa using le_of_not_gt h) hzb
  have hr1 : rho.re < 1 := by
    by_contra h
    exact d.character.LFunction_ne_zero_of_one_le_re (Or.inl d.ne_one)
      (le_of_not_gt h) hz
  let u := (3 / 10) / Real.log x
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3 / 20 := by
    dsimp [u]
    apply (div_le_iff₀ hL0).mpr
    linarith
  have huL : u * Real.log x = 3 / 10 := by dsimp [u]; field_simp
  have hh := same_source_damped_bound d (original_re_half hx hb) (original_re_half hx hr)
    hzb hz (sigma := 1 + u) (by linarith) (by linarith)
  have hinv : 1 / (1 + u - 1) = (10 / 3) * Real.log x := by
    dsimp [u]; field_simp; ring
  rw [hinv] at hh
  have hterm (b : ℝ) (hb1 : b < 1)
      (hgap : (1 - b) * Real.log x < 21 / 200) :
      (200 / 81) * Real.log x < 1 / (1 + u - b) := by
    apply (lt_div_iff₀ (show 0 < 1 + u - b by linarith)).mpr
    nlinarith only [hgap, huL]
  have h1 := hterm beta hb1 (original_gap_scaled hx hb)
  have h2 := hterm rho.re hr1 (original_gap_scaled hx hr)
  have hpole : poleDifference (1 + u) rho.im ≤ (15 / 17) * Real.log x := by
    have hh := LowOrderClosure.scaled_pole_paid (1 : DirichletCharacter ℂ 1)
      (A := 3 / 10) (v := 1 / 2) (j := 1) hL0 (by norm_num) (by norm_num)
      (le_of_lt (lt_of_not_ge hlo))
    norm_num [Uniform.harmonicPole] at hh
    dsimp [u]
    linarith only [hh]
  have hlogs := mul_le_mul_of_nonneg_left (conductor_height_log_max_le hdx ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) conductorCoeff_bounds.1)
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_bounds.2 hL0.le
  nlinarith only [hh, h1, h2, hpole, hlogs, hk, hL0]

end LiuWang.Proof.SourceRoute.Exception.Restart
