import LiuWang.Proof.SourceRoute.Exception.Restart.FixedSource
import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalPayment

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.MultiZeroRepulsion.Continuation

namespace LiuWang.Proof.SourceRoute.Exception.Restart

theorem source_zeta_damped_bound (d : PrimitiveQuadraticDatum) {beta : ℝ}
    (hb : 1 / 2 < beta) (hzb : datumL d (beta : ℂ) = 0)
    (p : RiemannXiDivisorZeroIndex) (hr : 1 / 2 < (riemannXiDivisorZeroValue p).re)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    1 / (sigma - beta) + 1 / (sigma - (riemannXiDivisorZeroValue p).re) ≤
      1 / (sigma - 1) + 2 * stechkinConductorCoeff *
        (Real.log d.modulus + Real.log |(riemannXiDivisorZeroValue p).im|) := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  let : NeZero (d.modulus * 1) := ⟨by simpa using d.modulus_ne⟩
  let t := (riemannXiDivisorZeroValue p).im
  have hpos := heterolevel_pair_euler_nonneg d.character (1 : DirichletCharacter ℂ 1) hs 0 t
  have he (a : ℝ) := general_damped_eq_of_nat_values
    (pairCharacter d.character (1 : DirichletCharacter ℂ 1)) d.character
    (fun n => by
      rw [pairCharacter_apply]
      have h1 : (1 : DirichletCharacter ℂ 1) n = 1 := by
        rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _]
        simp
      rw [h1, mul_one]) hs a
  have hdinv : d.character⁻¹ = d.character :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using d.square_eq_one)
  have hev := damped_inverse_neg d.character hs t
  rw [hdinv] at hev
  simp only [inv_one, zero_add, zero_sub, he, hev] at hpos
  have hd := primitive_actual_selected_bound d.ne_one d.isPrimitive hb hzb hs hs1
  have ht := (xi_zero_height_gt_one p).le
  have hz := zeta_selected_high p hr hs hs1
  have hp := primitive_damped_bound d.ne_one d.isPrimitive hs hs1 t
  have h0 := zeta_real_strong hs hs1
  simp only [Complex.ofReal_im, abs_zero, max_eq_left zero_le_one, Real.log_one,
    add_zero, Complex.ofReal_re] at hd
  rw [max_eq_right ht] at hp
  have hzeta :
      dampedLogDeriv (1 : DirichletCharacter ℂ 1) sigma (stechkinSigma sigma) stechkinK t =
        zetaDamped sigma t := by
    simp only [dampedLogDeriv, DirichletCharacter.LFunction_modOne_eq, zetaDamped]
  rw [hzeta] at hpos
  have hpi := mul_le_mul_of_nonneg_left ChebyshevBound.HighHeight.log_pi_ge_one
    conductorCoeff_bounds.1
  change zetaDamped sigma t + _ ≤ _ at hz
  nlinarith [ApplicationScale.conductorCoeff_lower, stechkinK_mem.1]

theorem fixed_source_zeta_exclusion (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hzb : datumL d (beta : ℂ) = 0) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) ≤ rho.re)
    (ht : |rho.im| ≤ x) : riemannZeta rho ≠ 0 := by
  intro hz
  have hrhalf := original_re_half hx hr
  obtain ⟨p, hv⟩ := exists_xi_index_of_zeta_zero (by linarith) hz
  have hr1 := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
  have ht1 := xi_zero_height_gt_one p
  rw [hv] at hr1 ht1
  have hb1 : beta < 1 := by
    let : NeZero d.modulus := ⟨d.modulus_ne⟩
    by_contra h
    exact d.character.LFunction_ne_zero_of_one_le_re (Or.inl d.ne_one)
      (by simpa using le_of_not_gt h) hzb
  apply two_zero_budget_contradiction hx hb1 hr1 hb hr
  intro sigma hs hs1
  have hh := source_zeta_damped_bound d (original_re_half hx hb) hzb p
    (by simpa only [hv] using hrhalf) hs hs1
  rw [hv] at hh
  have hl1 := Real.log_le_log (Nat.cast_pos.mpr d.modulus_pos) hdx
  have hl2 := Real.log_le_log (by linarith : 0 < |rho.im|) ht
  have hlogs := mul_le_mul_of_nonneg_left (add_le_add hl1 hl2)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) conductorCoeff_bounds.1)
  nlinarith only [hh, hlogs]

end LiuWang.Proof.SourceRoute.Exception.Restart
