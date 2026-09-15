import LiuWang.Proof.Campaign20260915.ZetaWinding.LittlewoodIdentity
import Mathlib.Analysis.SpecialFunctions.Log.Summable

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open Complex.Hadamard
open BombieriVinogradov.SiegelWalfisz

def xiGenusLog (s : ℂ) (p : RiemannXiDivisorZeroIndex) : ℝ :=
  Real.log ‖weierstrassFactor 1 (s / riemannXiDivisorZeroValue p)‖

theorem abs_log_norm_weierstrass_one {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    |Real.log ‖weierstrassFactor 1 z‖| ≤ 2 * ‖z‖ ^ 2 := by
  have h1 : ‖z‖ < 1 := by linarith
  have hn : z ≠ 1 := by intro he; norm_num [he] at hz
  rw [weierstrassFactor_eq_exp_neg_tail 1 h1 hn, norm_exp, Real.log_exp, neg_re, abs_neg]
  exact (abs_re_le_norm _).trans (norm_logTail_le_two_mul_norm_pow h1 hz 1)

theorem xiGenusLog_far_bound {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : ‖s‖ ≤ R)
    (p : RiemannXiDivisorZeroIndex) (hp : 2 * R < ‖riemannXiDivisorZeroValue p‖) :
    |xiGenusLog s p| ≤ (2 * R ^ 2) * ‖riemannXiDivisorZeroValue p‖⁻¹ ^ 2 := by
  have h := abs_log_norm_weierstrass_one
    (norm_div_le_half_of_norm_le_of_two_mul_lt hR hs hp)
  unfold xiGenusLog
  refine h.trans ?_
  rw [norm_div, div_eq_mul_inv, mul_pow]
  rw [← mul_assoc]
  gcongr

theorem xiGenusLog_summable (s : ℂ) : Summable (xiGenusLog s) := by
  let R := max ‖s‖ 1
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hs : ‖s‖ ≤ R := le_max_left _ _
  have hF := divisorZeroIndex₀_norm_le_finite (f := riemannXi) (U := Set.univ) (2 * R)
    (Set.subset_univ _)
  apply (summable_riemannXiDivisorZero_norm_inv_sq.mul_left (2 * R ^ 2)).of_norm_bounded_eventually
  filter_upwards [hF.eventually_cofinite_notMem] with p hp
  exact xiGenusLog_far_bound hR hs p (lt_of_not_ge hp)

theorem xiGenusLog_horizontal_integrable (p : RiemannXiDivisorZeroIndex) (T a b : ℝ) :
    IntervalIntegrable (fun x => xiGenusLog (horizontalAt T x) p) volume a b := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro x _
  have hA : AnalyticAt ℝ (fun x => horizontalAt T x / riemannXiDivisorZeroValue p) x :=
    ((Complex.ofRealCLM.analyticAt x).add analyticAt_const).div_const
  exact (((differentiable_weierstrassFactor 1).analyticAt _).restrictScalars (𝕜 := ℝ) |>.comp hA).meromorphicAt

theorem xiGenusLog_integral_norm_summable (T a b : ℝ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      ∫ x in a..b, |xiGenusLog (horizontalAt T x) p|) := by
  have hc : Continuous (horizontalAt T) := by unfold horizontalAt; fun_prop
  obtain ⟨M, hM⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn hc.continuousOn
  let R := max M 1
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hs : ∀ x ∈ Set.uIcc a b, ‖horizontalAt T x‖ ≤ R :=
    fun x hx => (hM x hx).trans (le_max_left _ _)
  have hF := divisorZeroIndex₀_norm_le_finite (f := riemannXi) (U := Set.univ) (2 * R)
    (Set.subset_univ _)
  apply (summable_riemannXiDivisorZero_norm_inv_sq.mul_left (2 * R ^ 2) |>.mul_right
    |b - a|).of_norm_bounded_eventually
  filter_upwards [hF.eventually_cofinite_notMem] with p hp
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  simpa only [Real.norm_eq_abs, abs_abs] using
    xiGenusLog_far_bound hR (hs x (Set.uIoc_subset_uIcc hx)) p (lt_of_not_ge hp)

theorem xiGenusLog_integral_tsum {a b : ℝ} (hab : a ≤ b) (T : ℝ) :
    (∫ x in a..b, ∑' p : RiemannXiDivisorZeroIndex, xiGenusLog (horizontalAt T x) p) =
      ∑' p : RiemannXiDivisorZeroIndex, ∫ x in a..b, xiGenusLog (horizontalAt T x) p := by
  have hc : (Set.univ : Set RiemannXiDivisorZeroIndex).Countable := by
    convert summable_riemannXiDivisorZero_norm_inv_sq.countable_support using 1
    ext p
    simp [Function.mem_support]
  have : Countable RiemannXiDivisorZeroIndex := Set.countable_univ_iff.mp hc
  have hs := xiGenusLog_integral_norm_summable T a b
  simp only [intervalIntegral.integral_of_le hab] at hs ⊢
  simpa only [Real.norm_eq_abs] using (integral_tsum_of_summable_integral_norm
    (fun p => (xiGenusLog_horizontal_integrable p T a b).1) hs).symm

theorem xi_log_norm_eq_genus_sum {s : ℂ} (hs : riemannXi s ≠ 0) :
    Real.log ‖riemannXi s‖ =
      Real.log ‖riemannXi 0‖ + ((logDeriv riemannXi 0) * s).re +
        ∑' p : RiemannXiDivisorZeroIndex, xiGenusLog s p := by
  have ha : ∀ p : RiemannXiDivisorZeroIndex, s ≠ riemannXiDivisorZeroValue p := by
    intro p he
    exact hs (he ▸ riemannXiDivisorZeroValue_eq_zero p)
  have hp := (hasProdUniformlyOn_divisorCanonicalProduct_univ 1 riemannXi
    (isCompact_singleton (x := s)) summable_riemannXiDivisorZero_norm_inv_sq).hasProd
      (Set.mem_singleton s)
  have hnon : ∀ p : RiemannXiDivisorZeroIndex,
      0 < ‖weierstrassFactor 1 (s / riemannXiDivisorZeroValue p)‖ := by
    intro p
    exact norm_pos_iff.mpr ((weierstrassFactor_div_ne_zero_iff 1
      (riemannXiDivisorZeroValue_ne_zero p)).mpr (ha p))
  have hexp := Real.hasProd_of_hasSum_log hnon (xiGenusLog_summable s).hasSum
  have he : Real.exp (∑' p, xiGenusLog s p) =
      ‖divisorCanonicalProduct 1 riemannXi Set.univ s‖ :=
    hexp.unique hp.norm
  have hlog : Real.log ‖divisorCanonicalProduct 1 riemannXi Set.univ s‖ =
      ∑' p, xiGenusLog s p := by rw [← he, Real.log_exp]
  obtain ⟨P, hdeg, hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  have hpoly := Polynomial.eq_X_add_C_of_degree_le_one hdeg
  have hB := Robin1984.riemannXi_hadamardPolynomialDerivative_eval_eq_logDeriv_zero hdeg hfac 0
  rw [hpoly] at hB
  simp at hB
  have hzero : Real.log ‖riemannXi 0‖ = (P.coeff 0).re := by
    rw [hfac 0]
    simp [divisorCanonicalProduct, norm_exp, Real.log_exp, ← Polynomial.coeff_zero_eq_eval_zero]
  rw [hfac s, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (exp_ne_zero _))
    (by rw [← he]; exact (Real.exp_pos _).ne'), norm_exp, Real.log_exp, hlog, hzero]
  conv_lhs => rw [hpoly]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, add_re]
  rw [hB]
  ring

theorem xi_horizontal_log_integrable (T a b : ℝ) :
    IntervalIntegrable (fun x => Real.log ‖riemannXi (horizontalAt T x)‖) volume a b := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro x _
  exact (((differentiable_riemannXi.analyticAt _).restrictScalars (𝕜 := ℝ)).comp
    ((Complex.ofRealCLM.analyticAt x).add analyticAt_const)).meromorphicAt

open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Argument
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem xi_horizontal_ne_zero_ae (T : ℝ) :
    ∀ᵐ x : ℝ, riemannXi (horizontalAt T x) ≠ 0 := by
  classical
  filter_upwards [((zetaClosedValues |T|).image Complex.re).finite_toSet.countable.ae_notMem volume]
    with x hx
  intro hz
  have hstrip := xi_zero_strip hz
  have hs1 : horizontalAt T x ≠ 1 := by
    intro he
    simpa [he] using hstrip.2
  have hzeta := (xi_zero_iff_zeta_zero (by linarith [hstrip.1]) hs1).mp hz
  apply hx
  exact Finset.mem_image.mpr ⟨horizontalAt T x,
    mem_zetaClosedValues.mpr ⟨hzeta, hstrip.1, hstrip.2, by simp [horizontalAt]⟩,
    by simp [horizontalAt]⟩

theorem xi_horizontal_log_integral_eq {a b : ℝ} (hab : a ≤ b) (T : ℝ) :
    (∫ x in a..b, Real.log ‖riemannXi (horizontalAt T x)‖) =
      (b - a) * Real.log ‖riemannXi 0‖ +
        (b ^ 2 - a ^ 2) / 2 * (logDeriv riemannXi 0).re -
        (b - a) * T * (logDeriv riemannXi 0).im +
        ∑' p : RiemannXiDivisorZeroIndex, ∫ x in a..b, xiGenusLog (horizontalAt T x) p := by
  let f : ℝ → ℝ := fun x => Real.log ‖riemannXi 0‖ +
    ((logDeriv riemannXi 0) * horizontalAt T x).re
  have hf : Continuous f := by unfold f horizontalAt; fun_prop
  have he :
      (∫ x in a..b, ∑' p : RiemannXiDivisorZeroIndex, xiGenusLog (horizontalAt T x) p) =
        (∫ x in a..b, Real.log ‖riemannXi (horizontalAt T x)‖) - ∫ x in a..b, f x := by
    rw [← intervalIntegral.integral_sub (xi_horizontal_log_integrable T a b)
      (hf.intervalIntegrable a b)]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [xi_horizontal_ne_zero_ae T] with x hx _
    have h := xi_log_norm_eq_genus_sum hx
    dsimp [f]
    linarith
  rw [xiGenusLog_integral_tsum hab T] at he
  have hfint : (∫ x in a..b, f x) =
      (b - a) * Real.log ‖riemannXi 0‖ +
        (b ^ 2 - a ^ 2) / 2 * (logDeriv riemannXi 0).re -
        (b - a) * T * (logDeriv riemannXi 0).im := by
    have hfpoint : f = fun x => Real.log ‖riemannXi 0‖ +
        (logDeriv riemannXi 0).re * x - (logDeriv riemannXi 0).im * T := by
      funext x
      simp [f, horizontalAt, mul_re]
      ring
    have hi : IntervalIntegrable (fun x : ℝ => (logDeriv riemannXi 0).re * x) volume a b :=
      (continuous_const.mul continuous_id).intervalIntegrable a b
    have hlin : (∫ x in a..b, (logDeriv riemannXi 0).re * x) =
        (logDeriv riemannXi 0).re * ((b ^ 2 - a ^ 2) / 2) := by
      simpa only [integral_id] using!
        (intervalIntegral.integral_const_mul (a := a) (b := b) (μ := volume)
          (logDeriv riemannXi 0).re (fun x : ℝ => x))
    rw [hfpoint, intervalIntegral.integral_sub
      (intervalIntegrable_const.add hi) intervalIntegrable_const,
      intervalIntegral.integral_add intervalIntegrable_const hi]
    rw [hlin]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hfint] at he
  linarith

theorem xiGenusLog_integral_summable {a b : ℝ} (hab : a ≤ b) (T : ℝ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      ∫ x in a..b, xiGenusLog (horizontalAt T x) p) := by
  apply (xiGenusLog_integral_norm_summable T a b).of_norm_bounded
  intro p
  simpa only [intervalIntegral.integral_of_le hab, Real.norm_eq_abs] using
    norm_integral_le_integral_norm (fun x => xiGenusLog (horizontalAt T x) p)

theorem xi_horizontal_unit_shift_integral {a b : ℝ} (hab : a ≤ b) (T : ℝ) :
    (∫ x in a..b, Real.log ‖riemannXi (horizontalAt T x)‖) -
      (∫ x in (a + 1)..(b + 1), Real.log ‖riemannXi (horizontalAt T x)‖) =
      -(b - a) * (logDeriv riemannXi 0).re +
        ∑' p : RiemannXiDivisorZeroIndex,
          ((∫ x in a..b, xiGenusLog (horizontalAt T x) p) -
            ∫ x in (a + 1)..(b + 1), xiGenusLog (horizontalAt T x) p) := by
  have hab' : a + 1 ≤ b + 1 := by linarith
  rw [(xiGenusLog_integral_summable hab T).tsum_sub (xiGenusLog_integral_summable hab' T),
    xi_horizontal_log_integral_eq hab T, xi_horizontal_log_integral_eq hab' T]
  ring

#print axioms xiGenusLog_summable
#print axioms xiGenusLog_integral_norm_summable
#print axioms xiGenusLog_integral_tsum
#print axioms xi_log_norm_eq_genus_sum
#print axioms xi_horizontal_log_integral_eq
#print axioms xi_horizontal_unit_shift_integral

end LiuWang.Proof.Campaign20260915.ZetaWinding
