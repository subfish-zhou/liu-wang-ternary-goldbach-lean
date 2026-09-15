import LiuWang.Proof.Campaign20260915.OriginalRegion.SourceFreeConsumers
import LiuWang.Proof.Campaign20260915.OriginalRegion.HighRegion

/-! The remaining auxiliary x>=10 domain is explicit, not silently replaced by the paper scale. -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem source_free_low_original_classification {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : 1 - 1 / (9.645908801 * Real.log x) < rho.re) (hr1 : rho.re < 1)
    (ht : Real.log x * |rho.im| ≤ 1 / 8) (hz : chi.LFunction rho = 0) :
    chi ≠ 1 ∧ chi ^ 2 = 1 ∧ rho.im = 0 ∧ analyticOrderNatAt chi.LFunction rho = 1 := by
  by_cases horder : chi ^ 3 = 1 ∨ chi ^ 4 = 1
  · exact small_order_low_classification hx hq chi horder hr hr1 ht hz
  · push Not at horder
    have h2 : chi ^ 2 ≠ 1 := by
      intro hh
      apply horder.2
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hh, one_pow]
    have ht1 : |rho.im| ≤ 1 := by
      nlinarith [log_scale_ge_34_15 hx, abs_nonneg rho.im]
    have hscale : (q : ℝ) * max 1 |rho.im| ≤ x := by
      simpa only [max_eq_left ht1, mul_one] using hq
    exact False.elim (ordinary_higher_order_original hx chi h2 horder.1 horder.2 hscale hr hz)

theorem original_nonreal_residual {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : 1 - 1 / (9.645908801 * Real.log x) < rho.re) (hr1 : rho.re < 1)
    (ht : |rho.im| ≤ x / q) (hz : chi.LFunction rho = 0) (hi : rho.im ≠ 0) :
    x < 8000000000 ∧ chi ≠ 1 ∧ (chi ^ 3 = 1 ∨ chi ^ 4 = 1) ∧
      1 / 8 < Real.log x * |rho.im| ∧ |rho.im| < 1 / 2 := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hscale : (q : ℝ) * max 1 |rho.im| ≤ x := by
    by_cases hh : |rho.im| ≤ 1
    · simpa only [max_eq_left hh, mul_one] using hq
    · rw [max_eq_right (le_of_not_ge hh)]
      simpa only [mul_comm] using (le_div_iff₀ hq0).mp ht
  have hsmall : x < 8000000000 := by
    by_contra hh
    exact hi (source_free_original_classification (le_of_not_gt hh) hq chi hr hr1 ht hz).2.2.1
  have hc : chi ≠ 1 := by
    intro he
    subst chi
    exact principal_original_no_zero hx hr ht (by intro hh; simp [hh] at hr1) hz
  have horder : chi ^ 3 = 1 ∨ chi ^ 4 = 1 := by
    by_contra hh
    push Not at hh
    have h2 : chi ^ 2 ≠ 1 := by
      intro he
      apply hh.2
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, he, one_pow]
    exact ordinary_higher_order_original hx chi h2 hh.1 hh.2 hscale hr hz
  have hlow : 1 / 8 < Real.log x * |rho.im| := by
    by_contra hh
    exact hi (source_free_low_original_classification hx hq chi hr hr1 (le_of_not_gt hh) hz).2.2.1
  have hhigh : |rho.im| < 1 / 2 := by
    by_contra hh
    exact ordinary_high_original hx chi hc hscale hr (le_of_not_gt hh) hz
  exact ⟨hsmall, hc, horder, hlow, hhigh⟩

theorem quarter_height_pole_obstruction : 0 < poleDifference (23 / 20) (1 / 4) := by
  have hb := stechkinSigma_bounds (by norm_num : (1 : ℝ) < 23 / 20) le_rfl
  have hv : 0 < stechkinSigma (23 / 20) - 1 := by linarith [hb.1]
  have hk := mul_le_mul_of_nonneg_left
    (positive_kernel_le_inverse (v := 1 / 4) hv) stechkinK_mem.1
  have hi : 1 / (stechkinSigma (23 / 20) - 1) ≤ 5 / 3 := by
    apply (div_le_iff₀ hv).mpr
    linarith [hb.1]
  have hu := mul_le_mul stechkinK_le hi (by positivity) (by norm_num : (0 : ℝ) ≤ 9 / 20)
  have he : poleDifference (23 / 20) (1 / 4) =
      (30 / 17 : ℝ) - stechkinK *
        ((stechkinSigma (23 / 20) - 1) /
          ((stechkinSigma (23 / 20) - 1) ^ 2 + (1 / 4 : ℝ) ^ 2)) := by
    simp only [poleDifference, one_div, Complex.inv_re, Complex.normSq_apply,
      Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.sub_im,
      Complex.one_im, Complex.mul_im]
    ring
  rw [he]
  simp only [div_eq_mul_inv] at *
  nlinarith

-- This is an unpaid residual goal, not a theorem or an assumed input to a proof.
#check (∀ (x : ℝ) (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (rho : ℂ),
  10 ≤ x → x < 8000000000 → (q : ℝ) ≤ x → chi ≠ 1 →
  (chi ^ 3 = 1 ∨ chi ^ 4 = 1) →
  1 - 1 / (9.645908801 * Real.log x) < rho.re → rho.re < 1 →
  1 / 8 < Real.log x * |rho.im| → |rho.im| < 1 / 2 →
  chi.LFunction rho ≠ 0 : Prop)

-- A sufficient scalar extension of the paid sigma<=1.02 pole lemma; still unproved.
#check (∀ (sigma beta v : ℝ), 1 < sigma → sigma ≤ 23 / 20 →
  9 / 10 ≤ beta → beta < 1 → 1 - beta ≤ sigma - 1 →
  poleDifference sigma v ≤ 2 * reflectedKernel sigma v (beta : ℂ) : Prop)

end LiuWang.Proof.Campaign20260915.OriginalRegion
