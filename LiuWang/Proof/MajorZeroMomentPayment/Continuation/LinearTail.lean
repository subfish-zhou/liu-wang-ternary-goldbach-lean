import LiuWang.Proof.MajorZeroMomentPayment.Continuation.LinearMoment

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularIntegral LiuWang.Proof.MajorArcApproximation

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation

def explicitVariation (N : ℕ) (rho : ℂ) : ℝ :=
  (baseWeight N rho.re + realEndpoint N rho.re +
    ‖rho - 1‖ * (realEndpoint N rho.re - baseWeight N rho.re) / (1 - rho.re)) /
      (2 * Real.pi)

theorem weightVariation_explicit {N : ℕ} (hN : 0 < N) {rho : ℂ} (hr : rho.re < 1) :
    weightVariation N rho = explicitVariation N rho := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have ha := window_lower_pos hN
  have he : sourceWindowLower N = 0.001 * (N : ℝ) := by
    unfold sourceWindowLower
    ring
  have hp (t : ℝ) (ht : 0 < t) (z : ℂ) :
      ‖(t : ℂ)^z‖ = t^z.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos ht z
  have hd :
      (∫ t in sourceWindowLower N..(N : ℝ), ‖(rho - 1) * (t : ℂ)^(rho - 1 - 1)‖) =
      ‖rho - 1‖ * ((N : ℝ)^(rho.re - 1) -
        (sourceWindowLower N)^(rho.re - 1)) / (rho.re - 1) := by
    have hi :
        (∫ t in sourceWindowLower N..(N : ℝ), ‖(rho - 1) * (t : ℂ)^(rho - 1 - 1)‖) =
        ‖rho - 1‖ * ∫ t in sourceWindowLower N..(N : ℝ), t^(rho.re - 1 - 1) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (window_lower_le N)] at ht
      dsimp only
      rw [norm_mul, hp t (ha.trans_le ht.1)]
      simp only [Complex.sub_re, Complex.one_re]
    rw [hi, integral_rpow (Or.inr ⟨by linarith, by
      rw [uIcc_of_le (window_lower_le N)]
      intro h
      have := h.1
      linarith⟩)]
    rw [sub_add_cancel]
    ring
  unfold weightVariation explicitVariation
  have hn' : ‖(N : ℂ)^(rho - 1)‖ = (N : ℝ)^(rho.re - 1) := by
    simpa only [Complex.ofReal_natCast, Complex.sub_re, Complex.one_re] using hp N hn (rho - 1)
  rw [hn', hp _ ha, hd]
  simp only [Complex.sub_re, Complex.one_re, he, baseWeight, realEndpoint]
  congr 1
  rw [show rho.re - 1 = -(1 - rho.re) by ring, div_neg]
  ring

theorem weightVariation_one {N : ℕ} (_hN : 0 < N) :
    weightVariation N 1 = 1 / Real.pi := by
  norm_num [weightVariation]
  ring

def linearValue (N : ℕ) (rho : ℂ) : ℂ :=
  (N : ℂ)^2 * (N : ℂ)^(rho - 1) * linearShape rho

def linearTail (N : ℕ) (delta : ℝ) (rho : ℂ) : ℝ :=
  explicitVariation N rho / (Real.pi^2 * delta^2)

theorem finite_linear_error {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hr : 0 < rho.re) (hr' : rho.re < 1) {delta : ℝ} (hd : 0 < delta) :
    ‖finiteMoment N delta 1 1 rho - linearValue N rho‖ ≤ linearTail N delta rho := by
  rw [finiteMoment_linear_permute, linearValue, ← fullMoment_linear hN hr, norm_sub_rev]
  apply (moment_tail_variation hN rho 1 1 hd).trans_eq
  rw [weightVariation_one hN, weightVariation_explicit hN hr']
  unfold linearTail
  ring

theorem finite_linear_signed_lower {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hr : 0 < rho.re) (hr' : rho.re < 1) {delta : ℝ} (hd : 0 < delta) (c : ℂ) :
    (c * linearValue N rho).re - ‖c‖ * linearTail N delta rho ≤
      (c * finiteMoment N delta 1 1 rho).re := by
  have hb := mul_le_mul_of_nonneg_left (finite_linear_error hN hr hr' hd) (norm_nonneg c)
  have he := Complex.re_le_norm (c * (linearValue N rho - finiteMoment N delta 1 1 rho))
  rw [norm_mul, norm_sub_rev] at he
  rw [mul_sub, Complex.sub_re] at he
  linarith

theorem actual_linear_tail {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (hq : 0 < q) {rho : ℂ} (hr : 0 < rho.re) (hr' : rho.re < 1) :
    ‖finiteMoment N (deltaRadius N q) 1 1 rho - linearValue N rho‖ ≤
      100 / 3.36^2 * ((q : ℝ) / sourceP N)^2 * (N : ℝ)^2 *
        explicitVariation N rho := by
  apply (finite_linear_error (nat_pos_of_exp_le hN) hr hr' (deltaRadius_pos hN hq)).trans_eq
  unfold linearTail deltaRadius
  field_simp
  ring

theorem linearShapeBound_high {rho : ℂ}
    (hr : 1/2 ≤ rho.re) (hg : 0 < |rho.im|) :
    linearShapeBound rho ≤ 1 / |rho.im|^2 + 0.033 / |rho.im| := by
  have ha : (0.001 : ℝ)^rho.re ≤ 0.032 := by
    have he := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 0.001)
      (by norm_num : (0.001 : ℝ) ≤ 1) hr
    rw [← Real.sqrt_eq_rpow] at he
    exact he.trans ((Real.sqrt_le_left (by norm_num)).mpr (by norm_num))
  have hb : (0.998 : ℝ)^(rho.re + 1) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
  have hc : (0.001 : ℝ)^(rho.re + 1) ≤ 0.000032 := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
    nlinarith
  have hnorm := Complex.abs_im_le_norm rho
  have hnorm' : |rho.im| ≤ ‖rho + 1‖ := by
    simpa only [Complex.add_im, Complex.one_im, add_zero] using Complex.abs_im_le_norm (rho + 1)
  unfold linearShapeBound
  calc
    _ ≤ 1 / (|rho.im| * |rho.im|) +
        (0.998 * 0.032) / |rho.im| + 0.000032 / |rho.im| := by
      apply add_le_add
      · apply add_le_add
        · exact div_le_div₀ (by positivity) hb (mul_pos hg hg)
            (mul_le_mul hnorm hnorm' hg.le (norm_nonneg _))
        · exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left ha (by norm_num))
            hg hnorm
      · exact div_le_div₀ (by positivity) hc hg hnorm'
    _ ≤ _ := by
      rw [pow_two]
      have hi : 0 ≤ |rho.im|⁻¹ := inv_nonneg.mpr hg.le
      simp only [div_eq_mul_inv]
      nlinarith

theorem full_linear_high {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hr : 1/2 ≤ rho.re) (hg : 0 < |rho.im|) :
    ‖linearValue N rho‖ ≤ (N : ℝ)^2 * baseWeight N rho.re *
      (1 / |rho.im|^2 + 0.033 / |rho.im|) := by
  rw [linearValue, ← fullMoment_linear hN (by linarith)]
  exact (norm_fullMoment_linear hN (by linarith)).trans
    (mul_le_mul_of_nonneg_left (linearShapeBound_high hr hg) (by unfold baseWeight; positivity))

end LiuWang.Proof.MajorZeroMomentPayment.Continuation
