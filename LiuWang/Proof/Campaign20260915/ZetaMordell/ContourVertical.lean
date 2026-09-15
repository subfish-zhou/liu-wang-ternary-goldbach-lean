import LiuWang.Proof.Campaign20260915.ZetaMordell.ContourRegularization

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Filter Set
open scoped Real Topology

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

def mordellLinearCoeff (a : ℂ) : ℂ := 2 * Real.pi * I * a * mordellRotor

def mordellVerticalBound (a : ℂ) : ℝ :=
  ‖mordellRotor‖ * 2 *
    Real.exp (2 * ‖mordellLinearCoeff a‖ ^ 2 + ‖mordellLinearCoeff a‖ + Real.pi / 8)

theorem mordellRotated_exp_norm (w : ℂ) :
    ‖exp (2 * Real.pi * I * mordellRotor * w)‖ =
      Real.exp (-Real.pi / 2 * (w.re + w.im)) := by
  rw [norm_exp]
  congr 1
  simp [mordellRotor, mul_re, mul_im]
  ring

theorem mordellRotated_denominator_inv_le {w : ℂ}
    (hr : 3 ≤ |w.re|) (hi : |w.im| ≤ 1) :
    ‖(exp (2 * Real.pi * I * mordellRotor * w) - 1)⁻¹‖ ≤ 2 := by
  have him := abs_le.mp hi
  have hl : 1 / 2 ≤ ‖exp (2 * Real.pi * I * mordellRotor * w) - 1‖ := by
    rcases le_abs.mp hr with hp | hn
    · have harg : 1 ≤ Real.pi / 2 * (w.re + w.im) := by
        nlinarith [Real.two_le_pi]
      have he : 2 ≤ Real.exp (Real.pi / 2 * (w.re + w.im)) :=
        le_trans (by linarith) (Real.add_one_le_exp _)
      have hi' : Real.exp (-Real.pi / 2 * (w.re + w.im)) ≤ 1 / 2 := by
        rw [show -Real.pi / 2 * (w.re + w.im) = -(Real.pi / 2 * (w.re + w.im)) by ring,
          Real.exp_neg]
        exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 2)).mpr
          (by norm_num; exact he)
      have h := norm_sub_norm_le (1 : ℂ) (exp (2 * Real.pi * I * mordellRotor * w))
      rw [norm_one, mordellRotated_exp_norm, norm_sub_rev] at h
      linarith
    · have harg : 1 ≤ -Real.pi / 2 * (w.re + w.im) := by
        nlinarith [Real.two_le_pi]
      have he := Real.add_one_le_exp (-Real.pi / 2 * (w.re + w.im))
      have h := norm_sub_norm_le (exp (2 * Real.pi * I * mordellRotor * w)) (1 : ℂ)
      rw [mordellRotated_exp_norm, norm_one] at h
      linarith
  rw [norm_inv]
  exact (inv_le_comm₀ (lt_of_lt_of_le (by norm_num) hl) (by norm_num : (0 : ℝ) < 2)).mpr
    (by norm_num; exact hl)

theorem mordellRotated_phase (a w : ℂ) :
    Real.pi * I * (mordellRotor * w) ^ 2 +
      2 * Real.pi * I * a * (mordellRotor * w) =
        (-Real.pi / 8 : ℂ) * w ^ 2 + mordellLinearCoeff a * w := by
  unfold mordellLinearCoeff mordellRotor
  ring_nf
  simp only [I_sq, I_pow_three]
  ring

theorem mordellRotated_gaussian_bound (a : ℂ) {T y : ℝ} (hy : |y| ≤ 1) :
    ‖exp (Real.pi * I * (mordellRotor * ((T : ℂ) + y * I)) ^ 2 +
      2 * Real.pi * I * a * (mordellRotor * ((T : ℂ) + y * I)))‖ ≤
        Real.exp (2 * ‖mordellLinearCoeff a‖ ^ 2 + ‖mordellLinearCoeff a‖ + Real.pi / 8) *
          Real.exp (-Real.pi / 16 * T ^ 2) := by
  rw [mordellRotated_phase, norm_exp, ← Real.exp_add, Real.exp_le_exp]
  have hw : ‖(T : ℂ) + y * I‖ ≤ |T| + 1 := by
    have h := norm_add_le (T : ℂ) ((y : ℂ) * I)
    simp only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  have hb := (re_le_norm (mordellLinearCoeff a * ((T : ℂ) + y * I))).trans
    (by simpa [norm_mul] using mul_le_mul_of_nonneg_left hw (norm_nonneg (mordellLinearCoeff a)))
  have hq : (((-Real.pi / 8 : ℂ) * ((T : ℂ) + y * I) ^ 2)).re =
      -Real.pi / 8 * (T ^ 2 - y ^ 2) := by
    simp [pow_two, mul_re, mul_im]
  rw [add_re, hq]
  have hy2 : y ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one y).mpr hy
  have ht := sq_nonneg (|T| - 4 * ‖mordellLinearCoeff a‖)
  have hp := mul_nonneg (show 0 ≤ Real.pi - 2 by linarith [Real.two_le_pi]) (sq_nonneg T)
  nlinarith [sq_abs T, mul_le_mul_of_nonneg_left hy2 Real.pi_pos.le]

theorem mordellRotated_vertical_bound (a : ℂ) {T y : ℝ}
    (hT : 3 ≤ |T|) (hy : |y| ≤ 1) :
    ‖mordellRotatedKernel a ((T : ℂ) + y * I)‖ ≤
      mordellVerticalBound a * Real.exp (-Real.pi / 16 * T ^ 2) := by
  have hd : ‖(exp (2 * Real.pi * I * mordellRotor * ((T : ℂ) + y * I)) - 1)⁻¹‖ ≤ 2 :=
    mordellRotated_denominator_inv_le (by simpa using hT) (by simpa using hy)
  have hg := mordellRotated_gaussian_bound a (T := T) hy
  unfold mordellRotatedKernel
  rw [div_eq_mul_inv, norm_mul, norm_mul]
  calc
    _ ≤ ‖mordellRotor‖ *
      (Real.exp (2 * ‖mordellLinearCoeff a‖ ^ 2 + ‖mordellLinearCoeff a‖ + Real.pi / 8) *
        Real.exp (-Real.pi / 16 * T ^ 2)) * 2 := by gcongr
    _ = _ := by unfold mordellVerticalBound; ring

theorem mordellRegular_vertical_bound (a : ℂ) {T y : ℝ}
    (hT : 3 ≤ |T|) (hy : |y| ≤ 1) :
    ‖mordellRegularKernel a ((T : ℂ) + y * I)‖ ≤
      mordellVerticalBound a * Real.exp (-Real.pi / 16 * T ^ 2) +
        ‖(2 * Real.pi * I : ℂ)⁻¹‖ / |T| := by
  have hT0 : 0 < |T| := by linarith
  have hw : (T : ℂ) + y * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
      sub_self, add_zero, zero_re] at this
    norm_num [this] at hT
  rw [mordellRegularKernel_eq a (by simpa using hy) hw]
  apply (norm_sub_le _ _).trans
  apply add_le_add (mordellRotated_vertical_bound a hT hy)
  rw [norm_div]
  apply div_le_div_of_nonneg_left (norm_nonneg _) hT0
  simpa using abs_re_le_norm ((T : ℂ) + y * I)

theorem mordellRegular_vertical_tendsto {ι : Type*} {l : Filter ι} {T : ι → ℝ}
    (a : ℂ) (hT : Tendsto (fun i => |T i|) l atTop) :
    Tendsto (fun i => ∫ y in (-1 : ℝ)..1, mordellRegularKernel a ((T i : ℂ) + y * I))
      l (𝓝 0) := by
  have hg : Tendsto (fun i => Real.exp (-Real.pi / 16 * T i ^ 2)) l (𝓝 0) := by
    have hsq : Tendsto (fun i => |T i| ^ 2) l atTop :=
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hT
    have hx := Real.tendsto_exp_atBot.comp
      (hsq.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos] : -Real.pi / 16 < 0))
    simpa only [sq_abs, Function.comp_def] using hx
  have hi : Tendsto (fun i => ‖(2 * Real.pi * I : ℂ)⁻¹‖ / |T i|) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hT
  have hb : Tendsto (fun i => (mordellVerticalBound a * Real.exp (-Real.pi / 16 * T i ^ 2) +
      ‖(2 * Real.pi * I : ℂ)⁻¹‖ / |T i|) * 2) l (𝓝 0) := by
    simpa using ((hg.const_mul (mordellVerticalBound a)).add hi).mul_const 2
  apply squeeze_zero_norm' _ hb
  filter_upwards [hT.eventually (eventually_ge_atTop 3)] with i hi
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 : ℝ)) (b := 1)
    (f := fun y : ℝ => mordellRegularKernel a ((T i : ℂ) + y * I))
    (fun y hy => mordellRegular_vertical_bound a hi (by
      have hy' : -1 < y ∧ y ≤ 1 := by simpa only [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1), mem_Ioc] using hy
      exact abs_le.mpr ⟨hy'.1.le, hy'.2⟩))
  norm_num at h ⊢
  exact h

end LiuWang.Proof.Campaign20260915.ZetaMordell
