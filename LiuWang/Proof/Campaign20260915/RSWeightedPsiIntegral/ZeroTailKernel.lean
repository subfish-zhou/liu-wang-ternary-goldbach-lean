import LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.ZeroExchange

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral

def logCubeKernel (y : ℝ) : ℝ := 1 / (y * Real.log y ^ 3)

def zeroPower (p : RiemannXiDivisorZeroIndex) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (riemannXiDivisorZeroValue p - 1)

def zeroC (p : RiemannXiDivisorZeroIndex) (y : ℝ) : ℂ :=
  zeroPower p y / (riemannXiDivisorZeroValue p * (riemannXiDivisorZeroValue p - 1))

def zeroD (p : RiemannXiDivisorZeroIndex) (y : ℝ) : ℂ :=
  zeroPower p y / (riemannXiDivisorZeroValue p - 1) ^ 2

def zeroBoundary (p : RiemannXiDivisorZeroIndex) (y : ℝ) : ℂ :=
  zeroC p y / (Real.log y : ℂ) + zeroD p y / (Real.log y : ℂ) ^ 2

def zeroRemainder (p : RiemannXiDivisorZeroIndex) (y : ℝ) : ℂ :=
  2 * zeroD p y * (logCubeKernel y : ℂ)

def integratedZeroTail (p : RiemannXiDivisorZeroIndex) (x : ℝ) : ℂ :=
  -rsZeroPrimitive 1 x p * (weight x : ℂ) -
    ∫ y in Ioi x, rsZeroPrimitive 1 y p * (weightSlope y : ℂ)

theorem logCube_primitive_deriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y => -(Real.log y)⁻¹ ^ 2 / 2) (logCubeKernel x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  convert! (((Real.hasDerivAt_log hx0).inv hl).pow 2).neg.div_const 2 using 1
  simp only [logCubeKernel, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.inv_apply]
  field_simp

theorem logCube_primitive_limit :
    Tendsto (fun y => -(Real.log y)⁻¹ ^ 2 / 2) atTop (𝓝 0) := by
  have h := (Real.tendsto_log_atTop.inv_tendsto_atTop.pow 2).neg.div_const 2
  simpa using h

theorem logCubeKernel_integrable {x : ℝ} (hx : 1 < x) :
    IntegrableOn logCubeKernel (Ioi x) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun y hy => logCube_primitive_deriv (hx.trans_le hy))
    (fun y hy => by
      have hy0 : 0 < y := lt_trans zero_lt_one (hx.trans hy)
      have hl := Real.log_pos (hx.trans hy)
      unfold logCubeKernel
      positivity) logCube_primitive_limit

theorem logCubeKernel_integral {x : ℝ} (hx : 1 < x) :
    (∫ y in Ioi x, logCubeKernel y) = 1 / (2 * Real.log x ^ 2) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y hy => logCube_primitive_deriv (hx.trans_le hy))
    (logCubeKernel_integrable hx) logCube_primitive_limit
  rw [h]
  ring

theorem zero_ne (p : RiemannXiDivisorZeroIndex) :
    riemannXiDivisorZeroValue p ≠ 0 ∧ riemannXiDivisorZeroValue p - 1 ≠ 0 := by
  have hr := riemannXiDivisorZeroValue_re_mem_Ioo p
  constructor
  · intro he
    have h := congrArg Complex.re he
    simp only [Complex.zero_re] at h
    linarith [hr.1]
  · intro he
    have h := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h
    linarith [hr.2]

theorem zeroPower_norm (p : RiemannXiDivisorZeroIndex) {y : ℝ} (hy : 0 < y) :
    ‖zeroPower p y‖ = Real.exp (((riemannXiDivisorZeroValue p).re - 1) * Real.log y) := by
  rw [zeroPower, Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.sub_re, Complex.one_re,
    Real.rpow_def_of_pos hy, mul_comm]

theorem zeroC_norm_bound (p : RiemannXiDivisorZeroIndex) {y : ℝ} (hy : 0 < y) :
    ‖zeroC p y‖ ≤ rsZeroMoment 1 (Real.log y) p := by
  have ht : 0 < |(riemannXiDivisorZeroValue p).im| :=
    lt_trans (by norm_num) (xi_zero_height_gt_one p)
  have h1 := Complex.abs_im_le_norm (riemannXiDivisorZeroValue p)
  have h2 := Complex.abs_im_le_norm (riemannXiDivisorZeroValue p - 1)
  simp only [Complex.sub_im, Complex.one_im, sub_zero] at h2
  have hd : |(riemannXiDivisorZeroValue p).im| ^ 2 ≤
      ‖riemannXiDivisorZeroValue p‖ * ‖riemannXiDivisorZeroValue p - 1‖ := by
    simpa only [pow_two] using mul_le_mul h1 h2 ht.le (norm_nonneg _)
  rw [zeroC, norm_div, norm_mul, zeroPower_norm p hy]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (sq_pos_of_pos ht) hd

theorem zeroD_norm_bound (p : RiemannXiDivisorZeroIndex) {y : ℝ} (hy : 0 < y) :
    ‖zeroD p y‖ ≤ rsZeroMoment 1 (Real.log y) p := by
  have ht : 0 < |(riemannXiDivisorZeroValue p).im| :=
    lt_trans (by norm_num) (xi_zero_height_gt_one p)
  have h2 := Complex.abs_im_le_norm (riemannXiDivisorZeroValue p - 1)
  simp only [Complex.sub_im, Complex.one_im, sub_zero] at h2
  rw [zeroD, norm_div, norm_pow, zeroPower_norm p hy]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (sq_pos_of_pos ht)
    (pow_le_pow_left₀ ht.le h2 2)

theorem momentTerm_antitone (p : RiemannXiDivisorZeroIndex)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    rsZeroMoment 1 (Real.log y) p ≤ rsZeroMoment 1 (Real.log x) p := by
  unfold rsZeroMoment
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (Real.log_le_log hx hxy)
    (by linarith [(riemannXiDivisorZeroValue_re_mem_Ioo p).2])

theorem zeroBoundary_norm_bound (p : RiemannXiDivisorZeroIndex) {x : ℝ} (hx : 1 < x) :
    ‖zeroBoundary p x‖ ≤ rsZeroMoment 1 (Real.log x) p * scaledWeight x := by
  have hl := Real.log_pos hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  apply (norm_add_le _ _).trans
  simp only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]
  apply (add_le_add
    (div_le_div_of_nonneg_right (zeroC_norm_bound p hx0) hl.le)
    (div_le_div_of_nonneg_right (zeroD_norm_bound p hx0) (sq_nonneg _))).trans_eq
  unfold scaledWeight
  field_simp
  ring

theorem zeroBoundary_tendsto_zero (p : RiemannXiDivisorZeroIndex) :
    Tendsto (zeroBoundary p) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun y => rsZeroMoment 1 0 p * scaledWeight y)
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    exact (zeroBoundary_norm_bound p hy).trans
      (mul_le_mul_of_nonneg_right (momentTerm_le_zero hy.le p) (scaledWeight_nonneg hy))
  · simpa only [mul_zero] using scaledWeight_tendsto_zero.const_mul (rsZeroMoment 1 0 p)

theorem zeroRemainder_norm_bound (p : RiemannXiDivisorZeroIndex)
    {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    ‖zeroRemainder p y‖ ≤
      2 * rsZeroMoment 1 (Real.log x) p * logCubeKernel y := by
  have hy : 1 < y := hx.trans_le hxy
  have hl := Real.log_pos hy
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hk : 0 ≤ logCubeKernel y := by unfold logCubeKernel; positivity
  rw [zeroRemainder, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    ((zeroD_norm_bound p hy0).trans (momentTerm_antitone p (lt_trans zero_lt_one hx) hxy))
    (by norm_num)) hk

theorem zeroRemainder_integrable (p : RiemannXiDivisorZeroIndex) {x : ℝ} (hx : 1 < x) :
    IntegrableOn (zeroRemainder p) (Ioi x) := by
  refine ((logCubeKernel_integrable hx).const_mul (2 * rsZeroMoment 1 (Real.log x) p)).mono'
    (by
      apply Measurable.aestronglyMeasurable
      unfold zeroRemainder zeroD zeroPower logCubeKernel
      fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact zeroRemainder_norm_bound p hx hy.le

theorem zeroRemainder_integral_norm_bound (p : RiemannXiDivisorZeroIndex)
    {x : ℝ} (hx : 1 < x) :
    ‖∫ y in Ioi x, zeroRemainder p y‖ ≤ rsZeroMoment 1 (Real.log x) p / Real.log x ^ 2 := by
  apply (norm_integral_le_integral_norm _).trans
  have h := integral_mono_ae (zeroRemainder_integrable p hx).norm
    ((logCubeKernel_integrable hx).const_mul (2 * rsZeroMoment 1 (Real.log x) p))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact zeroRemainder_norm_bound p hx hy.le)
  rw [integral_const_mul, logCubeKernel_integral hx] at h
  exact h.trans_eq (by ring)

theorem zeroPower_hasDerivAt (p : RiemannXiDivisorZeroIndex) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (zeroPower p)
      ((riemannXiDivisorZeroValue p - 1) * zeroPower p x / (x : ℂ)) x := by
  have h := hasDerivAt_ofReal_cpow_const hx.ne' (zero_ne p).2
  convert! h using 1
  rw [Complex.cpow_sub _ 1 (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one]
  unfold zeroPower
  ring

theorem zeroBoundary_hasDerivAt (p : RiemannXiDivisorZeroIndex) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (zeroBoundary p)
      (rsZeroPrimitive 0 x p * (weight x : ℂ) - zeroRemainder p x) x := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hl : (Real.log x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hx).ne'
  have hp := zeroPower_hasDerivAt p hx0
  have hc := hp.div_const (riemannXiDivisorZeroValue p * (riemannXiDivisorZeroValue p - 1))
  have hd := hp.div_const ((riemannXiDivisorZeroValue p - 1) ^ 2)
  have hlog := (Real.hasDerivAt_log hx0.ne').ofReal_comp
  convert! (hc.div hlog hl).add (hd.div (hlog.pow 2) (pow_ne_zero _ hl)) using 1
  have he : (x : ℂ) ^ riemannXiDivisorZeroValue p = zeroPower p x * (x : ℂ) := by
    unfold zeroPower
    simpa only [sub_add_cancel, Complex.cpow_one] using
      (Complex.cpow_add (riemannXiDivisorZeroValue p - 1) 1 hxc)
  simp only [rsZeroPrimitive, Finset.prod_range_succ, Finset.prod_range_zero,
    Nat.cast_zero, add_zero, one_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
  rw [he]
  unfold zeroRemainder zeroD weight logCubeKernel
  push_cast
  field_simp [(zero_ne p).1, (zero_ne p).2, hxc, hl]
  ring

#print axioms zeroBoundary_hasDerivAt
#print axioms zeroRemainder_integral_norm_bound

end LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral
