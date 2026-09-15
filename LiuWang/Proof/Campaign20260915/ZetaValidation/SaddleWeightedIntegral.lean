import LiuWang.Proof.Campaign20260915.ZetaValidation.SaddleWeightedBounds

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsJnOuterConstant (sigma d : ℝ) (N : ℕ) : ℝ :=
  21 * Real.exp (|sigma - 1| * Real.log (5 / 2)) * (20 / 21 : ℝ) ^ N /
    (1 - Real.exp (-Real.sqrt 2 * Real.pi * d))

theorem rsJnOuterConstant_pos (sigma : ℝ) {d : ℝ} (hd : 0 < d) (N : ℕ) :
    0 < rsJnOuterConstant sigma d N := by
  have hx : -Real.sqrt 2 * Real.pi * d < 0 := by
    have := mul_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)) Real.pi_pos) hd
    nlinarith
  unfold rsJnOuterConstant
  exact div_pos (by positivity) (sub_pos.mpr (Real.exp_lt_one_iff.mpr hx))

theorem rsJnIntegrand_continuousAt (sigma : ℝ) (m N : ℕ) {eta y : ℝ}
    (he : 0 < eta) (hy : 0 < |y|) (hye : |y| < eta) :
    ContinuousAt (rsJnIntegrand sigma eta m N) y := by
  have hD : rsHankelDenominator (rsDescentPoint eta y) ≠ 0 := by
    have hp : 0 < 1 - Real.exp (-Real.sqrt 2 * Real.pi * |y|) := by
      apply sub_pos.mpr
      apply Real.exp_lt_one_iff.mpr
      have := mul_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)) Real.pi_pos) hy
      nlinarith
    exact norm_pos_iff.mp (hp.trans_le (rsDescent_denominator_lower eta le_rfl))
  have hz : ‖(rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)‖ < rsSaddleScale * eta := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos rsSaddleScale_pos,
      rsDescentPoint_distance]
    exact mul_lt_mul_of_pos_left hye rsSaddleScale_pos
  have hw : ContinuousAt (fun y : ℝ => rsSaddleWeight sigma (rsSaddleScale * eta)
      ((rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta))) y := by
    exact ContinuousAt.comp (f := fun y : ℝ =>
      (rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta))
      (rsSaddle_analytic sigma (mul_pos rsSaddleScale_pos he) hz).continuousAt
      (by unfold rsDescentPoint; fun_prop)
  have hg : ContinuousAt (fun y : ℝ => rsGaussianKernel eta m (rsDescentPoint eta y)) y := by
    unfold rsGaussianKernel
    apply ContinuousAt.div
    · unfold rsDescentPoint
      fun_prop
    · unfold rsHankelDenominator rsDescentPoint
      fun_prop
    · exact hD
  unfold rsJnIntegrand rsSaddleRemainder
  apply (continuousAt_const.mul hg).mul (hw.sub ?_)
  unfold rsDescentPoint
  fun_prop

theorem rsGaussian_tail_interval {c d A : ℝ} (hc : 0 < c) (hd : 0 < d) (hA : d ≤ A) :
    (∫ y : ℝ in d..A, Real.exp (-c * y ^ 2)) ≤ Real.exp (-c * d ^ 2) / (2 * c * d) := by
  have hi : IntervalIntegrable (fun y : ℝ => y * Real.exp (-c * y ^ 2)) volume d A :=
    (by fun_prop : Continuous (fun y : ℝ => y * Real.exp (-c * y ^ 2))).intervalIntegrable _ _
  have hprim : (∫ y : ℝ in d..A, y * Real.exp (-c * y ^ 2)) =
      (Real.exp (-c * d ^ 2) - Real.exp (-c * A ^ 2)) / (2 * c) := by
    have hder (y : ℝ) :
        HasDerivAt (fun x : ℝ => -Real.exp (-c * x ^ 2) / (2 * c))
          (y * Real.exp (-c * y ^ 2)) y := by
      have h := (((((hasDerivAt_id y).pow 2).const_mul (-c)).exp).neg).div_const (2 * c)
      simp only [id_eq, Pi.pow_apply, mul_one, pow_one, Nat.cast_ofNat, Nat.reduceSub] at h
      convert! h using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hder y) hi]
    ring
  have hg : IntervalIntegrable (fun y : ℝ => Real.exp (-c * y ^ 2)) volume d A :=
    (by fun_prop : Continuous (fun y : ℝ => Real.exp (-c * y ^ 2))).intervalIntegrable _ _
  calc
    _ ≤ ∫ y : ℝ in d..A, (y * Real.exp (-c * y ^ 2)) / d :=
      intervalIntegral.integral_mono_on hA hg (hi.div_const d) (fun y hy => by
        rw [le_div_iff₀ hd]
        nlinarith [mul_le_mul_of_nonneg_right hy.1 (Real.exp_pos (-c * y ^ 2)).le])
    _ = (Real.exp (-c * d ^ 2) - Real.exp (-c * A ^ 2)) / (2 * c * d) := by
      rw [intervalIntegral.integral_div, hprim]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-c * A ^ 2)]) (by positivity)

theorem rsJn_outer_half_bound (sigma : ℝ) {eta d A e : ℝ} {m : ℕ}
    (he : 0 < eta) (hd : 0 < d) (hAd : d ≤ A) (hAe : A ≤ eta / 2)
    (hlarge : 58 * Real.sqrt 2 ≤ d) (heps : |e| = 1)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖∫ y : ℝ in d..A, rsJnIntegrand sigma eta m N (e * y)‖ ≤
      rsJnOuterConstant sigma d N * (29 / (Real.pi * d)) * Real.exp (-Real.pi / 58 * d ^ 2) := by
  have hC := rsJnOuterConstant_pos sigma hd N
  have hb (y : ℝ) (hy : y ∈ Icc d A) :
      ‖rsJnIntegrand sigma eta m N (e * y)‖ ≤
        rsJnOuterConstant sigma d N * Real.exp (-Real.pi / 58 * y ^ 2) := by
    have hy0 : 0 ≤ y := le_trans hd.le hy.1
    have hnorm : |e * y| = y := by rw [abs_mul, heps, abs_of_nonneg hy0, one_mul]
    have hsquare : (e * y) ^ 2 = y ^ 2 := by
      rw [← sq_abs (e * y), hnorm]
    have h := rsJnIntegrand_bound sigma he hd (by rw [hnorm]; exact hy.1)
      (by rw [hnorm]; linarith [hy.2]) hm0 hm1 N
    rw [hnorm, hsquare] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
    have hl : 58 * Real.sqrt 2 ≤ y := hlarge.trans hy.1
    nlinarith [mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hl hy0) Real.pi_pos.le]
  have hi : IntervalIntegrable (fun y : ℝ =>
      rsJnOuterConstant sigma d N * Real.exp (-Real.pi / 58 * y ^ 2)) volume d A :=
    (by fun_prop : Continuous (fun y : ℝ =>
      rsJnOuterConstant sigma d N * Real.exp (-Real.pi / 58 * y ^ 2))).intervalIntegrable _ _
  calc
    _ ≤ ∫ y : ℝ in d..A, rsJnOuterConstant sigma d N * Real.exp (-Real.pi / 58 * y ^ 2) :=
      intervalIntegral.norm_integral_le_of_norm_le hAd
        (Filter.Eventually.of_forall (fun y hy => hb y ⟨hy.1.le, hy.2⟩)) hi
    _ = rsJnOuterConstant sigma d N *
        (∫ y : ℝ in d..A, Real.exp (-Real.pi / 58 * y ^ 2)) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ rsJnOuterConstant sigma d N *
        (Real.exp (-Real.pi / 58 * d ^ 2) / (2 * (Real.pi / 58) * d)) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [neg_div] using
          rsGaussian_tail_interval (by positivity : 0 < Real.pi / 58) hd hAd) hC.le
    _ = _ := by ring

theorem rsJn_outer_integrals (sigma : ℝ) {eta d A : ℝ} {m : ℕ}
    (he : 0 < eta) (hd : 0 < d) (hAd : d ≤ A) (hAe : A ≤ eta / 2)
    (hlarge : 58 * Real.sqrt 2 ≤ d) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    IntervalIntegrable (rsJnIntegrand sigma eta m N) volume d A ∧
    IntervalIntegrable (rsJnIntegrand sigma eta m N) volume (-A) (-d) ∧
    ‖∫ y : ℝ in d..A, rsJnIntegrand sigma eta m N y‖ +
      ‖∫ y : ℝ in (-A)..(-d), rsJnIntegrand sigma eta m N y‖ ≤
        2 * rsJnOuterConstant sigma d N * (29 / (Real.pi * d)) *
          Real.exp (-Real.pi / 58 * d ^ 2) := by
  have hcont : ∀ {y : ℝ}, d ≤ |y| → |y| ≤ A →
      ContinuousAt (rsJnIntegrand sigma eta m N) y := fun hy hA =>
    rsJnIntegrand_continuousAt sigma m N he (hd.trans_le hy) (by linarith)
  have hip : IntervalIntegrable (rsJnIntegrand sigma eta m N) volume d A := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [uIcc_of_le hAd] at hy
    exact (hcont (by rw [abs_of_nonneg (hd.le.trans hy.1)]; exact hy.1)
      (by rw [abs_of_nonneg (hd.le.trans hy.1)]; exact hy.2)).continuousWithinAt
  have hin : IntervalIntegrable (rsJnIntegrand sigma eta m N) volume (-A) (-d) := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [uIcc_of_le (by linarith : -A ≤ -d)] at hy
    have hy0 : y ≤ 0 := by linarith [hy.2]
    exact (hcont (by rw [abs_of_nonpos hy0]; linarith [hy.2])
      (by rw [abs_of_nonpos hy0]; linarith [hy.1])).continuousWithinAt
  have hp := rsJn_outer_half_bound sigma he hd hAd hAe hlarge
    (e := 1) (by norm_num) hm0 hm1 N
  have hn := rsJn_outer_half_bound sigma he hd hAd hAe hlarge
    (e := -1) (by norm_num) hm0 hm1 N
  simp only [one_mul] at hp
  simp only [neg_one_mul, intervalIntegral.integral_comp_neg] at hn
  exact ⟨hip, hin, by linarith⟩

end LiuWang.Proof.Campaign20260915.ZetaValidation
