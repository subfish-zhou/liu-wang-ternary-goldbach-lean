import LiuWang.Proof.OscillatoryBounds.Near

/-! # 远频段：原权重与分离的一阶相位 -/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Interval
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.VaughanTypeI (norm_charReal_eq_one)

namespace LiuWang.Proof.OscillatoryBounds

private theorem far_primitive_algebra (r beta g c z e x : ℂ)
    (hd : g + c * x ≠ 0) (hr : r = beta + g) :
    z * e - ((1 - beta) * (z * e) / (g + c * x) -
        g * (z * e) / (g + c * x) ^ 2) =
      ((r * z * e + z * x * (e * c)) * (g + c * x) -
        (z * x * e) * c) / (g + c * x) ^ 2 := by
  rw [hr]
  field_simp
  ring

theorem far_denominator_lower {a t η : ℝ} {rho : ℂ}
    (ha : 0 < a) (ht : a ≤ t)
    (hsep : 2 * |rho.im| ≤ (2 * Real.pi * |η|) * a) :
    (2 * Real.pi * |η|) * t / 2 ≤
      ‖(rho.im : ℂ) * Complex.I + (2 * Real.pi * η * Complex.I) * t‖ := by
  have hnorm : ‖(rho.im : ℂ) * Complex.I‖ = |rho.im| := by simp
  have hnormc : ‖(2 * Real.pi * η * Complex.I : ℂ) * t‖ =
      (2 * Real.pi * |η|) * t := by
    rw [norm_mul, norm_frequency, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ha.trans_le ht)]
  have htri := norm_sub_le
    ((rho.im : ℂ) * Complex.I + (2 * Real.pi * η * Complex.I) * t)
    ((rho.im : ℂ) * Complex.I)
  rw [add_sub_cancel_left, hnormc, hnorm] at htri
  have hmul := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * Real.pi * |η|)
  linarith

theorem hasDerivAt_far_primitive {t η : ℝ} {rho : ℂ}
    (ht : 0 < t) (hr : rho ≠ 0)
    (hd : (rho.im : ℂ) * Complex.I + (2 * Real.pi * η * Complex.I) * t ≠ 0) :
    HasDerivAt
      (fun x : ℝ => (x : ℂ) ^ rho * charReal (η * x) /
        ((rho.im : ℂ) * Complex.I + (2 * Real.pi * η * Complex.I) * x))
      ((t : ℂ) ^ (rho - 1) * charReal (η * t) -
        (((1 - rho.re : ℝ) : ℂ) * ((t : ℂ) ^ (rho - 1) * charReal (η * t)) /
          ((rho.im : ℂ) * Complex.I + (2 * Real.pi * η * Complex.I) * t) -
        (rho.im : ℂ) * Complex.I * ((t : ℂ) ^ (rho - 1) * charReal (η * t)) /
          ((rho.im : ℂ) * Complex.I + (2 * Real.pi * η * Complex.I) * t) ^ 2)) t := by
  have hpow := hasDerivAt_ofReal_cpow_const ht.ne' hr
  have hden := ((hasDerivAt_id t).ofReal_comp.const_mul
    (2 * Real.pi * η * Complex.I)).const_add ((rho.im : ℂ) * Complex.I)
  convert! (hpow.mul (hasDerivAt_charReal_mul η t)).div hden hd using 1
  have hp : (t : ℂ) ^ rho = (t : ℂ) ^ (rho - 1) * t := by
    simpa only [sub_add_cancel, Complex.cpow_one] using
      Complex.cpow_add (rho - 1) 1 (Complex.ofReal_ne_zero.mpr ht.ne')
  simp only [id_eq, Pi.mul_apply, Complex.ofReal_one, mul_one]
  rw [hp]
  push_cast
  exact far_primitive_algebra rho rho.re ((rho.im : ℂ) * Complex.I)
    (2 * Real.pi * η * Complex.I) ((t : ℂ) ^ (rho - 1))
    (charReal (η * t)) t hd (Complex.re_add_im rho).symm

theorem norm_integral_cpow_charReal_far_general {a b η : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {rho : ℂ} (hr : rho ≠ 0)
    (hbeta : rho.re ≤ 1) (hη : η ≠ 0)
    (hsep : 2 * |rho.im| ≤ (2 * Real.pi * |η|) * a) :
    ‖∫ t in a..b, (t : ℂ) ^ (rho - 1) * charReal (η * t)‖ ≤
      6 * a ^ (rho.re - 1) / (2 * Real.pi * |η|) := by
  let K : ℝ := 2 * Real.pi * |η|
  let G : ℝ := |rho.im|
  let A : ℝ := a ^ (rho.re - 1)
  let B : ℝ := b ^ (rho.re - 1)
  let d : ℝ → ℂ := fun t =>
    (rho.im : ℂ) * Complex.I + (2 * Real.pi * η * Complex.I) * t
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ (rho - 1) * charReal (η * t)
  let H : ℝ → ℂ := fun t => (t : ℂ) ^ rho * charReal (η * t) / d t
  let R : ℝ → ℂ := fun t =>
    ((1 - rho.re : ℝ) : ℂ) * f t / d t -
      (rho.im : ℂ) * Complex.I * f t / d t ^ 2
  let W : ℝ → ℝ := fun t => (1 - rho.re) * t ^ (rho.re - 1 - 1)
  have hb : 0 < b := ha.trans_le hab
  have hK : 0 < K := by dsimp [K]; positivity
  have hG : 0 ≤ G := abs_nonneg _
  have hA : 0 < A := Real.rpow_pos_of_pos ha _
  have hB : 0 < B := Real.rpow_pos_of_pos hb _
  have hD : ∀ t ∈ Set.Icc a b, K * t / 2 ≤ ‖d t‖ := by
    intro t ht
    exact far_denominator_lower ha ht.1 hsep
  have hD0 : ∀ t ∈ Set.Icc a b, d t ≠ 0 := by
    intro t ht
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le
      (by have := ha.trans_le ht.1; positivity) (hD t ht)))
  have hnorm : ∀ t ∈ Set.Icc a b, ‖f t‖ = t ^ (rho.re - 1) :=
    fun t ht => norm_cpow_charReal (ha.trans_le ht.1) rho η
  have hwle : ∀ t ∈ Set.Icc a b, t ^ (rho.re - 1) ≤ A := by
    intro t ht
    exact Real.rpow_le_rpow_of_nonpos ha ht.1 (sub_nonpos.mpr hbeta)
  have hH : ∀ t ∈ Set.Icc a b, ‖H t‖ ≤ 2 * t ^ (rho.re - 1) / K := by
    intro t ht
    have ht0 := ha.trans_le ht.1
    dsimp [H]
    rw [norm_div, norm_mul, norm_charReal_eq_one, mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    calc
      _ ≤ t ^ rho.re / (K * t / 2) :=
        div_le_div₀ (by positivity) le_rfl (by positivity) (hD t ht)
      _ = 2 * t ^ (rho.re - 1) / K := by
        rw [Real.rpow_sub_one ht0.ne']
        ring
  have hRc : ContinuousOn R (Set.Icc a b) := by
    have hfc := continuousOn_cpow_charReal ha rho η (b := b)
    have hdc : ContinuousOn d (Set.Icc a b) := by dsimp [d]; fun_prop
    exact ((continuousOn_const.mul hfc).div hdc hD0).sub
      ((continuousOn_const.mul hfc).div (hdc.pow 2) (fun t ht => pow_ne_zero _ (hD0 t ht)))
  have hWi : IntervalIntegrable W volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.mul (continuousOn_id.rpow_const
      (fun t ht => Or.inl (ne_of_gt (ha.trans_le ht.1))))
  have hVi : IntervalIntegrable (fun t : ℝ => t ^ (-2 : ℝ)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (ha.trans_le ht.1)))
  have hWint : (∫ t in a..b, W t) = A - B := by
    have hd : ∀ t ∈ Set.uIcc a b,
        HasDerivAt (fun x : ℝ => -(x ^ (rho.re - 1))) (W t) t := by
      rw [Set.uIcc_of_le hab]
      intro t ht
      convert! (Real.hasDerivAt_rpow_const (p := rho.re - 1)
        (Or.inl (ne_of_gt (ha.trans_le ht.1)))).neg using 1
      ring
    simpa only [neg_sub_neg] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd hWi
  have hVint : (∫ t in a..b, t ^ (-2 : ℝ)) = 1 / a - 1 / b := by
    rw [integral_rpow (Or.inr ⟨by norm_num, by
      rw [Set.uIcc_of_le hab]; exact fun h => (not_le_of_gt ha) h.1⟩)]
    norm_num [Real.rpow_neg_one]
    ring
  have hR : ∀ t ∈ Set.Icc a b,
      ‖R t‖ ≤ (2 / K) * W t + (4 * G * A / K ^ 2) * t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 := ha.trans_le ht.1
    have hn : 0 ≤ t ^ (rho.re - 1) := Real.rpow_nonneg ht0.le _
    have hterm1 :
        ‖((1 - rho.re : ℝ) : ℂ) * f t / d t‖ ≤ (2 / K) * W t := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hbeta), hnorm t ht]
      calc
        _ ≤ (1 - rho.re) * t ^ (rho.re - 1) / (K * t / 2) :=
          div_le_div₀ (by positivity) le_rfl (by positivity) (hD t ht)
        _ = (2 / K) * W t := by
          dsimp [W]
          rw [Real.rpow_sub_one ht0.ne' (rho.re - 1)]
          ring
    have hterm2 :
        ‖(rho.im : ℂ) * Complex.I * f t / d t ^ 2‖ ≤
          (4 * G * A / K ^ 2) * t ^ (-2 : ℝ) := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, hnorm t ht, norm_pow]
      calc
        _ ≤ G * A / (K * t / 2) ^ 2 :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (hwle t ht) hG)
            (by positivity) (pow_le_pow_left₀ (by positivity) (hD t ht) 2)
        _ = (4 * G * A / K ^ 2) * t ^ (-2 : ℝ) := by
          rw [Real.rpow_neg ht0.le, Real.rpow_two]
          ring
    exact (norm_sub_le _ _).trans (add_le_add hterm1 hterm2)
  have hRi : IntervalIntegrable R volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hab] using hRc
  have hRint : ‖∫ t in a..b, R t‖ ≤ (2 / K) * (A - B) + 2 * A / K := by
    have h := intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall fun t ht => hR t ⟨ht.1.le, ht.2⟩)
      ((hWi.const_mul (2 / K)).add (hVi.const_mul (4 * G * A / K ^ 2)))
    rw [intervalIntegral.integral_add (hWi.const_mul _) (hVi.const_mul _),
      intervalIntegral.integral_const_mul (2 / K) W,
      intervalIntegral.integral_const_mul (4 * G * A / K ^ 2),
      hWint, hVint] at h
    apply h.trans
    apply add_le_add le_rfl
    calc
      (4 * G * A / K ^ 2) * (1 / a - 1 / b) ≤ (4 * G * A / K ^ 2) * (1 / a) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
      _ ≤ 2 * A / K := by
        have hsep' : 2 * G ≤ K * a := hsep
        have hm := mul_le_mul_of_nonneg_right hsep' hA.le
        field_simp
        nlinarith
  have hfi := intervalIntegrable_cpow_charReal ha hab rho η
  have hFTC : (∫ t in a..b, f t) = H b - H a + ∫ t in a..b, R t := by
    have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt H (f t - R t) t := by
      rw [Set.uIcc_of_le hab]
      intro t ht
      exact hasDerivAt_far_primitive (ha.trans_le ht.1) hr (hD0 t ht)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hfi.sub hRi)
    rw [intervalIntegral.integral_sub hfi hRi] at h
    exact sub_eq_iff_eq_add.mp h
  change ‖∫ t in a..b, f t‖ ≤ 6 * A / K
  rw [hFTC]
  calc
    _ ≤ ‖H b - H a‖ + ‖∫ t in a..b, R t‖ := norm_add_le _ _
    _ ≤ (‖H b‖ + ‖H a‖) + ‖∫ t in a..b, R t‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (2 * B / K + 2 * A / K) + ((2 / K) * (A - B) + 2 * A / K) :=
      add_le_add (add_le_add (hH b ⟨hab, le_rfl⟩) (hH a ⟨le_rfl, hab⟩)) hRint
    _ = 6 * A / K := by ring

theorem norm_integral_cpow_charReal_far {N : ℝ} (hN : 0 < N)
    {rho : ℂ} (hbeta : rho.re ≤ 1) (hgamma : rho.im ≠ 0) {η : ℝ}
    (hη : |rho.im| / (0.001 * Real.pi * N) ≤ |η|) :
    ‖∫ t in N / 1000..N, (t : ℂ) ^ (rho - 1) * charReal (η * t)‖ ≤
      (4 / Real.pi) * (0.001 * N) ^ (rho.re - 1) / |η| := by
  have hG : 0 < |rho.im| := abs_pos.mpr hgamma
  have hη0 : η ≠ 0 := by
    have : 0 < |η| := (div_pos hG (by positivity)).trans_le hη
    exact abs_pos.mp this
  have hsep : 2 * |rho.im| ≤ (2 * Real.pi * |η|) * (N / 1000) := by
    have h := (div_le_iff₀ (by positivity : 0 < 0.001 * Real.pi * N)).mp hη
    nlinarith
  have hr : rho ≠ 0 := fun h => hgamma (by simp [h])
  have h := norm_integral_cpow_charReal_far_general (by positivity : 0 < N / 1000)
    (by linarith : N / 1000 ≤ N) hr hbeta hη0 hsep
  apply h.trans
  rw [show N / 1000 = (0.001 : ℝ) * N by ring]
  have hpos : 0 < (0.001 * N) ^ (rho.re - 1) := Real.rpow_pos_of_pos (by positivity) _
  have hηpos := abs_pos.mpr hη0
  field_simp
  nlinarith

end LiuWang.Proof.OscillatoryBounds
