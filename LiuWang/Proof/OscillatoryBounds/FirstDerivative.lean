import LiuWang.Proof.OscillatoryBounds.Far

/-!
# 原对数相位的一阶导数界

对 `gamma + 2*pi*eta*t` 分离的子区间直接分部积分。
倒数相位的变差由 `t / (gamma + 2*pi*eta*t)` 的实际导数积分支付。
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Interval
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.VaughanTypeI (norm_charReal_eq_one)

namespace LiuWang.Proof.OscillatoryBounds

theorem norm_phase_denominator (gamma η t : ℝ) :
    ‖(gamma : ℂ) * Complex.I + (2 * Real.pi * η * Complex.I) * t‖ =
      |gamma + 2 * Real.pi * η * t| := by
  have h : (gamma : ℂ) * Complex.I + (2 * Real.pi * η * Complex.I) * t =
      ((gamma + 2 * Real.pi * η * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h]
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem reciprocal_phase_variation {a b gamma k m : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hm : 0 < m)
    (hsep : ∀ t ∈ Set.Icc a b, m * t ≤ |gamma + k * t|) :
    (∫ t in a..b, |gamma| / (gamma + k * t) ^ 2) ≤ 2 / m := by
  have hden : ∀ t ∈ Set.Icc a b, gamma + k * t ≠ 0 := by
    intro t ht
    exact abs_pos.mp ((mul_pos hm (ha.trans_le ht.1)).trans_le (hsep t ht))
  have hvi : IntervalIntegrable (fun t => 1 / (gamma + k * t) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.div (by fun_prop) (fun t ht => pow_ne_zero _ (hden t ht))
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => x / (gamma + k * x))
        (gamma / (gamma + k * t) ^ 2) t := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    convert! (hasDerivAt_id t).div
      (((hasDerivAt_id t).const_mul k).const_add gamma) (hden t ht) using 1
    simp only [id_eq, mul_one, one_mul]
    congr 1
    ring
  have hgi : IntervalIntegrable (fun t => gamma / (gamma + k * t) ^ 2) volume a b := by
    simpa only [mul_one_div] using hvi.const_mul gamma
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hgi
  have hnonneg : 0 ≤ ∫ t in a..b, 1 / (gamma + k * t) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun t _ => by positivity)
  have heq : (∫ t in a..b, |gamma| / (gamma + k * t) ^ 2) =
      |b / (gamma + k * b) - a / (gamma + k * a)| := by
    rw [← hFTC]
    simp_rw [div_eq_mul_inv, intervalIntegral.integral_const_mul, abs_mul]
    have hn : 0 ≤ ∫ t in a..b, ((gamma + k * t) ^ 2)⁻¹ := by
      simpa only [one_div] using hnonneg
    rw [abs_of_nonneg hn]
  have hq : ∀ t ∈ Set.Icc a b, |t / (gamma + k * t)| ≤ 1 / m := by
    intro t ht
    have ht0 := ha.trans_le ht.1
    rw [abs_div, abs_of_pos ht0]
    calc
      _ ≤ t / (m * t) :=
        div_le_div₀ ht0.le le_rfl (mul_pos hm ht0) (hsep t ht)
      _ = 1 / m := by field_simp
  rw [heq]
  calc
    _ ≤ |b / (gamma + k * b)| + |a / (gamma + k * a)| := abs_sub _ _
    _ ≤ 1 / m + 1 / m := add_le_add (hq b ⟨hab, le_rfl⟩) (hq a ⟨le_rfl, hab⟩)
    _ = 2 / m := by ring

theorem norm_integral_cpow_charReal_first_derivative {a b η m : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {rho : ℂ} (hr : rho ≠ 0)
    (hbeta : rho.re ≤ 1) (hm : 0 < m)
    (hsep : ∀ t ∈ Set.Icc a b, m * t ≤ |rho.im + 2 * Real.pi * η * t|) :
    ‖∫ t in a..b, (t : ℂ) ^ (rho - 1) * charReal (η * t)‖ ≤
      4 * a ^ (rho.re - 1) / m := by
  let A : ℝ := a ^ (rho.re - 1)
  let B : ℝ := b ^ (rho.re - 1)
  let d : ℝ → ℂ := fun t =>
    (rho.im : ℂ) * Complex.I + (2 * Real.pi * η * Complex.I) * t
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ (rho - 1) * charReal (η * t)
  let H : ℝ → ℂ := fun t => (t : ℂ) ^ rho * charReal (η * t) / d t
  let R : ℝ → ℂ := fun t => ((1 - rho.re : ℝ) : ℂ) * f t / d t -
    (rho.im : ℂ) * Complex.I * f t / d t ^ 2
  let W : ℝ → ℝ := fun t => (1 - rho.re) * t ^ (rho.re - 1 - 1)
  let V : ℝ → ℝ := fun t => |rho.im| / (rho.im + 2 * Real.pi * η * t) ^ 2
  have hA : 0 < A := Real.rpow_pos_of_pos ha _
  have hD : ∀ t ∈ Set.Icc a b, m * t ≤ ‖d t‖ := by
    intro t ht
    rw [show ‖d t‖ = _ from norm_phase_denominator rho.im η t]
    exact hsep t ht
  have hD0 : ∀ t ∈ Set.Icc a b, d t ≠ 0 := by
    intro t ht
    exact norm_ne_zero_iff.mp (ne_of_gt ((mul_pos hm (ha.trans_le ht.1)).trans_le (hD t ht)))
  have hrealD0 : ∀ t ∈ Set.Icc a b, rho.im + 2 * Real.pi * η * t ≠ 0 := by
    intro t ht
    exact abs_pos.mp ((mul_pos hm (ha.trans_le ht.1)).trans_le (hsep t ht))
  have hWi : IntervalIntegrable W volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.mul (continuousOn_id.rpow_const
      (fun t ht => Or.inl (ne_of_gt (ha.trans_le ht.1))))
  have hVi : IntervalIntegrable V volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.div (by fun_prop) (fun t ht => pow_ne_zero _ (hrealD0 t ht))
  have hWint : (∫ t in a..b, W t) = A - B := by
    have hd : ∀ t ∈ Set.uIcc a b,
        HasDerivAt (fun x : ℝ => -(x ^ (rho.re - 1))) (W t) t := by
      rw [Set.uIcc_of_le hab]
      intro t ht
      convert! (Real.hasDerivAt_rpow_const (p := rho.re - 1)
        (Or.inl (ne_of_gt (ha.trans_le ht.1)))).neg using 1
      ring
    simpa only [neg_sub_neg] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hWi
  have hVint : (∫ t in a..b, V t) ≤ 2 / m :=
    reciprocal_phase_variation ha hab hm hsep
  have hH : ∀ t ∈ Set.Icc a b, ‖H t‖ ≤ t ^ (rho.re - 1) / m := by
    intro t ht
    have ht0 := ha.trans_le ht.1
    dsimp [H]
    rw [norm_div, norm_mul, norm_charReal_eq_one, mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    calc
      _ ≤ t ^ rho.re / (m * t) :=
        div_le_div₀ (by positivity) le_rfl (by positivity) (hD t ht)
      _ = t ^ (rho.re - 1) / m := by rw [Real.rpow_sub_one ht0.ne']; ring
  have hR : ∀ t ∈ Set.Icc a b, ‖R t‖ ≤ W t / m + A * V t := by
    intro t ht
    have ht0 := ha.trans_le ht.1
    have htA : t ^ (rho.re - 1) ≤ A :=
      Real.rpow_le_rpow_of_nonpos ha ht.1 (sub_nonpos.mpr hbeta)
    have h1 : ‖((1 - rho.re : ℝ) : ℂ) * f t / d t‖ ≤ W t / m := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hbeta), norm_cpow_charReal ht0]
      calc
        _ ≤ (1 - rho.re) * t ^ (rho.re - 1) / (m * t) :=
          div_le_div₀ (by positivity) le_rfl (by positivity) (hD t ht)
        _ = W t / m := by
          dsimp [W]
          rw [Real.rpow_sub_one ht0.ne' (rho.re - 1)]
          ring
    have h2 : ‖(rho.im : ℂ) * Complex.I * f t / d t ^ 2‖ ≤ A * V t := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, norm_cpow_charReal ht0,
        norm_pow, show ‖d t‖ = _ from norm_phase_denominator rho.im η t, sq_abs]
      dsimp [V]
      calc
        _ ≤ |rho.im| * A / (rho.im + 2 * Real.pi * η * t) ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htA (abs_nonneg _))
            (sq_nonneg _)
        _ = _ := by ring
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hRc : ContinuousOn R (Set.Icc a b) := by
    have hfc := continuousOn_cpow_charReal ha rho η (b := b)
    have hdc : ContinuousOn d (Set.Icc a b) := by dsimp [d]; fun_prop
    exact ((continuousOn_const.mul hfc).div hdc hD0).sub
      ((continuousOn_const.mul hfc).div (hdc.pow 2) (fun t ht => pow_ne_zero _ (hD0 t ht)))
  have hRi : IntervalIntegrable R volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hab] using hRc
  have hRint : ‖∫ t in a..b, R t‖ ≤ (A - B) / m + A * (2 / m) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall fun t ht => hR t ⟨ht.1.le, ht.2⟩)
      ((hWi.div_const m).add (hVi.const_mul A))
    rw [intervalIntegral.integral_add (hWi.div_const m) (hVi.const_mul A),
      intervalIntegral.integral_div, intervalIntegral.integral_const_mul A,
      hWint] at h
    exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hVint hA.le))
  have hfi := intervalIntegrable_cpow_charReal ha hab rho η
  have hFTC : (∫ t in a..b, f t) = H b - H a + ∫ t in a..b, R t := by
    have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt H (f t - R t) t := by
      rw [Set.uIcc_of_le hab]
      intro t ht
      exact hasDerivAt_far_primitive (ha.trans_le ht.1) hr (hD0 t ht)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hfi.sub hRi)
    rw [intervalIntegral.integral_sub hfi hRi] at h
    exact sub_eq_iff_eq_add.mp h
  change ‖∫ t in a..b, f t‖ ≤ 4 * A / m
  rw [hFTC]
  calc
    _ ≤ ‖H b - H a‖ + ‖∫ t in a..b, R t‖ := norm_add_le _ _
    _ ≤ (‖H b‖ + ‖H a‖) + ‖∫ t in a..b, R t‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (B / m + A / m) + ((A - B) / m + A * (2 / m)) :=
      add_le_add (add_le_add (hH b ⟨hab, le_rfl⟩) (hH a ⟨le_rfl, hab⟩)) hRint
    _ = 4 * A / m := by ring

end LiuWang.Proof.OscillatoryBounds
