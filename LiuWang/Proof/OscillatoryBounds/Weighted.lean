import LiuWang.Proof.OscillatoryBounds.Main

/-! # 非负递减权的分部积分估计 -/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Interval
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.VaughanTypeI (norm_charReal_eq_one)

namespace LiuWang.Proof.OscillatoryBounds

theorem norm_integral_weight_mul_le {a b C : ℝ} {g g' : ℝ → ℝ} {F G : ℝ → ℂ}
    (hab : a ≤ b)
    (hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hg' : ContinuousOn g' (Set.Icc a b))
    (hgpos : ∀ t ∈ Set.Icc a b, 0 ≤ g t)
    (hgneg : ∀ t ∈ Set.Icc a b, g' t ≤ 0)
    (hG : ∀ t ∈ Set.Icc a b, HasDerivAt G (F t) t)
    (hF : IntervalIntegrable F volume a b)
    (hbound : ∀ t ∈ Set.Icc a b, ‖G t‖ ≤ C) :
    ‖∫ t in a..b, (g t : ℂ) * F t‖ ≤ 2 * g a * C := by
  have hgu : ∀ t ∈ Set.uIcc a b, HasDerivAt g (g' t) t := by
    simpa only [Set.uIcc_of_le hab] using hg
  have hGu : ∀ t ∈ Set.uIcc a b, HasDerivAt G (F t) t := by
    simpa only [Set.uIcc_of_le hab] using hG
  have hgi : IntervalIntegrable g' volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hab] using hg'
  have hgci : IntervalIntegrable (fun t => (g' t : ℂ)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact Complex.continuous_ofReal.comp_continuousOn hg'
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => (hgu t ht).ofReal_comp) hGu hgci hF
  have hvariation : (∫ t in a..b, -g' t * C) = (g a - g b) * C := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hgu hgi]
    ring
  have hrem : ‖∫ t in a..b, (g' t : ℂ) * G t‖ ≤ (g a - g b) * C := by
    rw [← hvariation]
    apply intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall fun t ht => ?_) (hgi.neg.mul_const C)
    have ht' : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (hgneg t ht')]
    exact mul_le_mul_of_nonneg_left (hbound t ht') (neg_nonneg.mpr (hgneg t ht'))
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hea : ‖(g a : ℂ) * G a‖ ≤ g a * C := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgpos a ha)]
    exact mul_le_mul_of_nonneg_left (hbound a ha) (hgpos a ha)
  have heb : ‖(g b : ℂ) * G b‖ ≤ g b * C := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgpos b hb)]
    exact mul_le_mul_of_nonneg_left (hbound b hb) (hgpos b hb)
  rw [hparts]
  calc
    _ ≤ ‖(g b : ℂ) * G b - (g a : ℂ) * G a‖ +
        ‖∫ t in a..b, (g' t : ℂ) * G t‖ := norm_sub_le _ _
    _ ≤ (‖(g b : ℂ) * G b‖ + ‖(g a : ℂ) * G a‖) +
        ‖∫ t in a..b, (g' t : ℂ) * G t‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ g b * C + g a * C + (g a - g b) * C :=
      add_le_add (add_le_add heb hea) hrem
    _ = 2 * g a * C := by ring

theorem hasDerivAt_charReal_mul (η t : ℝ) :
    HasDerivAt (fun x => charReal (η * x))
      (charReal (η * t) * (2 * Real.pi * η * Complex.I)) t := by
  simp_rw [charReal_mul_eq_exp]
  simpa using (((hasDerivAt_id t).ofReal_comp.const_mul
    (2 * Real.pi * η * Complex.I)).cexp)

theorem norm_integral_rpow_charReal_le {a b beta η : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : beta ≤ 1) (hη : η ≠ 0) :
    ‖∫ t in a..b, (t ^ (beta - 1) : ℝ) • charReal (η * t)‖ ≤
      a ^ (beta - 1) / (Real.pi * |η|) := by
  let c : ℂ := 2 * Real.pi * η * Complex.I
  have hc : c ≠ 0 := by
    apply norm_ne_zero_iff.mp
    dsimp [c]
    rw [norm_frequency]
    exact ne_of_gt (by positivity)
  have hgp : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun x : ℝ => x ^ (beta - 1))
        ((beta - 1) * t ^ (beta - 1 - 1)) t := by
    intro t ht
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (ha.trans_le ht.1)))
  have hgc : ContinuousOn (fun t : ℝ => (beta - 1) * t ^ (beta - 1 - 1))
      (Set.Icc a b) := by
    apply continuousOn_const.mul
    exact continuousOn_id.rpow_const
      (fun t ht => Or.inl (ne_of_gt (ha.trans_le ht.1)))
  have hG : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun x => charReal (η * x) / c) (charReal (η * t)) t := by
    intro t _
    simpa only [show (2 * Real.pi * η * Complex.I : ℂ) = c from rfl,
      mul_div_cancel_right₀ _ hc] using (hasDerivAt_charReal_mul η t).div_const c
  have hbound : ∀ t ∈ Set.Icc a b, ‖charReal (η * t) / c‖ ≤
      1 / (2 * Real.pi * |η|) := by
    intro t _
    simp only [norm_div, norm_charReal_eq_one, c, norm_frequency, le_refl]
  have h := norm_integral_weight_mul_le hab
    hgp hgc (fun t ht => Real.rpow_nonneg (ha.trans_le ht.1).le _)
    (fun t ht => mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb)
      (Real.rpow_nonneg (ha.trans_le ht.1).le _))
    hG (intervalIntegrable_charReal a b η) hbound
  change ‖∫ t in a..b, (↑(t ^ (beta - 1)) : ℂ) * charReal (η * t)‖ ≤ _
  convert h using 1
  ring

theorem norm_integral_real_cpow_charReal_le {a b beta η : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : beta ≤ 1) (hη : η ≠ 0) :
    ‖∫ t in a..b, (t : ℂ) ^ ((beta : ℂ) - 1) * charReal (η * t)‖ ≤
      a ^ (beta - 1) / (Real.pi * |η|) := by
  have heq :
      (∫ t in a..b, (t : ℂ) ^ ((beta : ℂ) - 1) * charReal (η * t)) =
      ∫ t in a..b, (t ^ (beta - 1) : ℝ) • charReal (η * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    dsimp only
    rw [Complex.real_smul, Complex.ofReal_cpow (ha.trans_le ht.1).le]
    push_cast
    rfl
  rw [heq]
  exact norm_integral_rpow_charReal_le ha hab hb hη

end LiuWang.Proof.OscillatoryBounds
