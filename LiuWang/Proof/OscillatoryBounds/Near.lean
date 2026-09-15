import LiuWang.Proof.OscillatoryBounds.Weighted

/-! # 近频段：显式复分母的分部积分余项 -/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Interval
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.VaughanTypeI (norm_charReal_eq_one)

namespace LiuWang.Proof.OscillatoryBounds

theorem near_denominator_lower {N t η : ℝ} {rho : ℂ}
    (ht : 0 ≤ t) (htN : t ≤ N)
    (hη : (2 * Real.pi * |η|) * N ≤ |rho.im| / 5) :
    |rho.im| / 2 ≤ ‖rho + (2 * Real.pi * η * Complex.I) * t‖ := by
  have he : (rho + (2 * Real.pi * η * Complex.I) * t).im =
      rho.im + 2 * Real.pi * η * t := by simp
  have habs : |2 * Real.pi * η * t| = 2 * Real.pi * |η| * t := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_nonneg ht]
    norm_num
  have htri : |rho.im| ≤
      |rho.im + 2 * Real.pi * η * t| + 2 * Real.pi * |η| * t := by
    have h := abs_sub (rho.im + 2 * Real.pi * η * t) (2 * Real.pi * η * t)
    simpa only [add_sub_cancel_right, habs] using h
  have him := Complex.abs_im_le_norm (rho + (2 * Real.pi * η * Complex.I) * t)
  rw [he] at him
  have hmul := mul_le_mul_of_nonneg_left htN (by positivity : 0 ≤ 2 * Real.pi * |η|)
  linarith [abs_nonneg rho.im]

theorem hasDerivAt_near_primitive {t η : ℝ} {rho : ℂ}
    (ht : 0 < t) (hr : rho ≠ 0)
    (hd : rho + (2 * Real.pi * η * Complex.I) * t ≠ 0) :
    HasDerivAt
      (fun x : ℝ => (x : ℂ) ^ rho * charReal (η * x) /
        (rho + (2 * Real.pi * η * Complex.I) * x))
      ((t : ℂ) ^ (rho - 1) * charReal (η * t) -
        (2 * Real.pi * η * Complex.I) * (t : ℂ) ^ rho * charReal (η * t) /
          (rho + (2 * Real.pi * η * Complex.I) * t) ^ 2) t := by
  have hpow := hasDerivAt_ofReal_cpow_const ht.ne' hr
  have hden := ((hasDerivAt_id t).ofReal_comp.const_mul
    (2 * Real.pi * η * Complex.I)).const_add rho
  convert! (hpow.mul (hasDerivAt_charReal_mul η t)).div hden hd using 1
  have hp : (t : ℂ) ^ rho = (t : ℂ) ^ (rho - 1) * t := by
    simpa only [sub_add_cancel, Complex.cpow_one] using
      Complex.cpow_add (rho - 1) 1 (Complex.ofReal_ne_zero.mpr ht.ne')
  simp only [id_eq, Pi.mul_apply, Complex.ofReal_one, mul_one]
  rw [hp]
  field_simp [hd]

theorem norm_integral_cpow_charReal_near {N : ℝ} (hN : 0 < N)
    {rho : ℂ} (hbeta : 0 ≤ rho.re) (hgamma : rho.im ≠ 0) {η : ℝ}
    (hη : |η| ≤ |rho.im| / (10 * Real.pi * N)) :
    ‖∫ t in N / 1000..N, (t : ℂ) ^ (rho - 1) * charReal (η * t)‖ ≤
      5 * N ^ rho.re / |rho.im| := by
  let a := N / 1000
  let c : ℂ := 2 * Real.pi * η * Complex.I
  let G : ℝ := |rho.im|
  let B : ℝ := N ^ rho.re
  let K : ℝ := 2 * Real.pi * |η|
  let H : ℝ → ℂ := fun t => (t : ℂ) ^ rho * charReal (η * t) / (rho + c * t)
  let R : ℝ → ℂ := fun t =>
    c * (t : ℂ) ^ rho * charReal (η * t) / (rho + c * t) ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ N := by dsimp [a]; linarith
  have hG : 0 < G := abs_pos.mpr hgamma
  have hB : 0 < B := Real.rpow_pos_of_pos hN _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKN : K * N ≤ G / 5 := by
    have h := (le_div_iff₀ (by positivity : 0 < 10 * Real.pi * N)).mp hη
    dsimp [K, G]
    nlinarith
  have hD : ∀ t ∈ Set.Icc a N, G / 2 ≤ ‖rho + c * t‖ := by
    intro t ht
    exact near_denominator_lower (ha.trans_le ht.1).le ht.2 hKN
  have hD0 : ∀ t ∈ Set.Icc a N, rho + c * t ≠ 0 := by
    intro t ht
    exact norm_ne_zero_iff.mp (ne_of_gt ((half_pos hG).trans_le (hD t ht)))
  have hr : rho ≠ 0 := by
    intro he
    exact hgamma (by simp [he])
  have hpow : ∀ t ∈ Set.Icc a N, ‖(t : ℂ) ^ rho‖ ≤ B := by
    intro t ht
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le ht.1)]
    exact Real.rpow_le_rpow (ha.trans_le ht.1).le ht.2 hbeta
  have hH : ∀ t ∈ Set.Icc a N, ‖H t‖ ≤ 2 * B / G := by
    intro t ht
    dsimp [H]
    rw [norm_div, norm_mul, norm_charReal_eq_one, mul_one]
    calc
      _ ≤ B / (G / 2) :=
        div_le_div₀ hB.le (hpow t ht) (half_pos hG) (hD t ht)
      _ = 2 * B / G := by ring
  have hR : ∀ t ∈ Set.Icc a N, ‖R t‖ ≤ 4 * K * B / G ^ 2 := by
    intro t ht
    dsimp [R]
    rw [norm_div, norm_mul, norm_mul, norm_charReal_eq_one, mul_one,
      norm_pow, show ‖c‖ = K from norm_frequency η]
    calc
      _ ≤ (K * B) / (G / 2) ^ 2 := by
        apply div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left (hpow t ht) hK) (by positivity)
        exact pow_le_pow_left₀ (by positivity) (hD t ht) 2
      _ = 4 * K * B / G ^ 2 := by ring
  have hRc : ContinuousOn R (Set.Icc a N) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have hp := Complex.continuousAt_ofReal_cpow_const t rho
      (Or.inr (ne_of_gt (ha.trans_le ht.1)))
    exact ((continuousAt_const.mul hp).mul
      (continuous_charReal_mul η).continuousAt).div
      (by fun_prop) (pow_ne_zero _ (hD0 t ht))
  have hRi : IntervalIntegrable R volume a N := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hab] using hRc
  have hKi := intervalIntegrable_cpow_charReal ha hab rho η
  have hFTC :
      (∫ t in a..N, (t : ℂ) ^ (rho - 1) * charReal (η * t)) =
      H N - H a + ∫ t in a..N, R t := by
    have hd : ∀ t ∈ Set.uIcc a N,
        HasDerivAt H ((t : ℂ) ^ (rho - 1) * charReal (η * t) - R t) t := by
      rw [Set.uIcc_of_le hab]
      intro t ht
      exact hasDerivAt_near_primitive (ha.trans_le ht.1) hr (hD0 t ht)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hKi.sub hRi)
    rw [intervalIntegral.integral_sub hKi hRi] at h
    exact sub_eq_iff_eq_add.mp h
  have hRint : ‖∫ t in a..N, R t‖ ≤ 4 * K * B / G ^ 2 * N := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := N) (C := 4 * K * B / G ^ 2) (fun t ht => by
        rw [Set.uIoc_of_le hab] at ht
        exact hR t ⟨ht.1.le, ht.2⟩)
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith : N - a ≤ N)
      (by positivity))
  have hsum : ‖∫ t in a..N, (t : ℂ) ^ (rho - 1) * charReal (η * t)‖ ≤
      4 * B / G + 4 * K * B / G ^ 2 * N := by
    rw [hFTC]
    calc
      _ ≤ ‖H N - H a‖ + ‖∫ t in a..N, R t‖ := norm_add_le _ _
      _ ≤ (‖H N‖ + ‖H a‖) + ‖∫ t in a..N, R t‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (2 * B / G + 2 * B / G) + 4 * K * B / G ^ 2 * N :=
        add_le_add (add_le_add (hH N ⟨hab, le_rfl⟩) (hH a ⟨le_rfl, hab⟩)) hRint
      _ = _ := by ring
  apply hsum.trans
  change 4 * B / G + 4 * K * B / G ^ 2 * N ≤ 5 * B / G
  have hKN' : 4 * (K * N) ≤ G := by linarith
  have hm := mul_le_mul_of_nonneg_right hKN' hB.le
  field_simp
  nlinarith

end LiuWang.Proof.OscillatoryBounds
