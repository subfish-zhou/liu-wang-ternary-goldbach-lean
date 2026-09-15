import LiuWang.Proof.Campaign20260915.RSMertensTransport.LogSeries

set_option autoImplicit false
noncomputable section

open AnalyticNumberTheory.Mertens
open MeasureTheory

namespace LiuWang.Proof.Campaign20260915.RSMertensTransport

private theorem theta_sum (t : ℝ) :
    (∑ p ∈ Finset.Icc 0 ⌊t⌋₊, if p.Prime then Real.log p else 0) =
      Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]

private theorem hasDerivAt_inv_sq {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ => 1 / u ^ 2) (-2 / t ^ 3) t := by
  apply ((hasDerivAt_const t (1 : ℝ)).div
    ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht)).congr_deriv
  simp only [id_eq, Pi.pow_apply]
  field_simp
  ring

theorem prime_log_square_window_eq {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
      if p.Prime then Real.log p / (p : ℝ) ^ 2 else 0) =
      Chebyshev.theta y / y ^ 2 - Chebyshev.theta x / x ^ 2 +
        ∫ t in Set.Ioc x y, 2 * Chebyshev.theta t / t ^ 3 := by
  let c : ℕ → ℝ := fun p => if p.Prime then Real.log p else 0
  have hd (t : ℝ) (ht : t ∈ Set.Icc x y) :=
    hasDerivAt_inv_sq (ne_of_gt (hx.trans_le ht.1))
  have hc : ContinuousOn (fun t : ℝ => -2 / t ^ 3) (Set.Icc x y) :=
    continuousOn_const.div (continuousOn_id.pow 3)
      (fun t ht => pow_ne_zero 3 (ne_of_gt (hx.trans_le ht.1)))
  have hderiv : Set.EqOn (deriv (fun t : ℝ => 1 / t ^ 2))
      (fun t => -2 / t ^ 3) (Set.Icc x y) := fun t ht => (hd t ht).deriv
  have hint : IntegrableOn (deriv (fun t : ℝ => 1 / t ^ 2)) (Set.Icc x y) :=
    (hc.integrableOn_Icc).congr_fun (fun t ht => (hderiv ht).symm) measurableSet_Icc
  have hs := sum_mul_eq_sub_sub_integral_mul c hx.le hxy
    (fun t ht => (hd t ht).differentiableAt) hint
  have hsum :
      (∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, 1 / (p : ℝ) ^ 2 * c p) =
        ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
          if p.Prime then Real.log p / (p : ℝ) ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [c]
    split_ifs <;> ring
  have hi :
      (∫ t in Set.Ioc x y, deriv (fun u : ℝ => 1 / u ^ 2) t *
        ∑ p ∈ Finset.Icc 0 ⌊t⌋₊, c p) =
      -(∫ t in Set.Ioc x y, 2 * Chebyshev.theta t / t ^ 3) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv]
    dsimp [c]
    rw [theta_sum]
    ring
  rw [hsum, hi] at hs
  simp only [c, theta_sum] at hs
  convert hs using 1
  ring

theorem prime_log_square_window_le {x y C : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hC : 0 ≤ C) (htheta : ∀ t ∈ Set.Icc x y, Chebyshev.theta t ≤ C * t) :
    (∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
      if p.Prime then Real.log p / (p : ℝ) ^ 2 else 0) ≤ 2 * C / x := by
  have hy : 0 < y := hx.trans_le hxy
  have hcont : ContinuousOn (fun t : ℝ => 2 / t ^ 3) (Set.Icc x y) :=
    continuousOn_const.div (continuousOn_id.pow 3)
      (fun t ht => pow_ne_zero 3 (ne_of_gt (hx.trans_le ht.1)))
  have hcont' : ContinuousOn (fun t : ℝ => 2 * C / t ^ 2) (Set.Icc x y) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt (hx.trans_le ht.1)))
  have hweighted := integrableOn_mul_sum_Icc (m := 0)
    (fun p : ℕ => if p.Prime then Real.log p else 0) hx.le hcont.integrableOn_Icc
  have hi : IntegrableOn (fun t : ℝ => 2 * Chebyshev.theta t / t ^ 3)
      (Set.Ioc x y) := by
    apply (hweighted.mono_set Set.Ioc_subset_Icc_self).congr_fun
      (fun t ht => ?_) measurableSet_Ioc
    rw [theta_sum]
    ring
  have hi' : IntegrableOn (fun t : ℝ => 2 * C / t ^ 2) (Set.Ioc x y) :=
    hcont'.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hbound : (∫ t in Set.Ioc x y, 2 * Chebyshev.theta t / t ^ 3) ≤
      ∫ t in Set.Ioc x y, 2 * C / t ^ 2 := by
    apply setIntegral_mono_on hi hi' measurableSet_Ioc
    intro t ht
    have ht0 := hx.trans ht.1
    calc
      2 * Chebyshev.theta t / t ^ 3 ≤ 2 * (C * t) / t ^ 3 := by
        gcongr
        exact htheta t ⟨ht.1.le, ht.2⟩
      _ = 2 * C / t ^ 2 := by field_simp
  have heval : (∫ t in Set.Ioc x y, 2 * C / t ^ 2) =
      2 * C / x - 2 * C / y := by
    rw [← intervalIntegral.integral_of_le hxy]
    have hd (t : ℝ) (ht : t ∈ Set.uIcc x y) :
        HasDerivAt (fun u : ℝ => -(2 * C) / u) (2 * C / t ^ 2) t := by
      rw [Set.uIcc_of_le hxy] at ht
      have ht0 : t ≠ 0 := ne_of_gt (hx.trans_le ht.1)
      apply ((hasDerivAt_const t (-(2 * C))).div (hasDerivAt_id t) ht0).congr_deriv
      simp only [id_eq]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (by simpa only [Set.uIcc_of_le hxy] using
        (show ContinuousOn (fun t : ℝ => 2 * C / t ^ 2) (Set.uIcc x y) from
          by rwa [Set.uIcc_of_le hxy]).intervalIntegrable)]
    ring
  have hend : Chebyshev.theta y / y ^ 2 ≤ C / y := by
    calc
      _ ≤ (C * y) / y ^ 2 := by
        gcongr
        exact htheta y ⟨hxy, le_rfl⟩
      _ = C / y := by field_simp
  have hstart : 0 ≤ Chebyshev.theta x / x ^ 2 := by positivity
  have hCy : 0 ≤ C / y := by positivity
  rw [prime_log_square_window_eq hx hxy]
  rw [heval] at hbound
  simp only [mul_div_assoc] at hbound ⊢
  linarith

#print axioms prime_log_square_window_eq
#print axioms prime_log_square_window_le

end LiuWang.Proof.Campaign20260915.RSMertensTransport
