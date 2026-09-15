import LiuWang.Proof.Campaign20260915.Density.HorizontalEnvelope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.Campaign20260915.Density

theorem source_density_scale_decay (q : ℕ) [NeZero q] {y a b : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (hab : a ≤ b) :
    chenDensityScale q y b ≤ chenDensityScale q y a *
      Real.exp (-2 * Real.log ((q : ℝ) * y) * (b - a)) := by
  have hm := mul_le_mul_of_nonneg_left (source_density_log_bounds q hy).1
    (sub_nonneg.mpr hab)
  apply (Real.log_le_log_iff (source_density_scale_pos q hy b)
    (mul_pos (source_density_scale_pos q hy a) (Real.exp_pos _))).mp
  rw [Real.log_mul (source_density_scale_pos q hy a).ne' (Real.exp_ne_zero _),
    Real.log_exp, source_density_scale_log q hy a, source_density_scale_log q hy b]
  nlinarith only [hm]

theorem source_density_scale_left_shift (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (alpha : ℝ) :
    chenDensityScale q y (alpha - 3 * sourceDelta ((q : ℝ) * y) / 2) ≤
      Real.exp 4 * chenDensityScale q y alpha := by
  have hd := (source_product_shift_bounds q hy).1
  have hL := source_product_log_ge_eleven q hy
  have hlogL : 0 ≤ Real.log (Real.log ((q : ℝ) * y)) := Real.log_nonneg (by linarith)
  have hm := mul_le_mul_of_nonneg_left (source_density_log_bounds q hy).2
    (show 0 ≤ 3 * sourceDelta ((q : ℝ) * y) / 2 by positivity)
  have hp := mul_nonneg hd.le hlogL
  have hs := source_shift_log q hy
  apply (Real.log_le_log_iff (source_density_scale_pos q hy _)
    (mul_pos (Real.exp_pos _) (source_density_scale_pos q hy alpha))).mp
  rw [Real.log_mul (Real.exp_ne_zero _) (source_density_scale_pos q hy alpha).ne',
    Real.log_exp, source_density_scale_log q hy _, source_density_scale_log q hy alpha]
  nlinarith only [hm, hp, hs]

theorem horizontalEnvelope_eq_density (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (sigma : ℝ) :
    horizontalEnvelope q y sigma =
      47.202 * chenDensityScale q y sigma / Real.log ((q : ℝ) * y) ^ (2 : ℕ) +
        200 * Real.log ((q : ℝ) * y) ^ (4 : ℕ) * ((q : ℝ) * y) ^ (2 * (1 - sigma)) := by
  have hL0 : 0 < Real.log ((q : ℝ) * y) := by linarith [source_product_log_ge_eleven q hy]
  unfold horizontalEnvelope chenDensityScale
  rw [Real.rpow_sub hL0, Real.rpow_two]
  ring

theorem horizontalEnvelope_continuous (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    Continuous (horizontalEnvelope q y) := by
  have hy0 : 0 < y := by linarith [source_height_ge_ten_thousand hy]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hL0 : 0 < Real.log ((q : ℝ) * y) := by linarith [source_product_log_ge_eleven q hy]
  unfold horizontalEnvelope
  fun_prop (disch := positivity)

theorem horizontalEnvelope_decay (q : ℕ) [NeZero q] {y a b : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (hab : a ≤ b) :
    horizontalEnvelope q y b ≤ horizontalEnvelope q y a *
      Real.exp (-2 * Real.log ((q : ℝ) * y) * (b - a)) := by
  have hy0 : 0 < y := by linarith [source_height_ge_ten_thousand hy]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX0 : 0 < (q : ℝ) * y := by positivity
  have he : ((q : ℝ) * y) ^ (2 * (1 - b)) =
      ((q : ℝ) * y) ^ (2 * (1 - a)) *
        Real.exp (-2 * Real.log ((q : ℝ) * y) * (b - a)) := by
    rw [Real.rpow_def_of_pos hX0, Real.rpow_def_of_pos hX0, ← Real.exp_add]
    congr 1
    ring
  have hd := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (source_density_scale_decay q hy hab) (by norm_num : (0 : ℝ) ≤ 47.202))
    (sq_nonneg (Real.log ((q : ℝ) * y)))
  rw [horizontalEnvelope_eq_density q hy b, horizontalEnvelope_eq_density q hy a, he]
  simp only [div_eq_mul_inv] at hd ⊢
  nlinarith only [hd]

theorem source_horizontalEnvelope_start (q : ℕ) [NeZero q] {y a : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : a + sourceDelta ((q : ℝ) * y) ≤ 1) :
    horizontalEnvelope q y (a - sourceDelta ((q : ℝ) * y) / 2) ≤
      6000 * chenDensityScale q y (a + sourceDelta ((q : ℝ) * y)) /
        Real.log ((q : ℝ) * y) ^ (2 : ℕ) := by
  let X : ℝ := (q : ℝ) * y
  let L : ℝ := Real.log X
  let d : ℝ := sourceDelta X
  let alpha : ℝ := a + d
  let sigma : ℝ := a - d / 2
  have hy0 : 0 < y := by linarith [source_height_ge_ten_thousand hy]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX0 : 0 < X := by dsimp [X]; positivity
  have hL0 : 0 < L := by dsimp [L, X]; linarith [source_product_log_ge_eleven q hy]
  have hs : sigma = alpha - 3 * d / 2 := by dsimp [sigma, alpha]; ring
  have hshift : chenDensityScale q y sigma ≤ Real.exp 4 * chenDensityScale q y alpha := by
    rw [hs]
    exact source_density_scale_left_shift q hy alpha
  have he : X ^ (2 * (1 - sigma)) = X ^ (2 * (1 - alpha)) * Real.exp 2 := by
    rw [Real.rpow_def_of_pos hX0, Real.rpow_def_of_pos hX0, ← Real.exp_add]
    congr 1
    have hh := source_shift_log q hy
    change d * L = 2 / 3 at hh
    change L * (2 * (1 - sigma)) = L * (2 * (1 - alpha)) + 2
    dsimp [sigma, alpha]
    nlinarith only [hh]
  have hm := mul_le_mul_of_nonneg_left hshift (by norm_num : (0 : ℝ) ≤ 47.202)
  have hr := mul_le_mul_of_nonneg_left (source_density_scale_ge_right q hy ha)
    (show 0 ≤ 200 * Real.exp 2 by positivity)
  have h4 : Real.exp 4 ≤ 81 := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    exact h
  have h2 : Real.exp 2 ≤ 9 := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 2
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    exact h
  have hc := mul_le_mul_of_nonneg_right
    (show 47.202 * Real.exp 4 + 200 * Real.exp 2 ≤ 6000 by linarith)
    (source_density_scale_pos q hy alpha).le
  have hmul : horizontalEnvelope q y sigma * L ^ (2 : ℕ) =
      47.202 * chenDensityScale q y sigma + 200 * L ^ (6 : ℕ) * X ^ (2 * (1 - sigma)) := by
    rw [horizontalEnvelope_eq_density q hy sigma]
    change (47.202 * chenDensityScale q y sigma / L ^ (2 : ℕ) +
      200 * L ^ (4 : ℕ) * X ^ (2 * (1 - sigma))) * L ^ (2 : ℕ) = _
    field_simp
  change horizontalEnvelope q y sigma ≤ 6000 * chenDensityScale q y alpha / L ^ (2 : ℕ)
  apply (le_div_iff₀ (sq_pos_of_pos hL0)).mpr
  rw [hmul, he]
  change 200 * Real.exp 2 * (X ^ (2 * (1 - alpha)) * L ^ (6 : ℕ)) ≤
    200 * Real.exp 2 * chenDensityScale q y alpha at hr
  nlinarith only [hm, hr, hc]

theorem integral_decay_kernel_le {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    (∫ x in a..b, Real.exp (-c * (x - a))) ≤ 1 / c := by
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => Real.exp (-c * x)) a,
    intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hc.ne'),
    integral_exp]
  simp only [sub_self, mul_zero, Real.exp_zero, smul_eq_mul]
  calc
    _ = (1 - Real.exp (-c * (b - a))) / c := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) hc.le

theorem source_horizontalEnvelope_integral (q : ℕ) [NeZero q] {y a : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha2 : a ≤ 2) (ha : a + sourceDelta ((q : ℝ) * y) ≤ 1) :
    (∫ x in a..2, horizontalEnvelope q y (x - sourceDelta ((q : ℝ) * y) / 2)) ≤
      3000 * chenDensityScale q y (a + sourceDelta ((q : ℝ) * y)) /
        Real.log ((q : ℝ) * y) ^ (3 : ℕ) := by
  let L : ℝ := Real.log ((q : ℝ) * y)
  let d : ℝ := sourceDelta ((q : ℝ) * y)
  let C : ℝ := horizontalEnvelope q y (a - d / 2)
  have hL0 : 0 < L := by dsimp [L]; linarith [source_product_log_ge_eleven q hy]
  have hC : 0 ≤ C := horizontalEnvelope_nonneg q hy _
  have hf : Continuous (fun x : ℝ => horizontalEnvelope q y (x - d / 2)) :=
    (horizontalEnvelope_continuous q hy).comp (continuous_id.sub continuous_const)
  have hg : Continuous (fun x : ℝ => C * Real.exp (-2 * L * (x - a))) := by fun_prop
  have hfi : IntervalIntegrable (fun x : ℝ => horizontalEnvelope q y (x - d / 2)) volume a 2 :=
    hf.intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun x : ℝ => C * Real.exp (-2 * L * (x - a))) volume a 2 :=
    hg.intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on ha2 hfi hgi (fun x hx => by
      have hh := horizontalEnvelope_decay q hy (show a - d / 2 ≤ x - d / 2 by linarith [hx.1])
      simpa only [show (x - d / 2) - (a - d / 2) = x - a by ring] using hh)
  rw [intervalIntegral.integral_const_mul] at h
  have hi := mul_le_mul_of_nonneg_left
    (integral_decay_kernel_le (show 0 < 2 * L by positivity) a 2) hC
  have hs := div_le_div_of_nonneg_right (source_horizontalEnvelope_start q hy ha)
    (show 0 ≤ 2 * L by positivity)
  have he : (6000 * chenDensityScale q y (a + d) / L ^ (2 : ℕ)) / (2 * L) =
      3000 * chenDensityScale q y (a + d) / L ^ (3 : ℕ) := by field_simp; ring
  change C / (2 * L) ≤ _ at hs
  rw [he] at hs
  simp only [neg_mul, mul_one_div] at hi h
  change _ ≤ 3000 * chenDensityScale q y (a + d) / L ^ (3 : ℕ)
  nlinarith only [h, hi, hs]

end LiuWang.Proof.Campaign20260915.Density
