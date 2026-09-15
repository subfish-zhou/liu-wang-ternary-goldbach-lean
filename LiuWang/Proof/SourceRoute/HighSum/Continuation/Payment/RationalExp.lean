import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Quadrature

/-! # Fixed, directed rational exponential enclosures (no floating arithmetic) -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment

def expTaylor (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 20, x ^ k / (k.factorial : ℝ)

def expNegUpper (x : ℝ) : ℝ := 1 / (expTaylor (x / 128)) ^ (128 : ℕ)

def expNegLower (x : ℝ) : ℝ :=
  1 / (expTaylor (x / 128) + 1 / 1000000000000000000) ^ (128 : ℕ)

theorem expTaylor_bounds {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    1 ≤ expTaylor x ∧ expTaylor x ≤ Real.exp x ∧
      Real.exp x ≤ expTaylor x + 1 / 1000000000000000000 := by
  have h1 : 1 ≤ expTaylor x := by
    have hh := Finset.single_le_sum (f := fun k : ℕ => x ^ k / (k.factorial : ℝ))
      (fun k _ => by positivity) (by decide : 0 ∈ Finset.range 20)
    simpa only [expTaylor, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] using hh
  have h2 := Real.sum_le_exp_of_nonneg hx 20
  have h3 := Real.exp_bound' hx hx' (n := 20) (by norm_num)
  have hpow : x ^ (20 : ℕ) ≤ 1 := pow_le_one₀ hx hx'
  have hrem : x ^ (20 : ℕ) * (20 + 1 : ℝ) /
      ((20 : ℕ).factorial * 20) ≤ 1 / 1000000000000000000 := by
    calc
      _ ≤ 1 * (20 + 1 : ℝ) / ((20 : ℕ).factorial * 20) := by gcongr
      _ ≤ _ := by norm_num
  exact ⟨h1, h2, h3.trans (add_le_add_right hrem _)⟩

theorem expNeg_bounds {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 128) :
    expNegLower x ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ expNegUpper x := by
  have ht := expTaylor_bounds (x := x / 128) (by positivity) (by linarith)
  have he : (Real.exp (x / 128)) ^ (128 : ℕ) = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hu := pow_le_pow_left₀ (by linarith : 0 ≤ expTaylor (x / 128)) ht.2.1 128
  have hl := pow_le_pow_left₀ (Real.exp_pos _).le ht.2.2 128
  rw [he] at hu hl
  rw [expNegLower, expNegUpper, Real.exp_neg, ← one_div]
  constructor
  · exact one_div_le_one_div_of_le (Real.exp_pos x) hl
  · exact one_div_le_one_div_of_le (pow_pos (by linarith : 0 < expTaylor (x / 128)) _) hu

theorem rational_lowerHeight : (25329 / 1000 : ℝ) ≤ lowerHeight 3100 := by
  apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3.36 * 3100 ^ (3 : ℕ))).mpr
  have ht := Real.exp_bound' (x := (329 / 1000 : ℝ)) (by norm_num) (by norm_num)
    (n := 6) (by norm_num)
  have he : Real.exp (329 / 1000 : ℝ) ≤ 1.3896 := by
    norm_num [Finset.sum_range_succ] at ht
    linarith
  have hpow := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 25
  rw [← Real.exp_nat_mul] at hpow
  norm_num only [Nat.cast_ofNat, mul_one] at hpow
  have hh := mul_le_mul hpow he (Real.exp_pos _).le (by positivity)
  rw [← Real.exp_add] at hh
  norm_num at hh
  linarith

theorem base_core_le_rational_interval :
    (∫ s in lowerHeight 3100..(100 : ℝ), sourceIntegrand 3100 s) ≤
      ∫ s in (25329 / 1000 : ℝ)..100, sourceIntegrand 3100 s := by
  have hb := original_height_bounds (L := 3100) le_rfl
  exact intervalIntegral.integral_mono_interval rational_lowerHeight hb.2.1 le_rfl
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs =>
      sourceIntegrand_nonneg (by norm_num) (by linarith [hs.1])))
    (sourceIntegrand_integrable _ (by norm_num) (by norm_num))

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment
