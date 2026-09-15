import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SmallCircleTaylor

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem powerGaussian_antitone (n : ℕ) {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d)
    (hn : (n : ℝ) ≤ 2 * c * d ^ 2) :
    AntitoneOn (fun y : ℝ => y ^ n * Real.exp (-c * y ^ 2)) (Ici d) := by
  cases n with
  | zero =>
    intro x hx y hy hxy
    simp only [pow_zero, one_mul, Real.exp_le_exp]
    have hx0 : 0 ≤ x := hd.trans hx
    have hy0 : 0 ≤ y := hd.trans hy
    have hs : x ^ 2 ≤ y ^ 2 := by nlinarith
    exact mul_le_mul_of_nonpos_left hs (neg_nonpos.mpr hc.le)
  | succ n =>
    apply antitoneOn_of_deriv_nonpos (convex_Ici d) (by fun_prop) (by fun_prop)
    intro x hx
    have hxd : d ≤ x := interior_subset hx
    have hx0 : 0 ≤ x := hd.trans hxd
    have hs : d ^ 2 ≤ x ^ 2 := by nlinarith
    have hn' : (n : ℝ) + 1 ≤ 2 * c * x ^ 2 := by
      simp only [Nat.cast_succ] at hn
      nlinarith
    have he : HasDerivAt (fun y : ℝ => Real.exp (-c * y ^ 2))
        ((-c * (2 * x)) * Real.exp (-c * x ^ 2)) x := by
      convert (((hasDerivAt_id x).pow 2).const_mul (-c)).exp using 1 <;> simp
      ring
    have hp := ((hasDerivAt_id x).pow (n + 1)).mul he
    change HasDerivAt (fun y : ℝ => y ^ (n + 1) * Real.exp (-c * y ^ 2))
      ((n + 1 : ℕ) * x ^ (n + 1 - 1) * 1 * Real.exp (-c * x ^ 2) +
        x ^ (n + 1) * ((-c * (2 * x)) * Real.exp (-c * x ^ 2))) x at hp
    rw [hp.deriv]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one]
    have heq : ((n : ℝ) + 1) * x ^ n * Real.exp (-c * x ^ 2) +
        x ^ (n + 1) * ((-c * (2 * x)) * Real.exp (-c * x ^ 2)) =
        (x ^ n * Real.exp (-c * x ^ 2)) * ((n : ℝ) + 1 - 2 * c * x ^ 2) := by
      rw [pow_succ]
      ring
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

theorem powerGaussian_tail_interval (n : ℕ) {c d A : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hAd : d ≤ A) (hn : (n : ℝ) ≤ c * d ^ 2) :
    (∫ y : ℝ in d..A, y ^ n * Real.exp (-c * y ^ 2)) ≤
      d ^ n / (c * d) * Real.exp (-c * d ^ 2) := by
  have ha := powerGaussian_antitone n (by positivity : 0 < c / 2) hd.le (by linarith)
  have hb (y : ℝ) (hy : y ∈ Icc d A) :
      y ^ n * Real.exp (-c * y ^ 2) ≤
        (d ^ n * Real.exp (-(c / 2) * d ^ 2)) * Real.exp (-(c / 2) * y ^ 2) := by
    have h := mul_le_mul_of_nonneg_right (ha (by simp) hy.1 hy.1)
      (Real.exp_pos (-(c / 2) * y ^ 2)).le
    have he : Real.exp (-(c / 2) * y ^ 2) * Real.exp (-(c / 2) * y ^ 2) =
        Real.exp (-c * y ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simpa only [mul_assoc, he] using h
  have h1 : IntervalIntegrable (fun y : ℝ => y ^ n * Real.exp (-c * y ^ 2)) volume d A :=
    (by fun_prop : Continuous (fun y : ℝ => y ^ n * Real.exp (-c * y ^ 2))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun y : ℝ =>
      (d ^ n * Real.exp (-(c / 2) * d ^ 2)) * Real.exp (-(c / 2) * y ^ 2)) volume d A :=
    (by fun_prop : Continuous (fun y : ℝ =>
      (d ^ n * Real.exp (-(c / 2) * d ^ 2)) * Real.exp (-(c / 2) * y ^ 2))).intervalIntegrable _ _
  calc
    _ ≤ ∫ y : ℝ in d..A, (d ^ n * Real.exp (-(c / 2) * d ^ 2)) *
        Real.exp (-(c / 2) * y ^ 2) :=
      intervalIntegral.integral_mono_on hAd h1 h2 hb
    _ = (d ^ n * Real.exp (-(c / 2) * d ^ 2)) *
        ∫ y : ℝ in d..A, Real.exp (-(c / 2) * y ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (d ^ n * Real.exp (-(c / 2) * d ^ 2)) *
        (Real.exp (-(c / 2) * d ^ 2) / (2 * (c / 2) * d)) :=
      mul_le_mul_of_nonneg_left (rsGaussian_tail_interval (by positivity) hd hAd) (by positivity)
    _ = _ := by
      have he : Real.exp (-(c / 2) * d ^ 2) * Real.exp (-(c / 2) * d ^ 2) =
          Real.exp (-c * d ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← he]
      ring

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
