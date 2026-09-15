import LiuWang.Proof.SourceRoute.HighSum.Continuation.LogHeight
import LiuWang.Proof.SourceRoute.HighSum.Continuation.EndpointScalar

/-! # Directed estimates for the exact seven positive lambda integrals -/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment

def sourceIntegrand (L s : ℝ) : ℝ :=
  L ^ (4 : ℕ) * Real.exp (-s) * source31Profile L s

def lambdaKernel (L s lam : ℝ) : ℝ :=
  L ^ (5 : ℕ) / s * Real.exp (-s - lam * L / s)

theorem lambdaKernel_integrable (L s a b : ℝ) :
    IntervalIntegrable (lambdaKernel L s) volume a b := by
  apply Continuous.intervalIntegrable
  unfold lambdaKernel
  fun_prop

theorem normalized_segment_eq (L s a b : ℝ) :
    L ^ (4 : ℕ) * Real.exp (-s) * lambdaSegment L s a b =
      ∫ lam in a..b, lambdaKernel L s lam := by
  unfold lambdaSegment lambdaKernel
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro lam _
  dsimp only
  rw [show -s - lam * L / s = -s + (-lam * L / s) by ring, Real.exp_add]
  ring

theorem sourceIntegrand_eq_segments {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    sourceIntegrand L s =
      35 * (∫ lam in (0.36 : ℝ)..0.39, lambdaKernel L s lam) +
      89 * (∫ lam in (0.39 : ℝ)..0.42, lambdaKernel L s lam) +
      182 * (∫ lam in (0.42 : ℝ)..0.45, lambdaKernel L s lam) +
      292 * (∫ lam in (0.45 : ℝ)..0.46, lambdaKernel L s lam) +
      664 * (∫ lam in (0.46 : ℝ)..0.47, lambdaKernel L s lam) +
      1668 * (∫ lam in (0.47 : ℝ)..0.475, lambdaKernel L s lam) +
      14000 * (∫ lam in (0.475 : ℝ)..0.478, lambdaKernel L s lam) := by
  simp_rw [← normalized_segment_eq]
  unfold sourceIntegrand source31Profile
  rw [← source31_signed_segments hL hs]
  ring

theorem fifth_exp_le {x y c : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hc : 5 ≤ c * x) :
    y ^ (5 : ℕ) * Real.exp (-c * y) ≤ x ^ (5 : ℕ) * Real.exp (-c * x) := by
  have hy : 0 < y := hx.trans_le hxy
  have hr : 1 ≤ y / x := (le_div_iff₀ hx).mpr (by simpa using hxy)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hy hx)
  have he : 5 * Real.log (y / x) - c * y ≤ -c * x := by
    have hh := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hr)
    field_simp at hh hlog ⊢
    nlinarith
  have hh := Real.exp_le_exp.mpr he
  rw [Real.exp_sub, show (5 : ℝ) * Real.log (y / x) =
    (5 : ℕ) * Real.log (y / x) by norm_num,
    Real.exp_nat_mul, Real.exp_log (div_pos hy hx)] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (pow_nonneg hx.le 5)
  rw [show -c * y = -(c * y) by ring, Real.exp_neg]
  calc
    _ = x ^ (5 : ℕ) * ((y / x) ^ (5 : ℕ) / Real.exp (c * y)) := by field_simp
    _ ≤ _ := hh'

theorem lambdaKernel_le_base {L s lam : ℝ} (hL : 3100 ≤ L)
    (hs : 0 < s) (hs' : s ≤ 100) (hlam : 0.36 ≤ lam) :
    lambdaKernel L s lam ≤ lambdaKernel 3100 s lam := by
  have hc : 5 ≤ (lam / s) * 3100 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hs).mpr
    nlinarith
  have h := fifth_exp_le (by norm_num : (0 : ℝ) < 3100) hL hc
  have he (x : ℝ) : lambdaKernel x s lam =
      (Real.exp (-s) / s) * (x ^ (5 : ℕ) * Real.exp (-(lam / s) * x)) := by
    unfold lambdaKernel
    rw [show -s - lam * x / s = -s + (-(lam / s) * x) by ring, Real.exp_add]
    ring
  rw [he, he]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem sourceIntegrand_le_base {L s : ℝ} (hL : 3100 ≤ L)
    (hs : 0 < s) (hs' : s ≤ 100) :
    sourceIntegrand L s ≤ sourceIntegrand 3100 s := by
  have h (a b : ℝ) (ha : 0.36 ≤ a) (hab : a ≤ b) :
      (∫ lam in a..b, lambdaKernel L s lam) ≤
        ∫ lam in a..b, lambdaKernel 3100 s lam :=
    intervalIntegral.integral_mono_on hab (lambdaKernel_integrable _ _ _ _)
      (lambdaKernel_integrable _ _ _ _)
      (fun lam hlam => lambdaKernel_le_base hL hs hs' (ha.trans hlam.1))
  rw [sourceIntegrand_eq_segments (by linarith) hs,
    sourceIntegrand_eq_segments (by norm_num) hs]
  have h1 := h 0.36 0.39 le_rfl (by norm_num)
  have h2 := h 0.39 0.42 (by norm_num) (by norm_num)
  have h3 := h 0.42 0.45 (by norm_num) (by norm_num)
  have h4 := h 0.45 0.46 (by norm_num) (by norm_num)
  have h5 := h 0.46 0.47 (by norm_num) (by norm_num)
  have h6 := h 0.47 0.475 (by norm_num) (by norm_num)
  have h7 := h 0.475 0.478 (by norm_num) (by norm_num)
  linarith

theorem lambdaKernel_le_polynomial {L s lam : ℝ} (hL : 0 ≤ L)
    (hs : 0 < s) (hlam : 0.36 ≤ lam) :
    lambdaKernel L s lam ≤ 20000 * s ^ (4 : ℕ) * Real.exp (-s) := by
  have ha : 0 ≤ (0.36 : ℝ) * L / s := by positivity
  have hp := Real.pow_div_factorial_le_exp ((0.36 : ℝ) * L / s) ha 5
  norm_num only [Nat.factorial, Nat.cast_ofNat] at hp
  have hh := mul_le_mul_of_nonneg_right hp
    (Real.exp_pos (-(0.36 : ℝ) * L / s)).le
  rw [← Real.exp_add] at hh
  have he : (9 / 25 : ℝ) * L / s + -(0.36 : ℝ) * L / s = 0 := by ring
  rw [he, Real.exp_zero] at hh
  have hpow : L ^ (5 : ℕ) * Real.exp (-(0.36 : ℝ) * L / s) ≤
      20000 * s ^ (5 : ℕ) := by
    have hm := mul_le_mul_of_nonneg_right hh (pow_nonneg hs.le 5)
    have hn : 0 ≤ L ^ (5 : ℕ) * Real.exp (-(0.36 : ℝ) * L / s) := by positivity
    field_simp at hm
    rw [show -(L * 0.36 / s) = -(0.36 : ℝ) * L / s by ring] at hm
    nlinarith [pow_nonneg hs.le 5]
  have hex : Real.exp (-lam * L / s) ≤ Real.exp (-(0.36 : ℝ) * L / s) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using div_le_div_of_nonneg_right
      (neg_le_neg (mul_le_mul_of_nonneg_right hlam hL)) hs.le
  unfold lambdaKernel
  rw [show -s - lam * L / s = -s + (-lam * L / s) by ring, Real.exp_add]
  have hp' := (mul_le_mul_of_nonneg_left hex (pow_nonneg hL 5)).trans hpow
  have hm := mul_le_mul_of_nonneg_left hp' (by positivity : 0 ≤ Real.exp (-s) / s)
  calc
    _ = Real.exp (-s) / s * (L ^ (5 : ℕ) * Real.exp (-lam * L / s)) := by ring
    _ ≤ _ := hm
    _ = _ := by field_simp

theorem sourceIntegrand_le_polynomial {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    sourceIntegrand L s ≤ 1400000 * s ^ (4 : ℕ) * Real.exp (-s) := by
  have h (a b : ℝ) (ha : 0.36 ≤ a) (hab : a ≤ b) :
      (∫ lam in a..b, lambdaKernel L s lam) ≤
        (b - a) * (20000 * s ^ (4 : ℕ) * Real.exp (-s)) := by
    have hh := intervalIntegral.integral_mono_on hab (lambdaKernel_integrable _ _ _ _)
      (intervalIntegrable_const) (fun lam hlam =>
        lambdaKernel_le_polynomial hL.le hs (ha.trans hlam.1))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh
  rw [sourceIntegrand_eq_segments hL hs]
  have h1 := h 0.36 0.39 le_rfl (by norm_num)
  have h2 := h 0.39 0.42 (by norm_num) (by norm_num)
  have h3 := h 0.42 0.45 (by norm_num) (by norm_num)
  have h4 := h 0.45 0.46 (by norm_num) (by norm_num)
  have h5 := h 0.46 0.47 (by norm_num) (by norm_num)
  have h6 := h 0.47 0.475 (by norm_num) (by norm_num)
  have h7 := h 0.475 0.478 (by norm_num) (by norm_num)
  have hn : 0 ≤ s ^ (4 : ℕ) * Real.exp (-s) := by positivity
  linarith

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment
