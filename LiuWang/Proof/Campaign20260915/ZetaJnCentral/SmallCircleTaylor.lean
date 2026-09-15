import LiuWang.Proof.Campaign20260915.ZetaJnCentral.ExactGaussian

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

def smallCircleMajorant (sigma lambda R : ℝ) : ℝ :=
  Real.exp (|sigma - 1| / 7 + 8 / 21 * lambda ^ 2 * (R / lambda) ^ 3)

theorem smallCircle_weight (sigma : ℝ) {lambda : ℝ} (hl : 0 < lambda)
    {z : ℂ} (hz : ‖z‖ ≤ lambda / 8) :
    ‖rsSaddleWeight sigma lambda z‖ ≤ smallCircleMajorant sigma lambda ‖z‖ := by
  have hu : ‖z / (lambda : ℂ)‖ ≤ 1 / 8 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hl, div_le_iff₀ hl]
    linarith
  have hi : (1 - ‖z / (lambda : ℂ)‖)⁻¹ ≤ 8 / 7 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    linarith
  have hlog : ‖log (1 + z / (lambda : ℂ))‖ ≤ 1 / 7 := by
    have h := norm_log_sub_logTaylor_le 0 (z := z / (lambda : ℂ)) (by linarith)
    norm_num [logTaylor] at h
    have hm := mul_le_mul hu hi (inv_nonneg.mpr (by linarith)) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    simp only [norm_div, norm_real, Real.norm_eq_abs] at hm
    nlinarith
  have ht := norm_log_sub_logTaylor_le 2 (z := z / (lambda : ℂ)) (by linarith)
  have hp : logTaylor 3 (z / (lambda : ℂ)) = z / lambda - (z / lambda) ^ 2 / 2 := by
    norm_num [logTaylor, Finset.sum_range_succ]
    ring
  rw [hp] at ht
  have hr : ‖log (1 + z / lambda) - z / lambda + (z / lambda) ^ 2 / 2‖ ≤
      8 / 21 * ‖z / (lambda : ℂ)‖ ^ 3 := by
    rw [show log (1 + z / lambda) - z / lambda + (z / lambda) ^ 2 / 2 =
      log (1 + z / lambda) - (z / lambda - (z / lambda) ^ 2 / 2) by ring]
    apply ht.trans
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    nlinarith [mul_le_mul_of_nonneg_left hi
      (pow_nonneg (norm_nonneg (z / (lambda : ℂ))) 3)]
  have hm : (((sigma - 1 : ℝ) : ℂ) * log (1 + z / lambda)).re ≤ |sigma - 1| / 7 := by
    apply (re_le_norm _).trans
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hlog (abs_nonneg _)).trans_eq (by ring)
  have hn := re_le_norm (I * (lambda : ℂ) ^ 2 *
    (log (1 + z / lambda) - z / lambda + (z / lambda) ^ 2 / 2))
  rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, norm_real, Real.norm_eq_abs,
    abs_of_pos hl] at hn
  have htail := hn.trans (mul_le_mul_of_nonneg_left hr (sq_nonneg lambda))
  rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hl] at htail
  rw [rsSaddleWeight, norm_exp, smallCircleMajorant, Real.exp_le_exp,
    rsSaddle_exponent_rewrite sigma hl.ne', add_re]
  linarith

theorem smallCircle_coefficient (sigma : ℝ) {lambda R : ℝ}
    (hl : 0 < lambda) (hR0 : 0 < R) (hR : R ≤ lambda / 8) (n : ℕ) :
    ‖rsSaddleCoefficient sigma lambda n‖ ≤ smallCircleMajorant sigma lambda R / R ^ n := by
  have hd := rsSaddle_differentiable_closedBall sigma hl (by linarith : R < lambda)
  have hc := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR0
    (hd.mono Metric.closure_ball_subset_closedBall).diffContOnCl (fun z hz => by
      have he : ‖z‖ = R := by simpa using hz
      simpa only [he] using smallCircle_weight sigma hl (he.le.trans hR))
  rw [rsSaddleCoefficient, norm_div, norm_natCast]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ hf]
  exact hc.trans_eq (by ring)

theorem smallCircle_remainder (sigma : ℝ) {lambda R : ℝ}
    (hl : 0 < lambda) (hR0 : 0 < R) (hR : R ≤ lambda / 8)
    {z : ℂ} (hz : ‖z‖ < R) (N : ℕ) :
    ‖rsSaddleRemainder sigma lambda N z‖ ≤
      smallCircleMajorant sigma lambda R * (‖z‖ / R) ^ N / (1 - ‖z‖ / R) := by
  have hs := rsSaddle_hasSum sigma hl hR0 (by linarith : R < lambda) hz
  have ht := (hasSum_nat_add_iff' N).mpr hs
  have hr0 : 0 ≤ ‖z‖ / R := div_nonneg (norm_nonneg _) hR0.le
  have hr1 : ‖z‖ / R < 1 := (div_lt_one hR0).mpr hz
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (smallCircleMajorant sigma lambda R * (‖z‖ / R) ^ N)
  rw [← div_eq_mul_inv] at hg
  apply ht.norm_le_of_bounded hg
  intro n
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (smallCircleMajorant sigma lambda R / R ^ (n + N)) * ‖z‖ ^ (n + N) :=
      mul_le_mul_of_nonneg_right (smallCircle_coefficient sigma hl hR0 hR _) (by positivity)
    _ = _ := by rw [div_pow, pow_add, pow_add]; ring

theorem smallCircle_remainder_four (sigma : ℝ) {lambda R : ℝ}
    (hl : 0 < lambda) (hR0 : 0 < R) (hR : R ≤ lambda / 8)
    {z : ℂ} (hz : 4 / 3 * ‖z‖ ≤ R) (N : ℕ) :
    ‖rsSaddleRemainder sigma lambda N z‖ ≤
      4 * smallCircleMajorant sigma lambda R * (‖z‖ / R) ^ N := by
  have hr : ‖z‖ / R ≤ 3 / 4 := by
    rw [div_le_iff₀ hR0]
    linarith
  apply (smallCircle_remainder sigma hl hR0 hR (by linarith) N).trans
  rw [div_le_iff₀ (by linarith)]
  have hp : 0 ≤ smallCircleMajorant sigma lambda R * (‖z‖ / R) ^ N := by
    unfold smallCircleMajorant
    positivity
  nlinarith

theorem jn_smallCircle_pointwise (sigma : ℝ) {eta R y : ℝ} {m : ℕ}
    (he : 0 < eta) (hR0 : 0 < R) (hR : R ≤ (rsSaddleScale * eta) / 8)
    (hyR : 4 / 3 * (rsSaddleScale * |y|) ≤ R)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖rsJnIntegrand sigma eta m (N + 1) y‖ ≤
      (4 * smallCircleMajorant sigma (rsSaddleScale * eta) R * (rsSaddleScale / R) ^ (N + 1)) *
        exactGaussianWeight Real.pi N y := by
  by_cases hy : y = 0
  · subst y
    rw [jn_zero, norm_zero]
    unfold smallCircleMajorant exactGaussianWeight
    have := rsSaddleScale_pos
    positivity
  have hz : ‖(rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)‖ = rsSaddleScale * |y| := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos rsSaddleScale_pos, rsDescentPoint_distance]
  have hr := smallCircle_remainder_four sigma (mul_pos rsSaddleScale_pos he) hR0 hR
    (z := (rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)) (by rwa [hz]) (N + 1)
  rw [hz] at hr
  rw [rsJnIntegrand, norm_mul, norm_mul, rsDescentDirection_norm, one_mul]
  apply (mul_le_mul_of_nonneg_left hr (norm_nonneg _)).trans
  have hc : 0 ≤ 4 * smallCircleMajorant sigma (rsSaddleScale * eta) R *
      (rsSaddleScale / R) ^ (N + 1) := by
    unfold smallCircleMajorant
    have := rsSaddleScale_pos
    positivity
  have h := mul_le_mul_of_nonneg_left (gaussian_times_distance eta m hy hm0 hm1)
    (mul_nonneg hc (pow_nonneg (abs_nonneg y) N))
  convert h using 1 <;>
    simp only [exactGaussianWeight, div_pow, mul_pow, pow_succ] <;> ring

theorem jn_smallCircle_integral (sigma : ℝ) {eta R d : ℝ} {m : ℕ}
    (he : 0 < eta) (hR0 : 0 < R) (hR : R ≤ (rsSaddleScale * eta) / 8)
    (hd : 0 ≤ d) (hdR : 4 / 3 * (rsSaddleScale * d) ≤ R)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖∫ y : ℝ in (-d)..d, rsJnIntegrand sigma eta m (N + 1) y‖ ≤
      (4 * smallCircleMajorant sigma (rsSaddleScale * eta) R * (rsSaddleScale / R) ^ (N + 1)) *
        exactGaussianBudget Real.pi N := by
  apply norm_interval_exactGaussian N Real.pi_pos (by linarith)
    (by unfold smallCircleMajorant; have := rsSaddleScale_pos; positivity)
  intro y hy
  have hyd : |y| ≤ d := abs_le.mpr hy
  exact jn_smallCircle_pointwise sigma he hR0 hR
    ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyd rsSaddleScale_pos.le)
      (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans hdR) hm0 hm1 N

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
