import LiuWang.Proof.Campaign20260915.ZetaValidation.RiemannSiegelSaddleRecurrence

set_option autoImplicit false
noncomputable section
open Complex Metric

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rsSaddle_log_re_bound {u : ℂ} (hu : ‖u‖ ≤ 3 / 5) :
    |(log (1 + u)).re| ≤ Real.log (5 / 2) := by
  have hlow : 1 - ‖u‖ ≤ ‖1 + u‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) (-u)
  have hhigh : ‖1 + u‖ ≤ 1 + ‖u‖ := by simpa using norm_add_le (1 : ℂ) u
  have hl : 2 / 5 ≤ ‖1 + u‖ := by linarith
  have hh : ‖1 + u‖ ≤ 5 / 2 := by linarith
  rw [log_re, abs_le]
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 2 / 5) hl
  have hhi := Real.log_le_log (by linarith : 0 < ‖1 + u‖) hh
  have he : Real.log (2 / 5) = -Real.log (5 / 2) := by
    rw [show (2 / 5 : ℝ) = (5 / 2)⁻¹ by norm_num, Real.log_inv]
  exact ⟨he ▸ hlo, hhi⟩

def rsSourceMajorant (sigma lambda R : ℝ) : ℝ :=
  Real.exp (|sigma - 1| * Real.log (5 / 2) + 5 / 6 * lambda ^ 2 * (R / lambda) ^ 3)

theorem rsSaddle_source_weight_bound (sigma : ℝ) {lambda : ℝ} (hl : 0 < lambda)
    {z : ℂ} (hz : ‖z‖ ≤ 3 / 5 * lambda) :
    ‖rsSaddleWeight sigma lambda z‖ ≤ rsSourceMajorant sigma lambda ‖z‖ := by
  have hu : ‖z / (lambda : ℂ)‖ ≤ 3 / 5 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hl, div_le_iff₀ hl]
    exact hz
  have ht := norm_log_sub_logTaylor_le 2 (z := z / (lambda : ℂ)) (by linarith)
  have hp : logTaylor 3 (z / (lambda : ℂ)) = z / lambda - (z / lambda) ^ 2 / 2 := by
    norm_num [logTaylor, Finset.sum_range_succ]
    ring
  rw [hp] at ht
  have hr : ‖log (1 + z / (lambda : ℂ)) - z / lambda + (z / lambda) ^ 2 / 2‖ ≤
      5 / 6 * ‖z / (lambda : ℂ)‖ ^ 3 := by
    rw [show log (1 + z / (lambda : ℂ)) - z / lambda + (z / lambda) ^ 2 / 2 =
      log (1 + z / lambda) - (z / lambda - (z / lambda) ^ 2 / 2) by ring]
    apply ht.trans
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    have hi : (1 - ‖z / (lambda : ℂ)‖)⁻¹ ≤ 5 / 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hi (pow_nonneg (norm_nonneg (z / (lambda : ℂ))) 3)]
  have hmain :
      (((sigma - 1 : ℝ) : ℂ) * log (1 + z / lambda)).re ≤
        |sigma - 1| * Real.log (5 / 2) := by
    rw [re_ofReal_mul]
    exact (le_abs_self _).trans
      ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left (rsSaddle_log_re_bound hu) (abs_nonneg _)))
  have hnorm := re_le_norm (I * (lambda : ℂ) ^ 2 *
    (log (1 + z / lambda) - z / lambda + (z / lambda) ^ 2 / 2))
  rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, norm_real,
    Real.norm_eq_abs, abs_of_pos hl] at hnorm
  have htail := hnorm.trans (mul_le_mul_of_nonneg_left hr (sq_nonneg lambda))
  rw [rsSaddleWeight, norm_exp, rsSourceMajorant, Real.exp_le_exp,
    rsSaddle_exponent_rewrite sigma hl.ne', add_re]
  rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hl] at htail
  linarith

theorem rsSaddle_source_coefficient_bound (sigma : ℝ) {lambda R : ℝ}
    (hl : 0 < lambda) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * lambda) (n : ℕ) :
    ‖rsSaddleCoefficient sigma lambda n‖ ≤ rsSourceMajorant sigma lambda R / R ^ n := by
  have hd := rsSaddle_differentiable_closedBall sigma hl (by linarith : R < lambda)
  have hc := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR0
    (hd.mono closure_ball_subset_closedBall).diffContOnCl (fun z hz => by
      have he : ‖z‖ = R := by simpa using hz
      simpa only [he] using rsSaddle_source_weight_bound sigma hl (he.le.trans hR))
  rw [rsSaddleCoefficient, norm_div, norm_natCast]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ hf]
  exact hc.trans_eq (by ring)

theorem rsSaddle_source_taylor_remainder (sigma : ℝ) {lambda R : ℝ}
    (hl : 0 < lambda) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * lambda)
    {z : ℂ} (hz : ‖z‖ < R) (N : ℕ) :
    ‖rsSaddleWeight sigma lambda z -
      ∑ n ∈ Finset.range N, rsSaddleCoefficient sigma lambda n * z ^ n‖ ≤
        rsSourceMajorant sigma lambda R * (‖z‖ / R) ^ N / (1 - ‖z‖ / R) := by
  have hs := rsSaddle_hasSum sigma hl hR0 (by linarith : R < lambda) hz
  have ht := (hasSum_nat_add_iff' N).mpr hs
  have hr0 : 0 ≤ ‖z‖ / R := div_nonneg (norm_nonneg _) hR0.le
  have hr1 : ‖z‖ / R < 1 := (div_lt_one hR0).mpr hz
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (rsSourceMajorant sigma lambda R * (‖z‖ / R) ^ N)
  rw [← div_eq_mul_inv] at hg
  apply ht.norm_le_of_bounded hg
  intro n
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (rsSourceMajorant sigma lambda R / R ^ (n + N)) * ‖z‖ ^ (n + N) :=
      mul_le_mul_of_nonneg_right (rsSaddle_source_coefficient_bound sigma hl hR0 hR _) (by positivity)
    _ = _ := by rw [div_pow, pow_add, pow_add]; ring

theorem rsSaddle_source_remainder_twenty_one (sigma : ℝ) {lambda R : ℝ}
    (hl : 0 < lambda) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * lambda)
    {z : ℂ} (hz : 21 / 20 * ‖z‖ ≤ R) (N : ℕ) :
    ‖rsSaddleWeight sigma lambda z -
      ∑ n ∈ Finset.range N, rsSaddleCoefficient sigma lambda n * z ^ n‖ ≤
        21 * rsSourceMajorant sigma lambda R * (‖z‖ / R) ^ N := by
  have hr : ‖z‖ / R ≤ 20 / 21 := by
    rw [div_le_iff₀ hR0]
    linarith
  have h := rsSaddle_source_taylor_remainder sigma hl hR0 hR (by linarith) N
  apply h.trans
  rw [div_le_iff₀ (by linarith)]
  have hp : 0 ≤ rsSourceMajorant sigma lambda R * (‖z‖ / R) ^ N := by
    unfold rsSourceMajorant
    positivity
  nlinarith

theorem siegel_asymptotic_cutoff_unavailable {t : ℝ} (ht : t ≤ 1894438)
    {n : ℕ} (hn : 1 ≤ n) : ¬((n : ℝ) ≤ 2 / 100000000 * t) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  intro h
  linarith

end LiuWang.Proof.Campaign20260915.ZetaValidation
