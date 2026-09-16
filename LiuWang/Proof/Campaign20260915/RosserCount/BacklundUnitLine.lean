import LiuWang.Proof.Campaign20260915.RosserCount.BacklundFiftyPhiBottom

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_unit_em_bound {s : ℂ} (hs : s.re = 1) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 6 ≤ N) :
    ‖riemannZeta s‖ ≤ Real.log N + 2 / 3 + 1 / (2 * (N : ℝ)) +
      1 / ‖s - 1‖ + ‖s‖ / (12 * (N : ℝ) ^ 2) +
      (‖s‖ + 2) ^ 3 / (720 * (N : ℝ) ^ 4) +
      (‖s‖ + 3) ^ 4 / (2880 * (N : ℝ) ^ 4) := by
  have hNp : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
  have hnorm (z : ℂ) : ‖(N : ℂ) ^ z‖ = (N : ℝ) ^ z.re :=
    Complex.norm_natCast_cpow_of_pos hNp z
  have hb4 : bernoulli 4 = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]
  have he : eulerMaclaurinApprox s N 3 = abelApprox s N +
      s * (1 / 12 : ℂ) * (N : ℂ) ^ (-s - 1) +
      risingProduct s 3 * (-1 / 720 : ℂ) * (N : ℂ) ^ (-s - 3) := by
    norm_num [eulerMaclaurinApprox, normalizedBernoulli_zero, hb4,
      risingProduct, Finset.prod_range_succ]
  have hsum := (backlund_partial_sum_norm hs.ge N).trans
    (Totient.harmonic_le_log_add_two_thirds hN)
  have ha : ‖abelApprox s N‖ ≤ Real.log N + 2 / 3 +
      1 / ‖s - 1‖ + 1 / (2 * (N : ℝ)) := by
    have h1 := norm_add_le (zetaPartialSum s N) ((N : ℂ) ^ (1 - s) / (s - 1))
    have h2 := norm_sub_le (zetaPartialSum s N + (N : ℂ) ^ (1 - s) / (s - 1))
      ((N : ℂ) ^ (-s) / 2)
    norm_num only [norm_div, hnorm, sub_re, one_re, neg_re, hs, sub_self, Real.rpow_zero,
      Real.rpow_neg_one, norm_ofNat] at h1 h2
    change ‖zetaPartialSum s N + (N : ℂ) ^ (1 - s) / (s - 1) -
      (N : ℂ) ^ (-s) / 2‖ ≤ _
    have hinv : (N : ℝ)⁻¹ / 2 = 1 / (2 * (N : ℝ)) := by ring
    rw [hinv] at h2
    linarith
  have h1 : ‖s * (1 / 12 : ℂ) * (N : ℂ) ^ (-s - 1)‖ =
      ‖s‖ / (12 * (N : ℝ) ^ 2) := by
    rw [norm_mul, norm_mul, hnorm]
    norm_num [hs, Real.rpow_neg hNR.le, Real.rpow_two]
    ring
  have h3 : ‖risingProduct s 3 * (-1 / 720 : ℂ) * (N : ℂ) ^ (-s - 3)‖ ≤
      (‖s‖ + 2) ^ 3 / (720 * (N : ℝ) ^ 4) := by
    rw [norm_mul, norm_mul, hnorm]
    norm_num only [norm_div, norm_neg, norm_one, norm_ofNat, sub_re, neg_re, hs]
    change ‖risingProduct s 3‖ * (1 / 720) * (N : ℝ) ^ (-1 - 3) ≤ _
    rw [show (-1 - 3 : ℝ) = -(4 : ℝ) by norm_num, Real.rpow_neg hNR.le,
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (norm_risingProduct_le s 2) (by norm_num : (0 : ℝ) ≤ 1 / 720))
      (by positivity : (0 : ℝ) ≤ ((N : ℝ) ^ 4)⁻¹)
    exact h.trans_eq (by norm_num; ring)
  have herr : ‖riemannZeta s - eulerMaclaurinApprox s N 3‖ ≤
      (‖s‖ + 3) ^ 4 / (2880 * (N : ℝ) ^ 4) := by
    rw [zeta_sub_eulerMaclaurinApprox 3 (by rw [hs]; norm_num) hs1 (by omega),
      norm_mul, norm_neg]
    have hb := backlund_bernoulli_four_tail (s := s) (by rw [hs]; norm_num) hNR
    rw [hs] at hb
    norm_num only [show (-1 - 3 : ℝ) = -(4 : ℝ) by norm_num,
      Real.rpow_neg hNR.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] at hb
    have h := mul_le_mul (norm_risingProduct_le s 3) hb (norm_nonneg _) (by positivity)
    exact h.trans_eq (by norm_num; ring)
  have hb := norm_add_le (abelApprox s N) (s * (1 / 12 : ℂ) * (N : ℂ) ^ (-s - 1))
  have hc := norm_add_le
    (abelApprox s N + s * (1 / 12 : ℂ) * (N : ℂ) ^ (-s - 1))
    (risingProduct s 3 * (-1 / 720 : ℂ) * (N : ℂ) ^ (-s - 3))
  rw [← he] at hc
  have hz := norm_add_le (riemannZeta s - eulerMaclaurinApprox s N 3) (eulerMaclaurinApprox s N 3)
  rw [sub_add_cancel] at hz
  linarith

theorem backlund_zeta_unit_line {s : ℂ} (hs : s.re = 1) (ht : 50 ≤ |s.im|) :
    ‖riemannZeta s‖ < Real.log |s.im| - 1 / 10 := by
  let t := |s.im|
  let N : ℕ := ⌊t / 3⌋₊ + 1
  have ht50 : 50 ≤ t := ht
  have ht0 : 0 < t := by linarith
  have hNlo : t / 3 ≤ (N : ℝ) := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (t / 3)).le
  have hNhi : (N : ℝ) ≤ t / 3 + 1 := by
    dsimp [N]
    push_cast
    linarith [Nat.floor_le (by positivity : 0 ≤ t / 3)]
  have hN6 : 6 ≤ N := by
    have h : (6 : ℝ) ≤ N := by linarith
    exact_mod_cast h
  have hN0 : (0 : ℝ) < N := by linarith
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at ht
  have hnorm : ‖s‖ + 3 ≤ 6 * t / 5 := by
    have h := norm_le_abs_re_add_abs_im s
    rw [hs] at h
    norm_num only [abs_one] at h
    change ‖s‖ ≤ 1 + t at h
    linarith
  have hpole : t ≤ ‖s - 1‖ := by simpa [t] using abs_im_le_norm (s - 1)
  have hlog : Real.log N ≤ Real.log t - Real.log 3 + 3 / t := by
    have h := Real.log_le_log hN0 hNhi
    have he : t / 3 + 1 = (t / 3) * (1 + 3 / t) := by field_simp
    rw [he, Real.log_mul (by positivity) (by positivity),
      Real.log_div ht0.ne' (by norm_num : (3 : ℝ) ≠ 0)] at h
    have hb := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 3 / t)
    linarith
  have hlogerr : 3 / t ≤ (3 / 50 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) ht50
  have hh : 1 / (2 * (N : ℝ)) ≤ (3 / 100 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hp : 1 / ‖s - 1‖ ≤ (1 / 50 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (ht50.trans hpole)
  have h1 : ‖s‖ / (12 * (N : ℝ) ^ 2) ≤ (9 / 500 : ℝ) := by
    calc
      _ ≤ (6 * t / 5) / (12 * (t / 3) ^ 2) := by
        gcongr
        linarith
      _ = 9 / (10 * t) := by field_simp; ring
      _ ≤ _ := by rw [div_le_iff₀ (by positivity)]; linarith
  have h3 : (‖s‖ + 2) ^ 3 / (720 * (N : ℝ) ^ 4) ≤ (1 / 250 : ℝ) := by
    calc
      _ ≤ (6 * t / 5) ^ 3 / (720 * (t / 3) ^ 4) := by
        gcongr
        linarith
      _ = 243 / (1250 * t) := by field_simp; ring
      _ ≤ _ := by rw [div_le_iff₀ (by positivity)]; linarith
  have h4 : (‖s‖ + 3) ^ 4 / (2880 * (N : ℝ) ^ 4) ≤ (3 / 50 : ℝ) := by
    calc
      _ ≤ (6 * t / 5) ^ 4 / (2880 * (t / 3) ^ 4) := by gcongr
      _ = (729 / 12500 : ℝ) := by field_simp; ring
      _ ≤ _ := by norm_num
  have hb := backlund_unit_em_bound hs hs1 hN6
  change ‖riemannZeta s‖ < Real.log t - 1 / 10
  linarith [Real.log_three_gt_d9]

#print axioms backlund_unit_em_bound
#print axioms backlund_zeta_unit_line

end LiuWang.Proof.Campaign20260915.RosserCount
