import LiuWang.Proof.Campaign20260915.ZetaValidation.BernoulliStep
import LiuWang.Proof.Campaign20260915.Totient.RSGamma

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_bernoulli_two_bound {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    |normalizedBernoulli 2 x| ≤ 1 / 12 := by
  have he : normalizedBernoulli 2 x = x ^ 2 / 2 - x / 2 + 1 / 12 := by
    norm_num [normalizedBernoulli_expansion, Finset.sum_range_succ]
    ring
  rw [he, abs_le]
  constructor
  · nlinarith [sq_nonneg (x - 1 / 2)]
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos hx.1 (sub_nonpos.mpr hx.2)]

theorem backlund_bernoulli_two_tail {s : ℂ} (hs : 0 < s.re)
    {a : ℝ} (ha : 0 < a) :
    ‖∫ u in Ioi a, bernoulliKernel 2 s u‖ ≤
      a ^ (-s.re - 1) / (12 * (s.re + 1)) := by
  calc
    _ ≤ ∫ u in Ioi a, (1 / 12 : ℝ) * u ^ (-s.re - 2) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 2 < -1) ha).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [bernoulliKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans hu)]
      simp only [sub_re, neg_re, Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_right
        (backlund_bernoulli_two_bound
          ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩)
        (Real.rpow_nonneg (ha.trans hu).le _)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ha]
      rw [show -s.re - 2 + 1 = -s.re - 1 by ring,
        show -s.re - 1 = -(s.re + 1) by ring, neg_div_neg_eq]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem backlund_zeta_em_correction {s : ℂ} (hs : 1 / 10 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - abelApprox s N‖ ≤
      ‖s‖ * (N : ℝ) ^ (-s.re - 1) / 12 +
        ‖s‖ * ‖s + 1‖ * (N : ℝ) ^ (-s.re - 1) / (12 * (s.re + 1)) := by
  have hNp : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
  have hb : (normalizedBernoulli 2 0 : ℂ) = 1 / 12 := by
    norm_num [normalizedBernoulli_zero]
  have hstep := bernoulli_tail_step 1 (by omega) (s := s) (by linarith) hN
  simp only [bernoulliKernel_first] at hstep
  norm_num only [Nat.cast_one, Nat.reduceAdd] at hstep
  rw [hb] at hstep
  have ht :
      ‖∫ u in Ioi (N : ℝ), centeredAbelKernel s u‖ ≤
        (N : ℝ) ^ (-s.re - 1) / 12 +
          ‖s + 1‖ * ((N : ℝ) ^ (-s.re - 1) / (12 * (s.re + 1))) := by
    rw [hstep]
    have htri := norm_add_le
      (-(1 / 12 : ℂ) * (N : ℂ) ^ (-s - 1))
      ((s + 1) * ∫ u in Ioi (N : ℝ), bernoulliKernel 2 s u)
    norm_num only [norm_mul, norm_neg, norm_div, norm_one, norm_ofNat,
      Complex.norm_natCast_cpow_of_pos hNp, sub_re, neg_re, one_re] at htri
    have htail := mul_le_mul_of_nonneg_left
      (backlund_bernoulli_two_tail (s := s) (by linarith) hNR) (norm_nonneg (s + 1))
    linarith
  rw [zeta_sub_abelApprox hs hs1 hN, norm_mul, norm_neg]
  calc
    _ ≤ ‖s‖ * ((N : ℝ) ^ (-s.re - 1) / 12 +
        ‖s + 1‖ * ((N : ℝ) ^ (-s.re - 1) / (12 * (s.re + 1)))) :=
      mul_le_mul_of_nonneg_left ht (norm_nonneg s)
    _ = _ := by ring

theorem backlund_partial_sum_norm {s : ℂ} (hs : 1 ≤ s.re) (N : ℕ) :
    ‖zetaPartialSum s N‖ ≤ (harmonic N : ℝ) := by
  unfold zetaPartialSum harmonic
  push_cast
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hc : (n + 1 : ℂ) = ((n + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n)]
  rw [neg_re, Nat.cast_succ]
  calc
    (n + 1 : ℝ) ^ (-s.re) ≤ (n + 1 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    _ = _ := Real.rpow_neg_one _

theorem backlund_zeta_em_bound {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 6 ≤ N) :
    ‖riemannZeta s‖ ≤ Real.log N + 2 / 3 + 1 / (2 * (N : ℝ)) +
      1 / ‖s - 1‖ + ‖s‖ / (12 * (N : ℝ) ^ 2) +
        ‖s‖ * ‖s + 1‖ / (24 * (N : ℝ) ^ 2) := by
  have hNp : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp : (N : ℝ) ^ (1 - s.re) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hNR1
      (show 1 - s.re ≤ 0 by linarith)
  have hq : (N : ℝ) ^ (-s.re) ≤ (N : ℝ)⁻¹ := by
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hNR1
      (show -s.re ≤ (-1 : ℝ) by linarith)
  have hr : (N : ℝ) ^ (-s.re - 1) ≤ ((N : ℝ) ^ 2)⁻¹ := by
    convert Real.rpow_le_rpow_of_exponent_le hNR1
      (show -s.re - 1 ≤ (-2 : ℝ) by linarith) using 1
    rw [Real.rpow_neg hNR.le, Real.rpow_two]
  have hsum := (backlund_partial_sum_norm hs N).trans
    (Totient.harmonic_le_log_add_two_thirds hN)
  have happ :
      ‖abelApprox s N‖ ≤ Real.log N + 2 / 3 + 1 / ‖s - 1‖ +
        1 / (2 * (N : ℝ)) := by
    have ha := norm_sub_le (zetaPartialSum s N + (N : ℂ) ^ (1 - s) / (s - 1))
      ((N : ℂ) ^ (-s) / 2)
    have hb := norm_add_le (zetaPartialSum s N) ((N : ℂ) ^ (1 - s) / (s - 1))
    norm_num only [norm_div, norm_ofNat, Complex.norm_natCast_cpow_of_pos hNp,
      sub_re, one_re, neg_re] at ha hb
    have h1 := div_le_div_of_nonneg_right hp (norm_nonneg (s - 1))
    have h2 := div_le_div_of_nonneg_right hq (by norm_num : (0 : ℝ) ≤ 2)
    change ‖zetaPartialSum s N + (N : ℂ) ^ (1 - s) / (s - 1) -
      (N : ℂ) ^ (-s) / 2‖ ≤ _
    have he : (N : ℝ)⁻¹ / 2 = 1 / (2 * (N : ℝ)) := by ring
    rw [he] at h2
    linarith
  have he := backlund_zeta_em_correction (s := s) (by linarith) hs1 (by omega : 1 ≤ N)
  have he1 :
      ‖s‖ * (N : ℝ) ^ (-s.re - 1) / 12 ≤ ‖s‖ / (12 * (N : ℝ) ^ 2) := by
    calc
      _ ≤ ‖s‖ * ((N : ℝ) ^ 2)⁻¹ / 12 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr (norm_nonneg s))
          (by norm_num)
      _ = _ := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  have he2 :
      ‖s‖ * ‖s + 1‖ * (N : ℝ) ^ (-s.re - 1) / (12 * (s.re + 1)) ≤
        ‖s‖ * ‖s + 1‖ / (24 * (N : ℝ) ^ 2) := by
    calc
      _ ≤ ‖s‖ * ‖s + 1‖ * ((N : ℝ) ^ 2)⁻¹ / (12 * (s.re + 1)) := by
        gcongr
      _ ≤ ‖s‖ * ‖s + 1‖ * ((N : ℝ) ^ 2)⁻¹ / 24 := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
        linarith
      _ = _ := by ring
  have hz := norm_add_le (riemannZeta s - abelApprox s N) (abelApprox s N)
  rw [sub_add_cancel] at hz
  linarith

#print axioms backlund_bernoulli_two_bound
#print axioms backlund_bernoulli_two_tail
#print axioms backlund_zeta_em_correction
#print axioms backlund_partial_sum_norm
#print axioms backlund_zeta_em_bound

end LiuWang.Proof.Campaign20260915.RosserCount
