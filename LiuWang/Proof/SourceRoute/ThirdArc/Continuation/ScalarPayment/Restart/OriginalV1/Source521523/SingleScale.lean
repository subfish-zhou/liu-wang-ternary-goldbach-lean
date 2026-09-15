import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Consumer

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523

theorem normalized_single_weight {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {beta : ℝ} (hb : 1 / 2 ≤ beta) (hb1 : beta < 1) :
    lowCoefficient beta * (N : ℝ) ^ (beta - 1) ≤ (0.999 : ℝ) :=
  WeightedLowZeros.weight_le_one (WeightedLowZeros.source_endpoint_ge_thousand hN)
    (by linarith) hb1.le

theorem logNu_exp_sixth_antitone :
    AntitoneOn (fun s : ℝ => Source524.logNu s * Real.exp (-s / 6)) (Set.Ici 24) := by
  intro s hs t _ hst
  change 24 ≤ s at hs
  have hs0 : 0 < s := by linarith [hs]
  have hu : 0 ≤ (t - s) / 6 := by linarith
  have hr : 1 ≤ Real.exp ((t - s) / 6) := Real.one_le_exp_iff.mpr hu
  have he := Real.add_one_le_exp ((t - s) / 6)
  have hmul := mul_le_mul_of_nonneg_left he hs0.le
  have hsq := mul_nonneg (show 0 ≤ s - 6 by linarith [hs]) (sub_nonneg.mpr hst)
  have hn := Source524.logNu_scaling hs hr hst (show t ≤ s * Real.exp ((t - s) / 6) by
    nlinarith only [hmul, hsq])
  have h := mul_le_mul_of_nonneg_right hn (Real.exp_pos (-t / 6)).le
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem single_endpoint_log :
    (3.1829365 : ℝ) ≤ Real.log (3 * Real.log 3100) ∧
      Real.log (3 * Real.log 3100) ≤ (3.1829367 : ℝ) := by
  have h := Source524.log_48_precise
  have hid : Real.log (6 * Real.log (3100 : ℝ)) =
      Real.log 2 + Real.log (3 * Real.log 3100) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by linarith [Source524.log_3100_precise.1] : 3 * Real.log (3100 : ℝ) ≠ 0)]
    congr 1
    ring
  rw [hid] at h
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

theorem single_endpoint_nu :
    Source524.logNu (3 * Real.log 3100) ≤
      1.781074 * 3.1829367 + 2.50637 / 3.1829365 := by
  exact add_le_add
    (mul_le_mul Source524.exp_euler_upper single_endpoint_log.2
      (by linarith [single_endpoint_log.1]) (by norm_num))
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) single_endpoint_log.1)

theorem single_endpoint_paid :
    (0.999 : ℝ) * Source524.logNu (3 * Real.log 3100) *
      Real.exp (-(3 * Real.log 3100) / 6) ≤ 0.11585 := by
  have hs : (55.6776 : ℝ) ≤ Real.sqrt 3100 := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  have he : Real.exp (-(3 * Real.log (3100 : ℝ)) / 6) = 1 / Real.sqrt 3100 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3100),
      one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [he, one_div, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
  nlinarith only [single_endpoint_nu, hs]

theorem original_nu_single_scale {L Q : ℝ} (hL : 3100 ≤ L) (hq : L ^ 3 ≤ Q) :
    (0.999 : ℝ) * L * sourceNu Q * Real.exp (-(1 / 2 : ℝ) * Real.log Q) ≤ 0.11585 := by
  have hL0 : 0 < L := by linarith
  have hQ0 : 0 < Q := (pow_pos hL0 3).trans_le hq
  have hl := Real.log_le_log (pow_pos hL0 3) hq
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hLlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3100) hL
  have hs : 24 ≤ 3 * Real.log (3100 : ℝ) := by linarith [Source524.log_3100_precise.1]
  have hst : 3 * Real.log (3100 : ℝ) ≤ Real.log Q := by linarith
  have hn := (Source524.logNu_bounds (hs.trans hst)).2
  have he : L * Real.exp (-(1 / 2 : ℝ) * Real.log Q) ≤
      Real.exp (-Real.log Q / 6) := by
    rw [← Real.exp_log hL0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.999) hn)
  have hd := mul_le_mul_of_nonneg_left
    (logNu_exp_sixth_antitone hs (hs.trans hst) hst) (by norm_num : (0 : ℝ) ≤ 0.999)
  change 0.999 * L * Source524.logNu (Real.log Q) * _ ≤ _
  nlinarith only [h, hd, single_endpoint_paid]

theorem equation_5_21_original {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    {beta : ℝ} (hb : 1 / 2 ≤ beta) (hb1 : beta < 1) :
    (Real.sqrt q / q.totient) * lowCoefficient beta * (N : ℝ) ^ beta ≤
      (0.11585 : ℝ) * N / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have hqR : (0 : ℝ) < q := (pow_pos hLp 3).trans_le hq
  have hw := normalized_single_weight hN hb hb1
  have hk := Source524.sqrt_totient_original (Nat.cast_pos.mp hqR) htotient
  have hscale := original_nu_single_scale hL hq
  have hnu : 0 ≤ Source524.logNu (Real.log q) := by
    have hs := Real.log_le_log (pow_pos hLp 3) hq
    rw [Real.log_pow] at hs
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 3100) hL
    exact (Source524.logNu_bounds (by norm_num at hs; linarith [Source524.log_3100_precise.1])).2
  have h := mul_le_mul hk hw
    (mul_nonneg (lowCoefficient_nonneg (by linarith)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (mul_nonneg hnu (Real.exp_pos _).le)
  have hid : (N : ℝ) * (lowCoefficient beta * (N : ℝ) ^ (beta - 1)) =
      lowCoefficient beta * (N : ℝ) ^ beta :=
    WeightedLowZeros.weight_mul_endpoint (nat_pos_of_exp_le hN) beta
  have h := mul_le_mul_of_nonneg_left h (show 0 ≤ (N : ℝ) * sourceL N by positivity)
  have hp := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg (α := ℝ) N)
  apply (le_div_iff₀ hLp).mpr
  change 0.999 * sourceL N * Source524.logNu (Real.log q) * _ ≤ _ at hscale
  change (N : ℝ) * (0.999 * sourceL N * Source524.logNu (Real.log q) * _) ≤ _ at hp
  calc
    _ = (Real.sqrt q / q.totient * sourceL N) *
        ((N : ℝ) * (lowCoefficient beta * (N : ℝ) ^ (beta - 1))) := by rw [hid]; ring
    _ = (N : ℝ) * sourceL N *
        (Real.sqrt q / q.totient * (lowCoefficient beta * (N : ℝ) ^ (beta - 1))) := by ring
    _ ≤ _ := h
    _ ≤ _ := by nlinarith only [hp]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523
