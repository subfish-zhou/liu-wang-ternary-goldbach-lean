import LiuWang.Proof.Campaign20260915.ZetaValidation.GammaPhase16

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.LowZeroMoment
open LiuWang.Proof.Campaign20260915.ZetaValidation

def gamma14AngleTerm (m : ℕ) : ℚ :=
  if m < 4 then
    (314159 / 100000 : ℚ) / 2 - rationalAtanTaylor 12 ((4 * m + 1) / 28)
  else if m < 14 then
    (314159 / 100000 : ℚ) / 4 + rationalAtanTaylor 12 ((27 - 4 * m) / (29 + 4 * m))
  else rationalAtanTaylor 12 (28 / (4 * m + 1))

def gamma14ArgumentCenter : ℚ :=
  35 * (287209 / 414355) - 7 * gamma16LogPiQuarter -
    ∑ m ∈ Finset.range 129, gamma14AngleTerm m

noncomputable section
open Complex Finset

theorem gamma14AngleTerm_error (m : ℕ) :
    |Real.arctan (28 / (4 * (m : ℝ) + 1)) - (gamma14AngleTerm m : ℝ)| ≤ 1 / 10000 := by
  have hp : |Real.pi - (314159 / 100000 : ℝ)| ≤ 1 / 100000 := by
    rw [abs_le]
    constructor <;> linarith [Real.pi_gt_d6, Real.pi_lt_d6]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  unfold gamma14AngleTerm
  split_ifs with h4 h14
  · have hmR : (m : ℝ) < 4 := by exact_mod_cast h4
    have hq : |((4 * (m : ℚ) + 1) / 28)| ≤ 1 / 2 := by
      have hmQ : (m : ℚ) ≤ 3 := by exact_mod_cast (show m ≤ 3 by omega)
      rw [abs_le]
      constructor <;> linarith [show (0 : ℚ) ≤ m by positivity]
    have he := rationalAtanTaylor_error 12 hq
    have hid := Real.arctan_inv_of_pos (show 0 < (4 * (m : ℝ) + 1) / 28 by positivity)
    rw [inv_div] at hid
    rw [hid]
    push_cast at he ⊢
    norm_num at he
    rw [abs_le] at hp he ⊢
    constructor <;> linarith [hp.1, hp.2, he.1, he.2]
  · have hmlo : (4 : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_not_gt h4)
    have hmhi : (m : ℝ) < 14 := by exact_mod_cast h14
    have hq : |((27 - 4 * (m : ℚ)) / (29 + 4 * m))| ≤ 1 / 2 := by
      have hmQ : (4 : ℚ) ≤ m := by exact_mod_cast (Nat.le_of_not_gt h4)
      have hmQ' : (m : ℚ) < 14 := by exact_mod_cast h14
      rw [abs_le]
      constructor
      · rw [le_div_iff₀ (by positivity)]
        linarith
      · rw [div_le_iff₀ (by positivity)]
        linarith
    have he := rationalAtanTaylor_error 12 hq
    have hd := arctan_diagonal (show (0 : ℝ) < 28 / (4 * m + 1) by positivity)
    have hh : (28 / (4 * (m : ℝ) + 1) - 1) /
        (28 / (4 * m + 1) + 1) = (27 - 4 * m) / (29 + 4 * m) := by
      field_simp
      ring
    rw [hd, hh]
    push_cast at he ⊢
    norm_num at he
    rw [abs_le] at hp he ⊢
    constructor <;> linarith [hp.1, hp.2, he.1, he.2]
  · have hq : |(28 / (4 * (m : ℚ) + 1))| ≤ 1 / 2 := by
      have hmQ : (14 : ℚ) ≤ m := by exact_mod_cast (Nat.le_of_not_gt h14)
      rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
      linarith
    have he := rationalAtanTaylor_error 12 hq
    push_cast at he
    norm_num at he
    exact he.trans (by norm_num)

theorem gamma14_argument_approx_formula :
    criticalGammaArgumentApprox 14 128 =
      49 * Real.log 2 - 7 * Real.log Real.pi -
        ∑ m ∈ Finset.range 129, Real.arctan (28 / (4 * (m : ℝ) + 1)) := by
  have hz : criticalPoint 14 / 2 = ((1 / 4 : ℝ) : ℂ) + (7 : ℂ) * I := by
    apply Complex.ext <;> norm_num [criticalPoint, Complex.div_re, Complex.div_im,
      Complex.normSq_apply]
  have ht (m : ℕ) :
      (log (criticalPoint 14 / 2 + m)).im = Real.arctan (28 / (4 * (m : ℝ) + 1)) := by
    rw [log_im_of_re_pos (by norm_num [hz]; positivity)]
    have hre : (criticalPoint 14 / 2 + m).re = (1 / 4 : ℝ) + m := by norm_num [hz]
    have him : (criticalPoint 14 / 2 + m).im = (7 : ℝ) := by norm_num [hz]
    rw [hre, him]
    apply congrArg Real.arctan
    field_simp
    ring
  unfold criticalGammaArgumentApprox Complex.logGammaSeq
  rw [Complex.sub_im, Complex.sub_im, Complex.add_im, Complex.im_sum]
  simp_rw [ht]
  have hlog : Real.log 128 = 7 * Real.log 2 := by
    simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 7 = 128 by norm_num] using Real.log_pow 2 7
  have hmul (r : ℝ) : (criticalPoint 14 / 2 * (r : ℂ)).im = 7 * r := by
    rw [hz]
    norm_num [Complex.mul_im]
  rw [hmul, hmul, Complex.ofReal_im]
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
  rw [hlog]
  ring

theorem gamma14_argument_center_error :
    |criticalGammaArgumentApprox 14 128 - (gamma14ArgumentCenter : ℝ)| ≤ 1 / 40 := by
  have hs :
      |(∑ m ∈ Finset.range 129, Real.arctan (28 / (4 * (m : ℝ) + 1))) -
        ∑ m ∈ Finset.range 129, (gamma14AngleTerm m : ℝ)| ≤ 129 / 10000 := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ m ∈ Finset.range 129,
          |Real.arctan (28 / (4 * (m : ℝ) + 1)) - (gamma14AngleTerm m : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ Finset.range 129, (1 / 10000 : ℝ) :=
        Finset.sum_le_sum (fun m _ => gamma14AngleTerm_error m)
      _ = _ := by norm_num
  have hp := gamma16_log_pi_error
  have hl := Real.log_two_near_10
  rw [gamma14_argument_approx_formula]
  unfold gamma14ArgumentCenter
  push_cast
  rw [abs_le] at hs hp hl ⊢
  constructor <;> linarith [hs.1, hs.2, hp.1, hp.2, hl.1, hl.2]

set_option maxHeartbeats 2000000 in
theorem gamma14_argument_center_rational :
    -(5 / 2 : ℚ) ≤ gamma14ArgumentCenter ∧ gamma14ArgumentCenter ≤ -(3 / 2 : ℚ) := by
  norm_num [gamma14ArgumentCenter, gamma16LogPiQuarter, gamma14AngleTerm,
    rationalAtanTaylor, imagIPower, Finset.sum_range_succ]

theorem gamma14_argument_rational_enclosure :
    -(31 / 10 : ℝ) < criticalGammaArgument 14 ∧ criticalGammaArgument 14 < 0 := by
  have hcenter := gamma14_argument_center_rational
  have hcl : -(5 / 2 : ℝ) ≤ (gamma14ArgumentCenter : ℝ) := by
    have h : ((-(5 / 2) : ℚ) : ℝ) ≤ (gamma14ArgumentCenter : ℝ) :=
      Rat.cast_le.mpr hcenter.1
    norm_num at h
    exact h
  have hcu : (gamma14ArgumentCenter : ℝ) ≤ -(3 / 2 : ℝ) := by
    have h : (gamma14ArgumentCenter : ℝ) ≤ ((-(3 / 2) : ℚ) : ℝ) :=
      Rat.cast_le.mpr hcenter.2
    norm_num at h
    exact h
  have hn : ‖criticalPoint 14 / 2‖ ≤ (71 / 10 : ℝ) := by
    have hs : ‖criticalPoint 14 / 2‖ ^ 2 = (785 / 16 : ℝ) := by
      norm_num [Complex.sq_norm, Complex.normSq_apply, criticalPoint, Complex.div_re,
        Complex.div_im]
      rw [div_pow, Complex.sq_norm]
      norm_num [Complex.normSq_apply]
    nlinarith [norm_nonneg (criticalPoint 14 / 2)]
  have he := criticalGammaArgument_error 14 (N := 128) (by norm_num) (by linarith)
  have hc := gamma14_argument_center_error
  have hsq := mul_self_le_mul_self (norm_nonneg (criticalPoint 14 / 2)) hn
  have hb : (‖criticalPoint 14 / 2‖ + ‖criticalPoint 14 / 2‖ ^ 2) / 128 ≤
      (71 / 10 + (71 / 10) ^ 2 : ℝ) / 128 := by nlinarith
  have hi := abs_le.mp (he.trans hb)
  have hj := abs_le.mp hc
  constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]

theorem gamma14_phase_im_neg : (criticalGammaPhase 14).im < 0 := by
  have ha := gamma14_argument_rational_enclosure
  have hp : 0 < -criticalGammaArgument 14 := by linarith
  have hp' : -criticalGammaArgument 14 < Real.pi := by linarith [Real.pi_gt_d2]
  have hs := Real.sin_pos_of_pos_of_lt_pi hp hp'
  rw [criticalGammaPhase_eq_exp_argument]
  simpa [Complex.exp_im] using (show Real.sin (criticalGammaArgument 14) < 0 by
    rw [Real.sin_neg] at hs; linarith)

#print axioms gamma14_phase_im_neg

end
end LiuWang.Proof.Campaign20260915.LowZeroMoment
