import LiuWang.Proof.Campaign20260915.ZetaValidation.RationalAngle
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def gamma16AngleTerm (m : ℕ) : ℚ :=
  if m < 4 then
    (314159 / 100000 : ℚ) / 2 - rationalAtanTaylor 12 ((4 * m + 1) / 32)
  else if m < 16 then
    (314159 / 100000 : ℚ) / 4 + rationalAtanTaylor 12 ((31 - 4 * m) / (33 + 4 * m))
  else rationalAtanTaylor 12 (32 / (4 * m + 1))

def gamma16LogPiQuarter : ℚ :=
  -(∑ j ∈ Finset.range 12, (1 - 314159 / 400000 : ℚ) ^ (j + 1) / (j + 1))

def gamma16ArgumentCenter : ℚ :=
  40 * (287209 / 414355) - 8 * gamma16LogPiQuarter -
    ∑ m ∈ Finset.range 129, gamma16AngleTerm m

noncomputable section
open Complex Finset

theorem arctan_diagonal {q : ℝ} (hq : 0 < q) :
    Real.arctan q = Real.pi / 4 + Real.arctan ((q - 1) / (q + 1)) := by
  have hd : 0 < q + 1 := by linarith
  have h := Real.arctan_add (x := 1) (y := (q - 1) / (q + 1))
    (by rw [one_mul, div_lt_iff₀ hd]; linarith)
  rw [Real.arctan_one] at h
  have he : (1 + (q - 1) / (q + 1)) / (1 - 1 * ((q - 1) / (q + 1))) = q := by
    field_simp
    ring
  rw [he] at h
  exact h.symm

theorem gamma16AngleTerm_error (m : ℕ) :
    |Real.arctan (32 / (4 * (m : ℝ) + 1)) - (gamma16AngleTerm m : ℝ)| ≤ 1 / 10000 := by
  have hp : |Real.pi - (314159 / 100000 : ℝ)| ≤ 1 / 100000 := by
    rw [abs_le]
    constructor <;> linarith [Real.pi_gt_d6, Real.pi_lt_d6]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  unfold gamma16AngleTerm
  split_ifs with h4 h16
  · have hmR : (m : ℝ) < 4 := by exact_mod_cast h4
    have hq : |((4 * (m : ℚ) + 1) / 32)| ≤ 1 / 2 := by
      have hmQ : (m : ℚ) ≤ 3 := by exact_mod_cast (show m ≤ 3 by omega)
      rw [abs_le]
      constructor <;> linarith [show (0 : ℚ) ≤ m by positivity]
    have he := rationalAtanTaylor_error 12 hq
    have hid := Real.arctan_inv_of_pos (show 0 < (4 * (m : ℝ) + 1) / 32 by positivity)
    rw [inv_div] at hid
    rw [hid]
    push_cast at he ⊢
    norm_num at he
    rw [abs_le] at hp he ⊢
    constructor <;> linarith [hp.1, hp.2, he.1, he.2]
  · have hmlo : (4 : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_not_gt h4)
    have hmhi : (m : ℝ) < 16 := by exact_mod_cast h16
    have hq : |((31 - 4 * (m : ℚ)) / (33 + 4 * m))| ≤ 1 / 2 := by
      have hmQ : (4 : ℚ) ≤ m := by exact_mod_cast (Nat.le_of_not_gt h4)
      have hmQ' : (m : ℚ) < 16 := by exact_mod_cast h16
      rw [abs_le]
      constructor
      · rw [le_div_iff₀ (by positivity)]
        linarith
      · rw [div_le_iff₀ (by positivity)]
        linarith
    have he := rationalAtanTaylor_error 12 hq
    have hd := arctan_diagonal (show (0 : ℝ) < 32 / (4 * m + 1) by positivity)
    have hh : (32 / (4 * (m : ℝ) + 1) - 1) /
        (32 / (4 * m + 1) + 1) = (31 - 4 * m) / (33 + 4 * m) := by
      field_simp
      ring
    rw [hd, hh]
    push_cast at he ⊢
    norm_num at he
    rw [abs_le] at hp he ⊢
    constructor <;> linarith [hp.1, hp.2, he.1, he.2]
  · have hq : |(32 / (4 * (m : ℚ) + 1))| ≤ 1 / 2 := by
      have hmQ : (16 : ℚ) ≤ m := by exact_mod_cast (Nat.le_of_not_gt h16)
      rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
      linarith
    have he := rationalAtanTaylor_error 12 hq
    push_cast at he
    norm_num at he
    exact he.trans (by norm_num)

theorem gamma16_log_pi_error :
    |Real.log Real.pi - (2 * (287209 / 414355 : ℝ) + gamma16LogPiQuarter)| ≤ 1 / 1000 := by
  have hp : |Real.log Real.pi - Real.log (314159 / 100000 : ℝ)| ≤ 1 / 10000 := by
    have h1 := Real.log_le_sub_one_of_pos
      (show 0 < Real.pi / (314159 / 100000 : ℝ) by positivity)
    have h2 := Real.log_le_sub_one_of_pos
      (show 0 < (314159 / 100000 : ℝ) / Real.pi by positivity)
    rw [Real.log_div Real.pi_pos.ne' (by norm_num)] at h1
    rw [Real.log_div (by norm_num) Real.pi_pos.ne'] at h2
    have hh : (314159 / 100000 : ℝ) / Real.pi ≤ 1 + 1 / 10000 := by
      rw [div_le_iff₀ Real.pi_pos]
      linarith [Real.pi_gt_d4]
    rw [abs_le]
    constructor <;> linarith [Real.pi_lt_d4]
  have ht := Real.abs_log_sub_add_sum_range_le
    (x := 1 - 314159 / 400000) (by norm_num) 12
  have he : Real.log (314159 / 100000 : ℝ) =
      2 * Real.log 2 + Real.log (314159 / 400000 : ℝ) := by
    have h2 : Real.log ((2 : ℝ) ^ 2) = 2 * Real.log 2 := by
      simpa only [Nat.cast_ofNat] using Real.log_pow 2 2
    rw [← h2]
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ^ 2 ≠ 0) (by norm_num)]
    norm_num
  have hl := Real.log_two_near_10
  have hc : (gamma16LogPiQuarter : ℝ) =
      -(∑ j ∈ Finset.range 12, (1 - 314159 / 400000 : ℝ) ^ (j + 1) / (j + 1)) := by
    simp only [gamma16LogPiQuarter]
    push_cast
    rfl
  rw [hc]
  norm_num only [show (1 : ℝ) - (1 - 314159 / 400000) = 314159 / 400000 by norm_num] at ht
  rw [he, abs_le] at hp
  rw [abs_le] at ht hl ⊢
  norm_num at ht
  constructor <;> linarith [hp.1, hp.2, ht.1, ht.2, hl.1, hl.2]

theorem gamma16_argument_approx_formula :
    criticalGammaArgumentApprox 16 128 =
      56 * Real.log 2 - 8 * Real.log Real.pi -
        ∑ m ∈ Finset.range 129, Real.arctan (32 / (4 * (m : ℝ) + 1)) := by
  have hz : criticalPoint 16 / 2 = ((1 / 4 : ℝ) : ℂ) + (8 : ℂ) * I := by
    apply Complex.ext <;> norm_num [criticalPoint, Complex.div_re, Complex.div_im,
      Complex.normSq_apply]
  have ht (m : ℕ) :
      (log (criticalPoint 16 / 2 + m)).im = Real.arctan (32 / (4 * (m : ℝ) + 1)) := by
    rw [log_im_of_re_pos (by norm_num [hz]; positivity)]
    have hre : (criticalPoint 16 / 2 + m).re = (1 / 4 : ℝ) + m := by norm_num [hz]
    have him : (criticalPoint 16 / 2 + m).im = (8 : ℝ) := by norm_num [hz]
    rw [hre, him]
    apply congrArg Real.arctan
    field_simp
    ring
  unfold criticalGammaArgumentApprox Complex.logGammaSeq
  rw [Complex.sub_im, Complex.sub_im, Complex.add_im, Complex.im_sum]
  simp_rw [ht]
  have hlog : Real.log 128 = 7 * Real.log 2 := by
    simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 7 = 128 by norm_num] using Real.log_pow 2 7
  have hmul (r : ℝ) : (criticalPoint 16 / 2 * (r : ℂ)).im = 8 * r := by
    rw [hz]
    norm_num [Complex.mul_im]
  rw [hmul, hmul, Complex.ofReal_im]
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
  rw [hlog]
  ring

theorem gamma16_argument_center_error :
    |criticalGammaArgumentApprox 16 128 - (gamma16ArgumentCenter : ℝ)| ≤ 1 / 40 := by
  have hs :
      |(∑ m ∈ Finset.range 129, Real.arctan (32 / (4 * (m : ℝ) + 1))) -
        ∑ m ∈ Finset.range 129, (gamma16AngleTerm m : ℝ)| ≤ 129 / 10000 := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ m ∈ Finset.range 129,
          |Real.arctan (32 / (4 * (m : ℝ) + 1)) - (gamma16AngleTerm m : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ Finset.range 129, (1 / 10000 : ℝ) :=
        Finset.sum_le_sum (fun m _ => gamma16AngleTerm_error m)
      _ = _ := by norm_num
  have hp := gamma16_log_pi_error
  have hl := Real.log_two_near_10
  rw [gamma16_argument_approx_formula]
  unfold gamma16ArgumentCenter
  push_cast
  rw [abs_le] at hs hp hl ⊢
  constructor <;> linarith [hs.1, hs.2, hp.1, hp.2, hl.1, hl.2]

#print axioms gamma16_argument_center_error

set_option maxHeartbeats 2000000 in
theorem gamma16_argument_center_rational :
    -(39 / 40 : ℚ) ≤ gamma16ArgumentCenter ∧ gamma16ArgumentCenter ≤ -(37 / 40 : ℚ) := by
  norm_num [gamma16ArgumentCenter, gamma16LogPiQuarter, gamma16AngleTerm,
    rationalAtanTaylor, imagIPower, Finset.sum_range_succ]

theorem gamma16_argument_rational_enclosure :
    -(157 / 100 : ℝ) < criticalGammaArgument 16 ∧ criticalGammaArgument 16 < -(3 / 10) := by
  have hcenter := gamma16_argument_center_rational
  have hcl : -(39 / 40 : ℝ) ≤ (gamma16ArgumentCenter : ℝ) := by
    have h : ((-(39 / 40) : ℚ) : ℝ) ≤ (gamma16ArgumentCenter : ℝ) := Rat.cast_le.mpr hcenter.1
    norm_num at h
    exact h
  have hcu : (gamma16ArgumentCenter : ℝ) ≤ -(37 / 40 : ℝ) := by
    have h : (gamma16ArgumentCenter : ℝ) ≤ ((-(37 / 40) : ℚ) : ℝ) := Rat.cast_le.mpr hcenter.2
    norm_num at h
    exact h
  have hn : ‖criticalPoint 16 / 2‖ ≤ (801 / 100 : ℝ) := by
    have hs : ‖criticalPoint 16 / 2‖ ^ 2 = (1025 / 16 : ℝ) := by
      norm_num [Complex.sq_norm, Complex.normSq_apply, criticalPoint, Complex.div_re,
        Complex.div_im]
      rw [div_pow, Complex.sq_norm]
      norm_num [Complex.normSq_apply]
    nlinarith [norm_nonneg (criticalPoint 16 / 2)]
  have he := criticalGammaArgument_error 16 (N := 128) (by norm_num) (by linarith)
  have hc := gamma16_argument_center_error
  have hsq := mul_self_le_mul_self (norm_nonneg (criticalPoint 16 / 2)) hn
  have hb : (‖criticalPoint 16 / 2‖ + ‖criticalPoint 16 / 2‖ ^ 2) / 128 ≤
      (801 / 100 + (801 / 100) ^ 2 : ℝ) / 128 := by nlinarith
  have hi := abs_le.mp (he.trans hb)
  have hj := abs_le.mp hc
  constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]

theorem gamma16_phase_quadrant :
    0 < (criticalGammaPhase 16).re ∧ (criticalGammaPhase 16).im < 0 := by
  have ha := gamma16_argument_rational_enclosure
  have hlo : -(Real.pi / 2) < criticalGammaArgument 16 := by linarith [Real.pi_gt_d2]
  have hhi : criticalGammaArgument 16 < Real.pi / 2 := by linarith [Real.pi_pos]
  rw [criticalGammaPhase_eq_exp_argument]
  constructor
  · simpa [Complex.exp_re] using Real.cos_pos_of_mem_Ioo ⟨hlo, hhi⟩
  · have hp : 0 < -criticalGammaArgument 16 := by linarith
    have hp' : -criticalGammaArgument 16 < Real.pi := by linarith [Real.pi_gt_d2]
    have hs := Real.sin_pos_of_pos_of_lt_pi hp hp'
    simpa [Complex.exp_im] using (show Real.sin (criticalGammaArgument 16) < 0 by
      rw [Real.sin_neg] at hs; linarith)

#print axioms gamma16_argument_rational_enclosure
#print axioms gamma16_phase_quadrant

end

end LiuWang.Proof.Campaign20260915.ZetaValidation
