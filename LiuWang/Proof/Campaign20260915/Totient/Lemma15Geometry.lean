import LiuWang.Proof.Campaign20260915.Totient.ThetaTable
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.Totient

private theorem log_le_two_fifths_sqrt {L : ℝ} (hL : 255 ≤ L) :
    Real.log L ≤ (2 / 5) * Real.sqrt L := by
  have he : Real.exp 2 ≤ 255 := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 2
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  have hlog : Real.log 255 ≤ 6 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 255)
      (show (255 : ℝ) ≤ 2 ^ 8 by norm_num)
    rw [Real.log_pow] at h
    norm_num at h
    linarith [Real.log_two_lt_d9]
  have hs : (15 : ℝ) ≤ Real.sqrt 255 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 255 by norm_num),
      Real.sqrt_nonneg 255]
  have hbase : Real.log 255 / Real.sqrt 255 ≤ (2 / 5 : ℝ) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    linarith
  have h := (Real.log_div_sqrt_antitoneOn he (he.trans hL) hL).trans hbase
  exact (div_le_iff₀ (Real.sqrt_pos.mpr (by linarith))).mp h

theorem lemma15_middle_conditions {L : ℝ} (h255 : 255 ≤ L) (h1340 : L ≤ 1340) :
    let y := 2 + 2 * Real.sqrt (1 + L)
    288 ≤ L + y ∧ L < Chebyshev.theta (L + y) ∧
      0 ≤ y - 2 ∧ y - 2 ≤ (0.9 * L) / Real.log L ∧ L + y ≤ 1420 := by
  dsimp only
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 < Real.log L := Real.log_pos (by linarith)
  have hsL := Real.sq_sqrt hL0.le
  have hs := Real.sq_sqrt (show 0 ≤ 1 + L by linarith)
  have hlo : 16 ≤ Real.sqrt (1 + L) := by nlinarith [Real.sqrt_nonneg (1 + L)]
  have hhi : Real.sqrt (1 + L) < 39 := by nlinarith [Real.sqrt_nonneg (1 + L)]
  have hratio : Real.sqrt (1 + L) ≤ (9 / 8) * Real.sqrt L := by
    nlinarith [Real.sqrt_nonneg L, Real.sqrt_nonneg (1 + L),
      sq_nonneg (Real.sqrt (1 + L) - (9 / 8) * Real.sqrt L)]
  have hlog := log_le_two_fifths_sqrt h255
  have hm := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ 2 * Real.sqrt (1 + L) by positivity)
  have hr := mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg L)
  refine ⟨by linarith, lemma15_middle_theta h255 h1340, by linarith, ?_, by linarith⟩
  apply (le_div_iff₀ hlog0).mpr
  nlinarith

theorem lemma15_large_envelope {L : ℝ} (hL : 1340 ≤ L) :
    let y := (0.9 * L) / Real.log L
    288 ≤ L + y ∧ 0 ≤ y - 2 ∧ y - 2 ≤ (0.9 * L) / Real.log L ∧
      L < (L + y) * (1 - 1 / (2 * Real.log (L + y))) := by
  let y := (0.9 * L) / Real.log L
  have hL0 : 0 < L := by linarith
  have hl : 2 ≤ Real.log L := by
    apply (Real.le_log_iff_exp_le hL0).mpr
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 2
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  have hl0 : 0 < Real.log L := by linarith
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hyeq : y * Real.log L = 0.9 * L := by
    dsimp [y]
    exact div_mul_cancel₀ _ hl0.ne'
  have hyhi : y ≤ (0.45 : ℝ) * L := by
    dsimp [y]
    apply (div_le_iff₀ hl0).mpr
    nlinarith
  have hylo : 2 ≤ y := by
    have hlog := log_le_two_fifths_sqrt (show 255 ≤ L by linarith)
    have hs := Real.sq_sqrt hL0.le
    have hsle : Real.sqrt L ≤ L := by nlinarith [Real.sqrt_nonneg L]
    dsimp [y]
    apply (le_div_iff₀ hl0).mpr
    linarith
  have hx0 : 0 < L + y := by positivity
  have hlog := Real.log_le_log hL0 (show L ≤ L + y by linarith)
  have hlogx : 0 < Real.log (L + y) := hl0.trans_le hlog
  have hgap : L + y < 2 * Real.log (L + y) * y := by
    have h := mul_le_mul_of_nonneg_right hlog hy0
    nlinarith
  have hdiv : (L + y) / (2 * Real.log (L + y)) < y :=
    (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
  change 288 ≤ L + y ∧ 0 ≤ y - 2 ∧ y - 2 ≤ y ∧
    L < (L + y) * (1 - 1 / (2 * Real.log (L + y)))
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  rw [mul_sub, mul_one, mul_one_div]
  linarith

theorem lemma15_scalar {L y : ℝ} (hL : 255 ≤ L) (hy : 0 ≤ y - 2)
    (hyhi : y - 2 ≤ (0.9 * L) / Real.log L) :
    Real.exp Real.eulerMascheroniConstant *
        (Real.log (L + y - 2) + 1 / (2 * Real.log (L + y - 2))) ≤
      Real.exp Real.eulerMascheroniConstant * Real.log L + 2.5 / Real.log L := by
  let E := Real.exp Real.eulerMascheroniConstant
  have hL0 : 0 < L := by linarith
  have hl0 : 0 < Real.log L := Real.log_pos (by linarith)
  have hx0 : 0 < L + y - 2 := by linarith
  have hlog := Real.log_le_log hL0 (show L ≤ L + y - 2 by linarith)
  have hlogx : 0 < Real.log (L + y - 2) := hl0.trans_le hlog
  have hshift : Real.log (L + y - 2) ≤ Real.log L + (0.9 : ℝ) / Real.log L := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx0 hL0)
    rw [Real.log_div hx0.ne' hL0.ne'] at h
    have hs : (y - 2) / L ≤ (0.9 : ℝ) / Real.log L := by
      apply (div_le_iff₀ hL0).mpr
      exact hyhi.trans_eq (by ring)
    have hid : (L + y - 2) / L - 1 = (y - 2) / L := by field_simp; ring
    rw [hid] at h
    linarith
  have hrec : 1 / (2 * Real.log (L + y - 2)) ≤ (0.5 : ℝ) / Real.log L := by
    have h := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
      (show 0 < 2 * Real.log L by positivity)
      (show 2 * Real.log L ≤ 2 * Real.log (L + y - 2) by linarith)
    exact h.trans_eq (by ring)
  have hE :=
    LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.gammaFactor_interval.2
  change E ≤ 1.78107245 at hE
  have hbudget : E * (1.4 : ℝ) ≤ 2.5 := by linarith
  have h := mul_le_mul_of_nonneg_left (add_le_add hshift hrec)
    (Real.exp_pos Real.eulerMascheroniConstant).le
  have he := div_le_div_of_nonneg_right hbudget hl0.le
  dsimp [E] at *
  have hid : Real.exp Real.eulerMascheroniConstant *
      (Real.log L + 0.9 / Real.log L + 0.5 / Real.log L) =
      Real.exp Real.eulerMascheroniConstant * Real.log L +
        (Real.exp Real.eulerMascheroniConstant * 1.4) / Real.log L := by ring
  rw [hid] at h
  linarith

#print axioms lemma15_middle_conditions
#print axioms lemma15_large_envelope
#print axioms lemma15_scalar

end LiuWang.Proof.Campaign20260915.Totient
