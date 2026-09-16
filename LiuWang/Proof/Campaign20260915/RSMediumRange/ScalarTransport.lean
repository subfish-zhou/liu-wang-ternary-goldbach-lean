import LiuWang.Proof.Campaign20260915.Totient.ProductCore
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

theorem four_log_le_sqrt {x : ℝ} (hx : 16000 ≤ x) :
    4 * Real.log x ≤ Real.sqrt x := by
  have he : Real.exp 2 ≤ 16000 := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 2
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  have hl : Real.log 16000 ≤ 10 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 16000)
      (show (16000 : ℝ) ≤ 2 ^ 14 by norm_num)
    rw [Real.log_pow] at h
    norm_num at h
    linarith [Real.log_two_lt_d9]
  have hs : (125 : ℝ) ≤ Real.sqrt 16000 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 16000 by norm_num),
      Real.sqrt_nonneg 16000]
  have hb : Real.log 16000 / Real.sqrt 16000 ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    linarith
  have h := (Real.log_div_sqrt_antitoneOn he (he.trans hx) hx).trans hb
  have h' := (div_le_iff₀ (Real.sqrt_pos.mpr (by linarith))).mp h
  linarith

theorem theorem23_error_le_3_29_error {x : ℝ} (hx : 16000 ≤ x) :
    2 / Real.sqrt x ≤ 1 / (2 * Real.log x) := by
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  apply (div_le_div_iff₀ hs (by positivity : 0 < 2 * Real.log x)).mpr
  nlinarith [four_log_le_sqrt hx]

theorem theorem23_envelope_le_3_29 {x : ℝ} (hx : 16000 ≤ x) :
    Real.exp Real.eulerMascheroniConstant * (Real.log x + 2 / Real.sqrt x) ≤
      Totient.productEnvelope x := by
  exact mul_le_mul_of_nonneg_left
    (add_le_add_right (theorem23_error_le_3_29_error hx) _)
    (Real.exp_pos _).le

theorem theta_lower_on_cell {a b x t : ℝ}
    (ha : 1 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (ht : (b - t) ^ 2 < 4 * b) :
    x - 2 * Real.sqrt x < t := by
  have hx : 0 ≤ x := by linarith
  have hb : 0 ≤ b := by linarith
  have hsx := Real.sq_sqrt hx
  have hsb := Real.sq_sqrt hb
  have hsm := Real.sqrt_le_sqrt hxb
  have hsl : 1 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ x by linarith)
    simpa using h
  have hmain : b - 2 * Real.sqrt b < t := by
    nlinarith [sq_nonneg (b - t + 2 * Real.sqrt b)]
  have hmono : x - 2 * Real.sqrt x ≤ b - 2 * Real.sqrt b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsm)
      (show 0 ≤ Real.sqrt x + Real.sqrt b - 2 by linarith)]
  exact hmono.trans_lt hmain

theorem theorem23_lower_envelope_on_cell {a b x l r : ℝ}
    (ha : 1 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (hl0 : 0 ≤ l) (hl : l ≤ Real.log a)
    (hr : Real.sqrt b ≤ r) :
    (178107239 / 100000000 : ℝ) * (l + 2 / r) ≤
      Real.exp Real.eulerMascheroniConstant * (Real.log x + 2 / Real.sqrt x) := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < x := ha0.trans_le hax
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsr : Real.sqrt x ≤ r := (Real.sqrt_le_sqrt hxb).trans hr
  have hr0 : 0 < r := hs.trans_le hsr
  have hlog : l ≤ Real.log x := hl.trans (Real.log_le_log ha0 hax)
  have hdiv : 2 / r ≤ 2 / Real.sqrt x :=
    div_le_div_of_nonneg_left (by norm_num) hs hsr
  have hg :=
    LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.gammaFactor_interval.1
  change (1.78107239 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant at hg
  exact mul_le_mul (by norm_num at hg ⊢; exact hg) (add_le_add hlog hdiv)
    (by positivity) (Real.exp_pos _).le

#print axioms four_log_le_sqrt
#print axioms theorem23_envelope_le_3_29
#print axioms theta_lower_on_cell
#print axioms theorem23_lower_envelope_on_cell

end LiuWang.Proof.Campaign20260915.RSMediumRange
