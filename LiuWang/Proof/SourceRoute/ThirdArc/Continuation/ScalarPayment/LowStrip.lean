import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.StripScalar

/-! The .00003 price applied to the actual full-family strip in original (5.25). -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment

def lowStripBill (N q : ℕ) [NeZero q] : ℝ :=
  ((N : ℝ) * Real.sqrt q / q.totient) *
    ∫ alpha in (1 - 0.478 / Real.log ((q : ℝ) * lowHeight))..
        (1 - 0.2067 / Real.log ((q : ℝ) * lowHeight)),
      betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight

theorem lowCoefficient_le_inverse {b : ℝ} (hb : 0 < b) :
    lowCoefficient b ≤ 1 / b := by
  unfold lowCoefficient
  exact div_le_div_of_nonneg_right
    (sub_le_self _ (Real.rpow_nonneg (by norm_num) b)) hb.le

theorem low_strip_table_envelope {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    lowStripBill N q ≤ ((N : ℝ) * Real.sqrt q / q.totient) *
      ((60 / 59) * 14000 *
        Real.exp (-0.2067 * sourceL N / Real.log ((q : ℝ) * lowHeight))) := by
  have hn := natCast_pos_of_exp_le hN
  have hc : lowCoefficient (59 / 60) ≤ 60 / 59 := by
    simpa using lowCoefficient_le_inverse (by norm_num : (0 : ℝ) < 59 / 60)
  have he : (N : ℝ) ^ (-0.2067 / Real.log ((q : ℝ) * lowHeight)) =
      Real.exp (-0.2067 * sourceL N / Real.log ((q : ℝ) * lowHeight)) := by
    rw [Real.rpow_def_of_pos hn, sourceL]
    congr 1
    ring
  apply (mul_le_mul_of_nonneg_left (original_low_0478_subinterval hN hq)
    (show 0 ≤ (N : ℝ) * Real.sqrt q / q.totient by positivity)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ lowCoefficient (59 / 60) *
        (14000 * (N : ℝ) ^ (-0.2067 / Real.log ((q : ℝ) * lowHeight))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sub_le_self _ (Real.rpow_nonneg hn.le _)) (by norm_num))
        (lowCoefficient_nonneg (by norm_num))
    _ ≤ (60 / 59) *
        (14000 * (N : ℝ) ^ (-0.2067 / Real.log ((q : ℝ) * lowHeight))) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [he]; ring

theorem equation_5_25_stronger {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    lowStripBill N q ≤ 0.00003 * (N : ℝ) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have hs : 0 < Real.log ((q : ℝ) * lowHeight) := by
    linarith [M3_log_product_ge_thirty hN hq le_rfl]
  have h := mul_le_mul_of_nonneg_left (low_strip_coupled_decay hL (NeZero.pos q) hs)
    (show 0 ≤ (14000 * (60 / 59) : ℝ) by norm_num)
  have hpaid : (14000 * (60 / 59)) *
      (sourceL N * (Real.sqrt q / q.totient) *
        Real.exp (-0.2067 * sourceL N / Real.log ((q : ℝ) * lowHeight))) ≤ 0.00003 :=
    h.trans (by simpa only [mul_assoc] using strip_endpoint_certificate)
  apply (low_strip_table_envelope hN hq).trans
  apply (le_div_iff₀ hLp).mpr
  have hn := mul_le_mul_of_nonneg_left hpaid (Nat.cast_nonneg (α := ℝ) N)
  convert hn using 1 <;> ring

theorem equation_5_25 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (_hq1 : (q : ℝ) ≤ sourceP1 N) :
    ((N : ℝ) * Real.sqrt q / q.totient) *
        (∫ alpha in (1 - 0.478 / Real.log ((q : ℝ) * lowHeight))..
            (1 - 0.2067 / Real.log ((q : ℝ) * lowHeight)),
          betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) ≤
      0.00003 * (N : ℝ) / sourceL N :=
  equation_5_25_stronger hN hq

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment
