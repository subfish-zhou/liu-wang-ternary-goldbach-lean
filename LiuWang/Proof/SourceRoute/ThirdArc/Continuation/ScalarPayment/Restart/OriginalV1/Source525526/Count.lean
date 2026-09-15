import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526.Modulus
import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralFamily

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526

def lastLower (q : ℕ) : ℝ := 1 - 0.2067 / Real.log ((q : ℝ) * lowHeight)

def lastUpper (q : ℕ) : ℝ :=
  1 - 1 / (9.645908801 * Real.log ((q : ℝ) * lowHeight))

def originalLastBill (N q : ℕ) [NeZero q] : ℝ :=
  ((N : ℝ) * Real.sqrt q / q.totient) *
    ∫ alpha in lastLower q..lastUpper q,
      betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight

theorem last_interval_order {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    59 / 60 ≤ lastLower q ∧ lastLower q ≤ lastUpper q ∧ lastUpper q < 1 := by
  have hl : 0 < Real.log ((q : ℝ) * lowHeight) := by
    linarith [M3_log_product_ge_thirty hN hq le_rfl]
  have hbase := M3_rowCutoff_ge_source_split .r0478 hN hq le_rfl
  change 59 / 60 ≤ 1 - 0.478 / Real.log ((q : ℝ) * lowHeight) at hbase
  have hab := div_le_div_of_nonneg_right
    (by norm_num : (0.2067 : ℝ) ≤ 0.478) hl.le
  have hbc := div_le_div_of_nonneg_right
    (by norm_num : (1 / 9.645908801 : ℝ) ≤ 0.2067) hl.le
  rw [div_div] at hbc
  have hp : 0 < 1 / (9.645908801 * Real.log ((q : ℝ) * lowHeight)) := by positivity
  unfold lastLower lastUpper
  exact ⟨by linarith, by linarith, by linarith⟩

theorem theorem_two_low_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    8000000000 ≤ (q : ℝ) * lowHeight ∧
      (q : ℝ) ≤ (q : ℝ) * lowHeight ∧
        (q : ℝ) * lowHeight / q = lowHeight := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  refine ⟨by linarith [(low_table_domain hN hq).1], ?_, ?_⟩
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left lowHeight_ge_one hq0.le
  · field_simp

theorem strict_to_closed_count {q : ℕ} [NeZero q] {a b y : ℝ} (hab : a < b) :
    familyCount q b y ≤ MultiZeroRepulsion.strictFamilyCount q a y := by
  unfold familyCount count MultiZeroRepulsion.strictFamilyCount
  apply Finset.sum_le_sum
  intro chi _
  apply Finset.sum_le_sum_of_subset
  intro rho hrho
  obtain ⟨hz, ⟨h0, h1, hh⟩, hb⟩ := mem_zeroValues.mp hrho
  exact MultiZeroRepulsion.mem_strictZeroValues.mpr ⟨hz, h0, hab.trans_le hb, h1, hh⟩

theorem original_T2_count {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {alpha : ℝ} (ha : lastLower q < alpha) :
    familyCount q alpha lowHeight ≤ 2 := by
  have hd := theorem_two_low_domain hN hq
  have h := MultiZeroRepulsion.Continuation.general_theorem_two hd.1 hd.2.1
  rw [hd.2.2] at h
  have h : MultiZeroRepulsion.strictFamilyCount q (lastLower q) lowHeight ≤ 2 := by
    simpa only [lastLower, show (2067 / 10000 : ℝ) = 0.2067 by norm_num] using h
  exact (strict_to_closed_count ha).trans h

theorem original_last_integral_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    (∫ alpha in lastLower q..lastUpper q,
      betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) ≤
      lowCoefficient (59 / 60) * (2 *
        Real.exp (-0.10367089 * sourceL N / Real.log ((q : ℝ) * lowHeight))) := by
  have hx := natCast_pos_of_exp_le hN
  have hL := sourceL_ge_3100 hN
  have ho := last_interval_order hN hq
  have hhalf : (1 : ℝ) / 2 ≤ lastLower q := by linarith [ho.1]
  have hl : 0 < Real.log ((q : ℝ) * lowHeight) := by
    linarith [M3_log_product_ge_thirty hN hq le_rfl]
  have hc := lowCoefficient_nonneg (by norm_num : (0 : ℝ) < 59 / 60)
  calc
    _ ≤ ∫ alpha in lastLower q..lastUpper q,
        (lowCoefficient (59 / 60) * 2) * betaKernel N alpha := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ho.2.1
        (family_low_integrable q lowHeight hx hhalf ho.2.1)
        (((betaKernel_continuous hx).const_mul _).intervalIntegrable _ _)
      intro alpha ha
      have hcnt : (familyCount q alpha lowHeight : ℝ) ≤ 2 := by
        exact_mod_cast original_T2_count hN hq ha.1
      have hcoef := lowCoefficient_antitone (by norm_num : (0 : ℝ) < 59 / 60)
        (ho.1.trans ha.1.le)
      have hk : 0 ≤ betaKernel N alpha := by
        unfold betaKernel
        exact mul_nonneg (Real.rpow_nonneg hx.le _) (by change 0 ≤ sourceL N; linarith)
      have h := mul_le_mul_of_nonneg_left
        (mul_le_mul hcoef hcnt (Nat.cast_nonneg _) hc) hk
      nlinarith only [h]
    _ = lowCoefficient (59 / 60) * 2 *
        ((N : ℝ) ^ (lastUpper q - 1) - (N : ℝ) ^ (lastLower q - 1)) := by
      rw [intervalIntegral.integral_const_mul, integral_betaKernel hx]
    _ ≤ lowCoefficient (59 / 60) * 2 * (N : ℝ) ^ (lastUpper q - 1) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (Real.rpow_nonneg hx.le _)) (by positivity)
    _ ≤ _ := by
      have hround := div_le_div_of_nonneg_right
        (by norm_num : (0.10367089 : ℝ) ≤ 1 / 9.645908801) hl.le
      rw [div_div] at hround
      have hp : (N : ℝ) ^ (lastUpper q - 1) ≤
          Real.exp (-0.10367089 * sourceL N / Real.log ((q : ℝ) * lowHeight)) := by
        rw [Real.rpow_def_of_pos hx]
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left hround (show 0 ≤ sourceL N by linarith)
        unfold lastUpper sourceL at h ⊢
        simp only [div_eq_mul_inv] at h ⊢
        nlinarith only [h]
      have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ lowCoefficient (59 / 60) * 2 by positivity)
      nlinarith only [h]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526
