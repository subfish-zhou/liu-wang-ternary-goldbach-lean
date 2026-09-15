import LiuWang.Proof.SourceRoute.SecondArc.MiddlePacket
import LiuWang.Proof.SourceRoute.SecondArc.LogHeight
import LiuWang.Proof.SourceRoute.SecondArc.SourceSevenIntegral

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc

def middleUpper (N q : ℕ) : ℝ :=
  10 * Real.pi * sourceL N ^ (7 : ℕ) / q

theorem log_large_le {L : ℝ} (hL : 3100 ≤ L) : Real.log L ≤ 9 * L / 3100 := by
  have hL0 : 0 < L := by linarith
  have hseed : Real.log (3100 : ℝ) ≤ 9 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3100)).mpr
    calc
      (3100 : ℝ) ≤ (2.7 : ℝ) ^ (9 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (9 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
      _ = Real.exp 9 := by rw [← Real.exp_nat_mul]; norm_num
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < L / 3100)
  rw [Real.log_div hL0.ne' (by norm_num)] at h
  linarith

theorem log_ten_pi_le_four : Real.log (10 * Real.pi) ≤ 4 := by
  apply (Real.log_le_iff_le_exp (by positivity : 0 < 10 * Real.pi)).mpr
  calc
    10 * Real.pi ≤ (2.7 : ℝ) ^ (4 : ℕ) := by nlinarith [Real.pi_lt_four]
    _ ≤ Real.exp 1 ^ (4 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
    _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num

theorem log_window_lower {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    sourceL N - 7 ≤ Real.log (0.001 * (N : ℝ)) := by
  have hn := natCast_pos_of_exp_le hN
  have hseed : Real.log (1000 : ℝ) ≤ 7 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1000)).mpr
    calc
      (1000 : ℝ) ≤ (2.7 : ℝ) ^ (7 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (7 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
      _ = Real.exp 7 := by rw [← Real.exp_nat_mul]; norm_num
  rw [show 0.001 * (N : ℝ) = (N : ℝ) / 1000 by ring,
    Real.log_div hn.ne' (by norm_num)]
  change sourceL N - 7 ≤ sourceL N - Real.log 1000
  linarith

theorem middle_height_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    0 < omegaCutoff N q ∧ omegaCutoff N q ≤ middleUpper N q ∧
      middleUpper N q ≤ sourceT N := by
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hP7 : sourceL N ^ (3 : ℕ) ≤ sourceL N ^ (7 : ℕ) :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  refine ⟨by linarith [omegaCutoff_ge (NeZero.pos q) hq], ?_, ?_⟩
  · unfold omegaCutoff sourceP middleUpper
    apply div_le_div_of_nonneg_right _ hq0.le
    exact (mul_le_mul_of_nonneg_left hP7 (by norm_num)).trans
      (mul_le_mul_of_nonneg_right (by linarith [Real.two_le_pi]) (by positivity))
  · unfold middleUpper sourceT
    calc
      10 * Real.pi * sourceL N ^ (7 : ℕ) / (q : ℝ) ≤
          10 * Real.pi * sourceL N ^ (7 : ℕ) :=
        div_le_self (by positivity) hq1
      _ ≤ sourceL N ^ (8 : ℕ) := by
        have hconst : 10 * Real.pi ≤ sourceL N := by linarith [Real.pi_lt_four]
        exact (mul_le_mul_of_nonneg_right hconst (by positivity)).trans_eq (by ring)
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)

theorem middle_log_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q)) :
    1 ≤ y ∧ 1 ≤ Real.log ((q : ℝ) * y) ∧
      4 * Real.log ((q : ℝ) * y) < Real.log (0.001 * (N : ℝ)) := by
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hlo : 3.36 ≤ y := (omegaCutoff_ge (NeZero.pos q) hq).trans hy.1
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hprod : 3.36 ≤ (q : ℝ) * y :=
    hlo.trans (le_mul_of_one_le_left (by linarith) hq1)
  have hz : 1 ≤ Real.log ((q : ℝ) * y) :=
    (Real.le_log_iff_exp_le (by positivity)).mpr (Real.exp_one_lt_three.le.trans (by linarith))
  have hup : (q : ℝ) * y ≤ 10 * Real.pi * sourceL N ^ (7 : ℕ) := by
    have h := (le_div_iff₀ hq0).mp hy.2
    simpa only [mul_comm] using h
  have hlup := Real.log_le_log (by positivity : 0 < (q : ℝ) * y) hup
  rw [Real.log_mul (by positivity : 10 * Real.pi ≠ 0) (by positivity),
    Real.log_pow] at hlup
  norm_num only [Nat.cast_ofNat] at hlup
  refine ⟨by linarith, hz, ?_⟩
  linarith [log_large_le hL, log_ten_pi_le_four, log_window_lower hN]

theorem source_53_packet {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : Nat.Coprime a q) :
    ∀ eta : ℝ, ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
      (10 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((0.001 * (N : ℝ)) ^ (-(1 / 2) : ℝ) *
            bandMass q (1 / 2) (omegaCutoff N q) (middleUpper N q) +
          (∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
            alphaKernel (0.001 * (N : ℝ)) alpha *
              bandMass q alpha (omegaCutoff N q) (middleUpper N q)) +
          ∫ alpha in (59 / 60 : ℝ)..1,
            alphaKernel (0.001 * (N : ℝ)) alpha *
              bandMass q alpha (omegaCutoff N q) (middleUpper N q)) :=
  fun eta => norm_middlePacket_le_alpha_integrals (nat_pos_of_exp_le hN) ha
    (omegaCutoff_pos (exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)) _ eta

theorem source_54_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (alpha : ℝ) :
    bandMass q alpha (omegaCutoff N q) (middleUpper N q) ≤
      (familyCount q alpha (middleUpper N q) : ℝ) / Real.sqrt (middleUpper N q) +
        (1 / 2 : ℝ) * ∫ y in (omegaCutoff N q)..(middleUpper N q),
          heightKernel y * (familyCount q alpha y : ℝ) := by
  have hh := middle_height_domain hN hq
  exact family_height_abel q alpha hh.1 hh.2.1

end LiuWang.Proof.SourceRoute.SecondArc
