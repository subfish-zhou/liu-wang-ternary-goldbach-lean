import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.ActualInner

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment

def scaledGate (L : ℝ) : ℝ := 10000 * L ^ (3 : ℕ) * Real.log (L ^ (3 : ℕ))

theorem densityGate_le_middle {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    densityGate q ≤ middleUpper N q := by
  have hL := sourceL_ge_3100 hN
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hlog : Real.log q ≤ 3 * sourceL N := by
    have hh := Real.log_le_log hq0 hq
    rw [sourceP, Real.log_pow] at hh
    have hl := Real.log_le_sub_one_of_pos (by linarith : 0 < sourceL N)
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  unfold densityGate middleUpper
  apply max_le
  · apply (div_le_div_iff_of_pos_right hq0).mpr
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) hL 7
    nlinarith [Real.pi_gt_three]
  · apply (le_div_iff₀ hq0).mpr
    have hh : 10000 * Real.log q * (q : ℝ) ≤ 30000 * sourceL N ^ (4 : ℕ) := by
      have hm := mul_le_mul (by linarith : 10000 * Real.log q ≤ 30000 * sourceL N)
        hq (by positivity) (by positivity)
      exact hm.trans_eq (by unfold sourceP; ring)
    have hp : (1000 : ℝ) ≤ sourceL N ^ (3 : ℕ) := by
      have ht := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) hL 3
      linarith
    calc
      _ ≤ 30000 * sourceL N ^ (4 : ℕ) := hh
      _ ≤ 30 * sourceL N ^ (3 : ℕ) * sourceL N ^ (4 : ℕ) := by gcongr; linarith
      _ ≤ 10 * Real.pi * sourceL N ^ (7 : ℕ) := by
        rw [show sourceL N ^ (7 : ℕ) = sourceL N ^ (3 : ℕ) * sourceL N ^ (4 : ℕ) by ring]
        nlinarith [mul_nonneg (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi - 3)
          (by positivity : 0 ≤ sourceL N ^ (3 : ℕ) * sourceL N ^ (4 : ℕ))]

theorem low_gate_coupled_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) :
    0 < omegaCutoff N q ∧ densityGate q ≤ middleUpper N q ∧
      (q : ℝ) * densityGate q ≤ scaledGate (sourceL N) := by
  have hL := sourceL_ge_3100 hN
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hP : (0 : ℝ) < sourceP N := by unfold sourceP; positivity
  have hlog : Real.log q ≤ Real.log (sourceP N) := Real.log_le_log hq0 hq
  have hlog0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast NeZero.pos q)
  have hprod : (q : ℝ) * densityGate q = max 100000 (10000 * (q : ℝ) * Real.log q) := by
    rw [densityGate, mul_max_of_nonneg _ _ hq0.le, mul_div_cancel₀ _ hq0.ne']
    congr 1
    ring
  have hmin : 3.36 * sourceP N ≤ (q : ℝ) * densityGate q := by
    have ht := (div_le_iff₀ hq0).mp hgate
    simpa only [omegaCutoff, mul_comm] using ht
  have hbig : (100000 : ℝ) < 3.36 * sourceP N := by
    unfold sourceP
    have ht := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) hL 3
    linarith
  have hwhich : 100000 ≤ 10000 * (q : ℝ) * Real.log q := by
    rw [hprod] at hmin
    by_contra hh
    rw [max_eq_left (le_of_not_ge hh)] at hmin
    linarith
  refine ⟨(middle_height_domain hN hq).1, densityGate_le_middle hN hq, ?_⟩
  rw [hprod, max_eq_right hwhich]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num)) hlog hlog0 (by positivity)

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
