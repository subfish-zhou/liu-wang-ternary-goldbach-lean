import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.OriginalScalar

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

theorem low_gate_exact {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (_hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) :
    densityGate q = 10000 * Real.log q := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hL := sourceL_ge_3100 hN
  have hbig : 100000 / (q : ℝ) < omegaCutoff N q := by
    unfold omegaCutoff
    apply (div_lt_div_iff_of_pos_right hq0).mpr
    unfold sourceP
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) hL 3
    linarith
  have hwhich : 100000 / (q : ℝ) ≤ 10000 * Real.log q := by
    by_contra hh
    have hmax : densityGate q = 100000 / (q : ℝ) :=
      max_eq_left (le_of_not_ge hh)
    rw [hmax] at hgate
    linarith
  exact max_eq_right hwhich

theorem low_gate_modulus_lower {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) :
    (700000 : ℝ) ≤ q := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hL := sourceL_ge_3100 hN
  have hbase : (100000000000 : ℝ) < 3.36 * sourceP N := by
    unfold sourceP
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) hL 3
    linarith
  have hprod : 3.36 * sourceP N ≤ 10000 * Real.log q * (q : ℝ) := by
    rw [low_gate_exact hN hq hgate] at hgate
    exact (div_le_iff₀ hq0).mp hgate
  by_contra hh
  have hsmall : (q : ℝ) ≤ 700000 := le_of_lt (lt_of_not_ge hh)
  have hlog : Real.log q ≤ 14 := by
    apply (Real.log_le_iff_le_exp hq0).mpr
    calc
      _ ≤ (700000 : ℝ) := hsmall
      _ ≤ (2.7 : ℝ) ^ (14 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (14 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hm := mul_le_mul_of_nonneg_right hlog hq0.le
  nlinarith only [hm, hsmall, hbase, hprod]

theorem low_scaled_interval {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q)
    {y : ℝ} (hy : y ∈ Set.Icc (omegaCutoff N q) (densityGate q)) :
    (q : ℝ) * y ∈ Set.Icc (3.36 * sourceP N) (scaledGate (sourceL N)) ∧
      y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q) := by
  have hd := low_gate_coupled_domain hN hq hgate
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hmin : 3.36 * sourceP N ≤ (q : ℝ) * y := by
    have hh := (div_le_iff₀ hq0).mp hy.1
    simpa only [mul_comm] using hh
  exact ⟨⟨hmin, (mul_le_mul_of_nonneg_left hy.2 hq0.le).trans hd.2.2⟩,
    ⟨hy.1, hy.2.trans hd.2.1⟩⟩

theorem low_scalar_domain {L : ℝ} (hL : 3100 ≤ L) :
    0 < 3.36 * L ^ (3 : ℕ) ∧
      3.36 * L ^ (3 : ℕ) ≤ scaledGate L ∧
      ∀ y ∈ Set.Icc (3.36 * L ^ (3 : ℕ)) (scaledGate L),
        1 < y ∧ 3 ≤ Real.log (L ^ (3 : ℕ) * y) := by
  have hL0 : 0 < L := by linarith
  have hlog : 7 ≤ Real.log L :=
    log_3100_bounds.1.trans (Real.log_le_log (by norm_num) hL)
  have hlogP : 21 ≤ Real.log (L ^ (3 : ℕ)) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hP : 1 ≤ L ^ (3 : ℕ) := one_le_pow₀ (by linarith)
  refine ⟨by positivity, ?_, ?_⟩
  · unfold scaledGate
    nlinarith [mul_le_mul_of_nonneg_left hlogP (by positivity : 0 ≤ L ^ (3 : ℕ))]
  · intro y hy
    have hy1 : 1 < y := by nlinarith [hy.1]
    have hlogy := Real.log_nonneg hy1.le
    rw [Real.log_mul (by positivity) (by linarith : y ≠ 0)]
    exact ⟨hy1, by linarith⟩

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight
