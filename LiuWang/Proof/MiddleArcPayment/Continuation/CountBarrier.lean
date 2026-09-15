import LiuWang.Proof.MiddleArcPayment.Continuation.MovingCells

/-!
# A certified numerical obstruction for the available count majorant

Near the original threshold, even the first height cell of `movingScalar`
exceeds `10 N`. This is a lower bound on a particular upper majorant, not on
the zero packet or on S. Thus the numerical payment cannot be claimed from
that majorant: genuinely sharper density or cancellation is still needed.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.MiddleArcPayment.Continuation

theorem modulusCount_one_ge_one (q : ℕ) [NeZero q] :
    1 ≤ modulusCount q 1 := by
  have hq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast (NeZero.one_le : 1 ≤ q))
  have hfive : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have ha : 0 < Real.arctan 1 := Real.arctan_pos.mpr (by norm_num)
  have ha1 : Real.arctan 1 ≤ 1 := by rw [Real.arctan_one]; linarith [Real.pi_lt_four]
  rw [Real.arctan_one] at ha1
  unfold modulusCount
  apply (le_div_iff₀ ha).mpr
  norm_num
  nlinarith

theorem middle_modulus_ge_ten_billion {q N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N < (q : ℝ)) :
    10000000000 ≤ (q : ℝ) := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) (sourceL_ge_3100 hN) 3
  change sourceL N ^ 3 < (q : ℝ) at hq
  norm_num at h
  linarith

theorem base_height_log_ge_twenty {q N : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N < (q : ℝ)) :
    20 ≤ Real.log (heightScale q 1) := by
  have hqbig := middle_modulus_ge_ten_billion hN hq
  have he : Real.exp 20 ≤ (3 : ℝ) ^ 20 := by
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 20
  have hx := (heightScale_parameters q 1).2.1
  apply (Real.le_log_iff_exp_le (by linarith : 0 < heightScale q 1)).mpr
  exact he.trans (by norm_num; linarith)

theorem base_cell_power_lower {q N : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N < (q : ℝ))
    (hL : sourceL N ≤ 4000) :
    (N : ℝ) / 19683 ≤ (N : ℝ) ^ movingCutoff q 1 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr
    (nat_pos_of_exp_le (exp_2000_le_of_exp_3100_le hN))
  have hlog := base_height_log_ge_twenty hN hq
  have hdiv : sourceL N / (24 * Real.log (heightScale q 1)) ≤ 9 :=
    (div_le_iff₀ (by linarith)).mpr (by nlinarith)
  have hexp : Real.exp 9 ≤ 19683 := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 9
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one, show (3 : ℝ) ^ 9 = 19683 by norm_num]
      using h
  have hexponent : Real.log N - 9 ≤ Real.log N * movingCutoff q 1 := by
    change sourceL N - 9 ≤ sourceL N * (1 - 1 / (24 * Real.log (heightScale q 1)))
    calc
      _ ≤ sourceL N - sourceL N / (24 * Real.log (heightScale q 1)) := by linarith
      _ = _ := by ring
  calc
    _ ≤ (N : ℝ) / Real.exp 9 :=
      div_le_div_of_nonneg_left hn.le (Real.exp_pos _) hexp
    _ = Real.exp (Real.log N - 9) := by rw [Real.exp_sub, Real.exp_log hn]
    _ ≤ _ := by rw [Real.rpow_def_of_pos hn]; exact Real.exp_le_exp.mpr hexponent

theorem movingScalar_ge_ten_N {q N : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N < (q : ℝ))
    (hL : sourceL N ≤ 4000) (eta : ℝ) :
    10 * (N : ℝ) ≤ movingScalar q N eta := by
  have hqbig := middle_modulus_ge_ten_billion hN hq
  have hroot : 100000 ≤ Real.sqrt q :=
    Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast hqbig)
  have hpower := base_cell_power_lower hN hq hL
  have hcount := modulusCount_one_ge_one q
  have hfirst :
      (N : ℝ) ^ movingCutoff q 1 * 2 * modulusCount q 1 ≤
        ∑ j ∈ Finset.range (sourceDyadicHeight N + 1),
          (N : ℝ) ^ movingCutoff q (cellUpper 1 j) *
            heightCost N eta (cellLower 1 j) * modulusCount q (cellUpper 1 j) := by
    have h := Finset.single_le_sum
      (s := Finset.range (sourceDyadicHeight N + 1))
      (f := fun j => (N : ℝ) ^ movingCutoff q (cellUpper 1 j) *
        heightCost N eta (cellLower 1 j) * modulusCount q (cellUpper 1 j))
      (fun j _ => mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (heightCost_nonneg N eta _))
        (modulusCount_nonneg (by unfold cellUpper; positivity)))
      (show 0 ∈ Finset.range (sourceDyadicHeight N + 1) by simp)
    simpa [cellUpper, cellLower, heightCost] using h
  have hpositive : 0 ≤ (N : ℝ) ^ movingCutoff q 1 := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    _ ≤ 100000 * ((N : ℝ) / 19683 * 2) := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
    _ ≤ Real.sqrt q * ((N : ℝ) ^ movingCutoff q 1 * 2 * modulusCount q 1) := by
      apply mul_le_mul hroot _ (by positivity) (Real.sqrt_nonneg _)
      calc
        _ ≤ (N : ℝ) ^ movingCutoff q 1 * 2 := by linarith
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hcount
    _ ≤ _ := mul_le_mul_of_nonneg_left hfirst (Real.sqrt_nonneg _)

theorem movingScalar_exceeds_target {q N : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N < (q : ℝ))
    (hL : sourceL N ≤ 4000) (eta : ℝ) :
    0.5033 * (N : ℝ) / sourceL N < movingScalar q N eta := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr
    (nat_pos_of_exp_le (exp_2000_le_of_exp_3100_le hN))
  have hLpos := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  apply lt_of_lt_of_le _ (movingScalar_ge_ten_N hN hq hL eta)
  apply (div_lt_iff₀ hLpos).mpr
  nlinarith [sourceL_ge_3100 hN]

end LiuWang.Proof.MiddleArcPayment.Continuation
