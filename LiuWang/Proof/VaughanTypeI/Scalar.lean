import LiuWang.Proof.VaughanTypeI.Middle
import LiuWang.Proof.VaughanTypeI.VariableKernel

/-! # 原大 N、同分母范围内的独立核界标量支付。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeI

open Interfaces Parameters Finset

theorem source_q_million {N q : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) : (1000000 : ℝ) ≤ q := by
  have hL : (10 : ℝ) ≤ sourceL N := by linarith [sourceL_ge_3100 hN]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hL 6
  norm_num at hp
  exact hp.trans hqL

theorem one_add_log_q_le_L {N q : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N) :
    1 + Real.log q ≤ sourceL N := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  have hqp : (0 : ℝ) < q := by linarith [source_q_million hN hqL]
  have hlog := Real.log_le_log hqp hqU
  rw [log_sourceQ h2000] at hlog
  have hlogL : 1 ≤ Real.log (sourceL N) := by
    apply (Real.le_log_iff_exp_le (sourceL_pos h2000)).mpr
    exact (Real.exp_one_lt_d9.le).trans (by linarith [sourceL_ge_3100 hN])
  linarith

theorem sourceVaughan_log_bounds {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    1 + Real.log (sourceVaughanV N) ≤ sourceL N ∧
      1 + Real.log (sourceVaughanU N * sourceVaughanV N) ≤ sourceL N ∧
      Real.log (sourceVaughanU N * sourceVaughanV N) ≤ (4 / 5 : ℝ) * sourceL N := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  have hlogL := Real.log_nonneg (one_le_sourceL h2000)
  have hlogLt := nat_mul_log_lt (k := 1) (sourceL_ge_2000 h2000) (by norm_num)
  have hL := sourceL_ge_3100 hN
  rw [log_sourceVaughanV h2000, Real.log_mul (sourceVaughanU_pos h2000).ne'
    (sourceVaughanV_pos h2000).ne', log_sourceVaughanU h2000, log_sourceVaughanV h2000]
  constructor
  · norm_num at hlogLt
    linarith
  · constructor <;> linarith

theorem kernel_N_term_le {N q : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) {X W : ℝ}
    (hX : 1 + Real.log X ≤ sourceL N) (hW : 0 ≤ W) (hWL : W ≤ sourceL N) :
    (6 * (N : ℝ) / q * (1 + Real.log X)) * W ≤
      0.0131 * (N : ℝ) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * sourceL N ^ 2 := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  have hqp : (0 : ℝ) < q := by linarith [source_q_million hN hqL]
  have hroot : (1000 : ℝ) ≤ Real.sqrt q :=
    Real.le_sqrt_of_sq_le (by norm_num only; exact source_q_million hN hqL)
  have hsqp : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqp
  have hcoeff : 6 / (q : ℝ) ≤ 0.0131 / Real.sqrt q := by
    apply (div_le_div_iff₀ hqp hsqp).mpr
    have hs := Real.sq_sqrt hqp.le
    nlinarith [sq_nonneg (Real.sqrt q - 1000)]
  calc
    _ ≤ (6 * (N : ℝ) / q * sourceL N) * W :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX (by positivity)) hW
    _ ≤ (6 * (N : ℝ) / q * sourceL N) * sourceL N :=
      mul_le_mul_of_nonneg_left hWL (by positivity [sourceL_pos h2000])
    _ = (N : ℝ) * (6 / q) * sourceL N ^ 2 := by ring
    _ ≤ (N : ℝ) * (0.0131 / Real.sqrt q) * sourceL N ^ 2 := by
      gcongr
    _ = _ := by
      rw [Real.rpow_neg hqp.le, ← Real.sqrt_eq_rpow]
      ring

theorem kernel_q_term_le {N q : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    {W : ℝ} (hW : 0 ≤ W) (hWL : W ≤ sourceL N) :
    ((q : ℝ) * (5 + 2 * Real.log q)) * W ≤
      0.0005 * (N : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) *
        sourceL N ^ (5 / 2 : ℝ) := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_ge_3100 hN
  have hL0 := sourceL_pos h2000
  have hN0 := natCast_pos_of_exp_le hN
  have hq0 : (0 : ℝ) < q := by linarith [source_q_million hN hqL]
  have hlogq := one_add_log_q_le_L hN hqL hqU
  have hqN : (q : ℝ) * sourceL N ^ 7 ≤ (N : ℝ) := by
    rw [sourceQ_eq_div] at hqU
    exact (le_div_iff₀ (pow_pos hL0 7)).mp hqU
  have hpow : (36000000 : ℝ) ≤ sourceL N ^ 7 := by
    have h100 : (100 : ℝ) ≤ sourceL N := by linarith
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) h100 4
    have hp' := pow_le_pow_right₀ (one_le_sourceL h2000) (show 4 ≤ 7 by norm_num)
    norm_num at hp
    linarith
  have hqbig : 36000000 * (q : ℝ) ≤ (N : ℝ) := by
    simpa only [mul_comm (q : ℝ) 36000000] using
      (mul_le_mul_of_nonneg_left hpow hq0.le).trans hqN
  have hs : 3 * Real.sqrt q ≤ 0.0005 * Real.sqrt N := by
    have hsN := Real.sq_sqrt hN0.le
    have hsq := Real.sq_sqrt hq0.le
    nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sqrt_nonneg (q : ℝ)]
  have hLL : sourceL N ^ (2 : ℕ) ≤ sourceL N ^ (5 / 2 : ℝ) := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le (one_le_sourceL h2000) (show (2 : ℝ) ≤ 5 / 2 by norm_num)
  calc
    _ ≤ ((q : ℝ) * (3 * sourceL N)) * W :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hq0.le) hW
    _ ≤ ((q : ℝ) * (3 * sourceL N)) * sourceL N :=
      mul_le_mul_of_nonneg_left hWL (by positivity)
    _ = (3 * Real.sqrt q) * Real.sqrt q * sourceL N ^ (2 : ℕ) := by
      rw [mul_assoc 3, Real.mul_self_sqrt hq0.le]
      ring
    _ ≤ (0.0005 * Real.sqrt N) * Real.sqrt q * sourceL N ^ (2 : ℕ) := by gcongr
    _ ≤ (0.0005 * Real.sqrt N) * Real.sqrt q * sourceL N ^ (5 / 2 : ℝ) := by gcongr
    _ = _ := by rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

theorem sourceVaughanUV_mul_L_sq {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    sourceVaughanU N * sourceVaughanV N * sourceL N ^ (2 : ℕ) =
      (N : ℝ) ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ) := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  have hn := natCast_pos_of_exp_le hN
  have hl := sourceL_pos h2000
  have hpN : (N : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (2 / 5 : ℝ) =
      (N : ℝ) ^ (4 / 5 : ℝ) := by
    rw [← Real.rpow_add hn]
    norm_num
  have hpL : sourceL N ^ (-4 / 5 : ℝ) * sourceL N ^ (1 / 5 : ℝ) *
      sourceL N ^ (2 : ℕ) = sourceL N ^ (7 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hl, ← Real.rpow_add hl]
    norm_num
  unfold sourceVaughanU sourceVaughanV
  calc
    _ = ((N : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (2 / 5 : ℝ)) *
        (sourceL N ^ (-4 / 5 : ℝ) * sourceL N ^ (1 / 5 : ℝ) * sourceL N ^ (2 : ℕ)) := by ring
    _ = _ := by rw [hpN, hpL]

theorem sourceVaughanV_mul_L_sq_le {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    sourceVaughanV N * sourceL N ^ (2 : ℕ) ≤
      0.0001 * (N : ℝ) ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ) := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  have hn := natCast_pos_of_exp_le hN
  have hl := sourceL_pos h2000
  have hlog10000 : Real.log 10000 ≤ 36 := by
    have h10 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    have he : (10000 : ℝ) = 10 ^ (4 : ℕ) := by norm_num
    rw [he, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have haux : 10000 * sourceL N ^ (4 / 5 : ℝ) ≤ (N : ℝ) ^ (2 / 5 : ℝ) := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by norm_num : (10000 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hl _).ne',
      Real.log_rpow hl, Real.log_rpow hn]
    change Real.log 10000 + (4 / 5 : ℝ) * Real.log (sourceL N) ≤ (2 / 5 : ℝ) * sourceL N
    have hlogL := nat_mul_log_lt (k := 16) (sourceL_ge_2000 h2000) (by norm_num)
    norm_num at hlogL
    linarith [sourceL_ge_3100 hN]
  have haux' : sourceL N ^ (4 / 5 : ℝ) ≤ 0.0001 * (N : ℝ) ^ (2 / 5 : ℝ) := by
    linarith
  have hpL : sourceL N ^ (1 / 5 : ℝ) * sourceL N ^ (2 : ℕ) =
      sourceL N ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hl, ← Real.rpow_add hl]
    norm_num
  have hpN : (N : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (2 / 5 : ℝ) =
      (N : ℝ) ^ (4 / 5 : ℝ) := by rw [← Real.rpow_add hn]; norm_num
  calc
    _ = (N : ℝ) ^ (2 / 5 : ℝ) *
        (sourceL N ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ)) := by
      rw [sourceVaughanV, mul_assoc, hpL]
    _ ≤ (N : ℝ) ^ (2 / 5 : ℝ) *
        ((0.0001 * (N : ℝ) ^ (2 / 5 : ℝ)) * sourceL N ^ (7 / 5 : ℝ)) := by gcongr
    _ = _ := by
      calc
        _ = 0.0001 * ((N : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (2 / 5 : ℝ)) *
            sourceL N ^ (7 / 5 : ℝ) := by ring
        _ = _ := by rw [hpN]

end LiuWang.Proof.VaughanTypeI
