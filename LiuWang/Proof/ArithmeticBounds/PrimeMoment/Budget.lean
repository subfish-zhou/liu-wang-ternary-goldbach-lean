import LiuWang.Proof.ArithmeticBounds.PrimeMoment.PrimeSum

/-! 用原 U、V 定义支付全应用域；不使用错误的 log U / log Y ≥ 2/3。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds.PrimeMoment

open Parameters LambdaMoment

theorem log_le_hundredth {L : Real} (hL : 3100 ≤ L) :
    Real.log L ≤ L / 100 := by
  have hL0 : 0 < L := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < L / 256 by positivity)
  rw [Real.log_div hL0.ne' (by norm_num)] at h
  have h256 : Real.log (256 : Real) ≤ 8 := by
    have heq : Real.log (256 : Real) = 8 * Real.log 2 := by
      simpa only [show (2 : Real) ^ 8 = 256 by norm_num, Nat.cast_ofNat] using
        (Real.log_pow (2 : Real) 8)
    rw [heq]
    linarith [Real.log_two_lt_d9]
  linarith

theorem log_source_quotient_V {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    Real.log ((N : Real) / sourceVaughanV N) =
      (3 * Interfaces.sourceL N - Real.log (Interfaces.sourceL N)) / 5 := by
  rw [Real.log_div (natCast_pos_of_exp_le hN).ne' (sourceVaughanV_pos hN).ne',
    log_sourceVaughanV hN]
  change Interfaces.sourceL N - _ = _
  ring

theorem scalar_budget_31 {L u y x : Real}
    (hL : 3100 ≤ L)
    (hu : u = (2 * L - 4 * Real.log L) / 5)
    (hy : y = (3 * L - Real.log L) / 5)
    (hx0 : 0 ≤ x) (hxy : x ≤ y) :
    (x ^ 2 - u ^ 2) / 2 + 20 * x + 2043 / 10000 ≤ (31 / 100) * y ^ 2 := by
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlog := log_le_hundredth hL
  have hL0 : 0 ≤ L := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hu' : (49 / 125 : Real) * L ≤ u := by linarith
  have hy' : y ≤ (3 / 5 : Real) * L := by linarith
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hxsq : x ^ 2 ≤ y ^ 2 := by nlinarith
  have husq : ((49 / 125 : Real) * L) ^ 2 ≤ u ^ 2 :=
    pow_le_pow_left₀ (by positivity) hu' 2
  have hysq : y ^ 2 ≤ ((3 / 5 : Real) * L) ^ 2 :=
    pow_le_pow_left₀ hy0 hy' 2
  have hpay : 3100 * L ≤ L ^ 2 := by nlinarith
  nlinarith

theorem source_prime_budget_31 {N : Nat} {M : Real}
    (hN : Real.exp 3100 ≤ (N : Real))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : Real) / sourceVaughanU N) :
    W1 N ((N : Real) / M) + 2043 / 10000 ≤
      (31 / 100) * Real.log ((N : Real) / sourceVaughanV N) ^ 2 := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hg := source_quotient_geometry hN hM hM'
  have hX0 := (sourceVaughanU_pos hn).trans_le hg.2.1
  have hW := W1_le_20 hn hg.2.1 hg.2.2.2.2
  have hb := scalar_budget_31 (sourceL_ge_3100 hN)
    (log_sourceVaughanU hn) (log_source_quotient_V hn)
    (Real.log_nonneg ((one_lt_sourceVaughanU hn).le.trans hg.2.1))
    (Real.log_le_log hX0 hg.2.2.1)
  linarith

end LiuWang.Proof.ArithmeticBounds.PrimeMoment
