import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.Source26Reduction

/-! The literal T7 expression at alpha = 19/20, LW p.140, before (2.21). -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1

theorem source21_height_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ sourceT N := by
  have hL := Parameters.sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hp : sourceL N ^ (2 : ℕ) ≤ sourceL N ^ (15 : ℕ) :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hlogq : Real.log q ≤ 3 * Real.log (sourceL N) := by
    simpa only [sourceP, Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hq0 hq
  have hl := original_log_linear hL
  apply max_le
  · have hd : 100000 / (q : ℝ) ≤ 100000 := by
      apply (div_le_iff₀ hq0).mpr
      linarith
    change _ ≤ sourceL N ^ (15 : ℕ)
    nlinarith
  · change _ ≤ sourceL N ^ (15 : ℕ)
    nlinarith

theorem source21_log_factor_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    (17102 + 254231 / s) * s ^ (57 / 10 : ℝ) ≤
      (17102 + 254231 / t) * t ^ (57 / 10 : ℝ) := by
  have he (x : ℝ) (hx : 0 < x) :
      (17102 + 254231 / x) * x ^ (57 / 10 : ℝ) =
        17102 * x ^ (57 / 10 : ℝ) + 254231 * x ^ (47 / 10 : ℝ) := by
    have hp : x ^ (57 / 10 : ℝ) = x ^ (47 / 10 : ℝ) * x := by
      calc
        _ = x ^ ((47 / 10 : ℝ) + 1) := by norm_num
        _ = _ := by rw [Real.rpow_add hx, Real.rpow_one]
    field_simp
    rw [hp]
    ring
  rw [he s hs, he t (hs.trans_le hst)]
  gcongr

theorem source21_expression_compare {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    Applications.sourceSevenBound q (19 / 20) (sourceT N) ≤
      (17102 + 254231 / (18 * Real.log (sourceL N))) *
        (18 * Real.log (sourceL N)) ^ (57 / 10 : ℝ) *
          sourceL N ^ (69 / 20 : ℝ) +
        16541 * (15 * Real.log (sourceL N)) ^ (6 : ℕ) := by
  have hL := Parameters.sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hT0 : 0 < sourceT N := by unfold sourceT; positivity
  have hs : 0 < Real.log ((q : ℝ) * sourceT N) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    have hT1 : 1 < sourceT N := by
      unfold sourceT
      exact one_lt_pow₀ (by linarith) (by norm_num)
    apply Real.log_pos
    nlinarith
  have ht := original_log_product_upper hN hq hT0 le_rfl
  have ht0 : 0 < 18 * Real.log (sourceL N) := hs.trans_le ht
  have hc := source21_log_factor_mono hs ht
  have hA : (q : ℝ) ^ (3 : ℕ) * sourceT N ^ (4 : ℕ) ≤
      sourceL N ^ (69 : ℕ) := by
    calc
      _ ≤ (sourceL N ^ (3 : ℕ)) ^ (3 : ℕ) *
          (sourceL N ^ (15 : ℕ)) ^ (4 : ℕ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hq 3)
          (by positivity)
      _ = _ := by ring
  have hr : ((q : ℝ) ^ (3 : ℕ) * sourceT N ^ (4 : ℕ)) ^ (1 / 20 : ℝ) ≤
      sourceL N ^ (69 / 20 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hA (by norm_num : (0 : ℝ) ≤ 1 / 20)
    rw [← Real.rpow_natCast_mul hL0.le] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hm := mul_le_mul hc hr (Real.rpow_nonneg (by positivity) _)
    (by positivity)
  unfold Applications.sourceSevenBound sourceT
  norm_num only [show (1 - 19 / 20 : ℝ) = 1 / 20 by norm_num,
    show (6 * (19 / 20) : ℝ) = 57 / 10 by norm_num, Real.log_pow, Nat.cast_ofNat]
  dsimp only [sourceT] at hm
  nlinarith only [hm]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1
