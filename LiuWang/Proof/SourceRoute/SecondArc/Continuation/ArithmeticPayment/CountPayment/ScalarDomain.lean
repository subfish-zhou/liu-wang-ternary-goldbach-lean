import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.GateDomain

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment

theorem scaledGate_bounds {L : ℝ} (hL : 3100 ≤ L) :
    210000 * L ^ (3 : ℕ) ≤ scaledGate L ∧
      scaledGate L ≤ (86000000 : ℝ) ^ (2 : ℕ) * scaling L ^ (8 : ℕ) := by
  have hs := scaling_bounds hL
  have hr : 0 < scaling L := by linarith
  have hlogL : 7 ≤ Real.log L :=
    log_3100_bounds.1.trans (Real.log_le_log (by norm_num) hL)
  have hu : Real.log L ≤ 8.05 * scaling L ^ (2 : ℕ) := by
    rw [log_source_in_scaling hL]
    nlinarith [log_3100_bounds.2, Real.log_le_sub_one_of_pos hr,
      sq_nonneg (scaling L - 1)]
  unfold scaledGate
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlogL (by positivity : 0 ≤ L ^ (3 : ℕ))]
  · have hm := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 30000 * L ^ (3 : ℕ))
    calc
      _ ≤ 241500 * L ^ (3 : ℕ) * scaling L ^ (2 : ℕ) := by nlinarith only [hm]
      _ = (241500 * (3100 : ℝ) ^ (3 : ℕ)) * scaling L ^ (8 : ℕ) := by
        nth_rw 1 [hs.2]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

theorem fixed_log_gate : Real.log ((86000000 : ℝ) ^ (2 : ℕ)) ≤ 36.6 := by
  apply (Real.log_le_iff_le_exp (by norm_num : 0 < (86000000 : ℝ) ^ (2 : ℕ))).mpr
  calc
    (86000000 : ℝ) ^ (2 : ℕ) ≤ (2.718 : ℝ) ^ (36 : ℕ) * (1 + 0.6 + 0.6 ^ (2 : ℕ) / 2) := by
      norm_num
    _ ≤ Real.exp 1 ^ (36 : ℕ) * Real.exp 0.6 :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _)
        (by nlinarith [Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.6)])
        (by norm_num) (by positivity)
    _ = Real.exp 36.6 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num

theorem log_scaledGate_bounds {L : ℝ} (hL : 3100 ≤ L) :
    0 < Real.log (scaledGate L) ∧ Real.log (scaledGate L) ≤ 36.6 * scaling L := by
  have hs := scaling_bounds hL
  have hb := scaledGate_bounds hL
  have hr : 0 < scaling L := by linarith
  have hL1 : 1 ≤ L ^ (3 : ℕ) := one_le_pow₀ (by linarith : 1 ≤ L)
  have hB1 : 1 < scaledGate L := by linarith
  refine ⟨Real.log_pos hB1, ?_⟩
  have hh := Real.log_le_log (by linarith : 0 < scaledGate L) hb.2
  rw [Real.log_mul (by norm_num) (by positivity)] at hh
  have hf := fixed_log_gate
  simp only [Real.log_pow, Nat.cast_ofNat] at hh hf
  linarith [Real.log_le_sub_one_of_pos hr]

theorem scaledGate_sqrt_bound {L : ℝ} (hL : 3100 ≤ L) :
    Real.sqrt (scaledGate L) ≤ 86000000 * scaling L ^ (4 : ℕ) := by
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity, (scaledGate_bounds hL).2.trans_eq (by ring)⟩

theorem scaledGate_phase {L : ℝ} (hL : 3100 ≤ L) :
    (Real.log (scaledGate L)) ^ (2 : ℕ) ≤ 0.478 * (L + Real.log 0.001) ∧
      40.39 * scaling L ≤ 0.478 * (L + Real.log 0.001) / Real.log (scaledGate L) := by
  have hs := scaling_bounds hL
  have hr : 0 < scaling L := by linarith
  have hl := log_scaledGate_bounds hL
  have hh := original_H_ge_scaling hL
  have hp := pow_le_pow_left₀ hl.1.le hl.2 2
  constructor
  · nlinarith [sq_nonneg (scaling L)]
  · apply (le_div_iff₀ hl.1).mpr
    have hm := mul_le_mul_of_nonneg_left hl.2 (by positivity : 0 ≤ 40.39 * scaling L)
    nlinarith [sq_nonneg (scaling L)]

theorem scaledGate_coefficient {L : ℝ} (hL : 3100 ≤ L) :
    (2 / 9 : ℝ) * Real.log (scaledGate L) +
      2 * (L ^ (3 : ℕ) / scaledGate L) * (4 * Real.log (scaledGate L) + 30) ≤
        8.14 * scaling L := by
  have hs := scaling_bounds hL
  have hl := log_scaledGate_bounds hL
  have hl0 : 0 ≤ Real.log (scaledGate L) := hl.1.le
  have hb := (scaledGate_bounds hL).1
  have hB : 0 < scaledGate L := lt_of_lt_of_le (by positivity) hb
  have hr : L ^ (3 : ℕ) / scaledGate L ≤ (1 / 210000 : ℝ) :=
    (div_le_iff₀ hB).mpr (by linarith)
  have hm := mul_le_mul hr (by linarith [hl.2] : 4 * Real.log (scaledGate L) + 30 ≤
      4 * (36.6 * scaling L) + 30) (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 210000)
  linarith

theorem fixed_gate_exponential : Real.exp (-40.39 : ℝ) ≤ 0.000000000000000003 := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have he : (2.718 : ℝ) ^ (40 : ℕ) * (1 + 0.39 + 0.39 ^ (2 : ℕ) / 2) ≤
      Real.exp (40.39 : ℝ) := by
    calc
      _ ≤ Real.exp 1 ^ (40 : ℕ) * Real.exp 0.39 :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _)
          (by nlinarith [Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.39)])
          (by norm_num) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  linarith

theorem gate_exponential_absorbs {r : ℝ} (hr : 1 ≤ r) :
    r ^ (7 : ℕ) * Real.exp (-40.39 * r) ≤ Real.exp (-40.39 : ℝ) := by
  have hr0 : 0 < r := by linarith
  calc
    _ = Real.exp (7 * Real.log r + -40.39 * r) := by
      rw [Real.exp_add, show (7 : ℝ) = (7 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hr0]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [Real.log_le_sub_one_of_pos hr0])

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
