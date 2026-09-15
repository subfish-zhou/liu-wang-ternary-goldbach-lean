import LiuWang.Proof.NonprincipalDensityMeans.Continuation.MixedMean

/-! # Actual Mobius cancellation in the collected finite detector -/

set_option autoImplicit false
noncomputable section

open Finset
open Classical
open scoped ArithmeticFunction.zeta
open MathlibNt.SieveTheory.LiuWeight

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation

theorem productCoefficient_eq_divisor_sum {M N n : ℕ}
    (hn : 0 < n) (hnM : n < M) (hnN : n < N) :
    productCoefficient M N n = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) := by
  unfold productCoefficient
  apply sum_bij (fun ab _ => ab.2)
  · intro ab hab
    have he := (mem_filter.mp hab).2
    exact Nat.mem_divisors.mpr ⟨he ▸ dvd_mul_left ab.2 ab.1, hn.ne'⟩
  · intro ab hab cd hcd he
    have hb := (mem_erase.mp (mem_product.mp (mem_filter.mp hab).1).2).1
    have hp := (mem_filter.mp hab).2.trans (mem_filter.mp hcd).2.symm
    have ha : ab.1 = cd.1 := by
      rw [← he] at hp
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hb) hp
    exact Prod.ext ha he
  · intro d hd
    have hdn := (Nat.mem_divisors.mp hd).1
    have hd0 := Nat.pos_of_dvd_of_pos hdn hn
    have hdle := Nat.le_of_dvd hn hdn
    have hquot := Nat.div_pos hdle hd0
    refine ⟨(n / d, d), mem_filter.mpr ⟨?_, Nat.div_mul_cancel hdn⟩, rfl⟩
    apply mem_product.mpr
    exact ⟨mem_erase.mpr ⟨hquot.ne', mem_range.mpr ((Nat.div_le_self n d).trans_lt hnM)⟩,
      mem_erase.mpr ⟨hd0.ne', mem_range.mpr (hdle.trans_lt hnN)⟩⟩
  · intro _ _
    rfl

theorem detectorCoefficient_eq_zero_below {M N n : ℕ}
    (hn : 0 < n) (hnM : n < M) (hnN : n < N) :
    detectorCoefficient M N n = 0 := by
  have hsum := congrArg (fun a : ArithmeticFunction ℂ => a n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] at hsum
  rw [detectorCoefficient, productCoefficient_eq_divisor_sum hn hnM hnN, hsum, sub_self]

theorem critical_weight_shift {n : ℕ} (hn : 0 < n) (c : ℕ → ℂ) (sigma : ℝ) :
    ‖verticalCoefficient c sigma n‖ ^ 2 =
      ‖c n‖ ^ 2 * (n : ℝ)⁻¹ * (n : ℝ) ^ (1 - 2 * sigma) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [verticalCoefficient, norm_div, Complex.norm_natCast_cpow_of_pos hn,
    Complex.ofReal_re, div_pow]
  rw [← Real.rpow_natCast ((n : ℝ) ^ sigma) 2, ← Real.rpow_mul hnR.le,
    div_eq_mul_inv, ← Real.rpow_neg hnR.le]
  rw [← Real.rpow_neg_one, mul_assoc, ← Real.rpow_add hnR]
  congr 1
  ring

theorem detectorCoefficient_strip_energy {M N : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M) {sigma : ℝ} (hs : 1 / 2 ≤ sigma) :
    (∑ n ∈ (range (M * N + 1)).erase 0,
      ‖verticalCoefficient (detectorCoefficient M N) sigma n‖ ^ 2) ≤
        (N : ℝ) ^ (1 - 2 * sigma) * liuHarmonic (M * N) ^ 4 := by
  have hM : 2 ≤ M := hN.trans hNM
  have hset : (range (M * N + 1)).erase 0 = Icc 1 (M * N) := by
    ext n
    simp only [mem_erase, mem_range, mem_Icc]
    omega
  have hpoint :
      (∑ n ∈ (range (M * N + 1)).erase 0,
        ‖verticalCoefficient (detectorCoefficient M N) sigma n‖ ^ 2) ≤
      (N : ℝ) ^ (1 - 2 * sigma) *
        ∑ n ∈ Icc 1 (M * N), (n.divisors.card : ℝ) ^ 2 * (n : ℝ)⁻¹ := by
    rw [hset, mul_sum]
    apply sum_le_sum
    intro n hn
    have hn0 : 0 < n := (mem_Icc.mp hn).1
    by_cases hnN : n < N
    · rw [verticalCoefficient, detectorCoefficient_eq_zero_below hn0 (hnN.trans_le hNM) hnN]
      simp only [zero_div, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      positivity
    · have hNn : N ≤ n := Nat.le_of_not_gt hnN
      rw [critical_weight_shift hn0]
      have hp : (n : ℝ) ^ (1 - 2 * sigma) ≤ (N : ℝ) ^ (1 - 2 * sigma) :=
        Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (by omega : 0 < N))
          (Nat.cast_le.mpr hNn) (by linarith)
      have hc := pow_le_pow_left₀ (norm_nonneg _) (detectorCoefficient_norm_le hM hN n) 2
      have hb := mul_le_mul
        (mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr (Nat.cast_nonneg n))) hp
        (by positivity : 0 ≤ (n : ℝ) ^ (1 - 2 * sigma))
        (by positivity : 0 ≤ (n.divisors.card : ℝ) ^ 2 * (n : ℝ)⁻¹)
      exact hb.trans_eq (by ring)
  exact hpoint.trans (mul_le_mul_of_nonneg_left
    (AnalyticNumberTheory.LargeSieve.divisorSquareWeightedPrefix_le_fourth_harmonic _)
    (by positivity))

end LiuWang.Proof.NonprincipalDensityMeans.Continuation
