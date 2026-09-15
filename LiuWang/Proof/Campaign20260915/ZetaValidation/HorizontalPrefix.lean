import LiuWang.Proof.Campaign20260915.ZetaValidation.HorizontalBlock0
import LiuWang.Proof.Campaign20260915.ZetaValidation.HorizontalBlock1
import LiuWang.Proof.Campaign20260915.ZetaValidation.HorizontalBlock2
import LiuWang.Proof.Campaign20260915.ZetaValidation.HorizontalBlock3
import LiuWang.Proof.Campaign20260915.ZetaValidation.HorizontalBlock4
import LiuWang.Proof.Campaign20260915.ZetaValidation.HorizontalBlock5
import LiuWang.Proof.Campaign20260915.ZetaValidation.HorizontalBlock6
import LiuWang.Proof.Campaign20260915.ZetaValidation.HorizontalBlock7

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable section
open Complex Finset

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem horizontal_coefficient_real {j : ℕ} (hj : j < 64) :
    (horizontalCoefficient j : ℝ) ≤ (((j + 1 : ℕ) : ℂ) ^ (-criticalPoint 16)).re := by
  have hrat : horizontalCoefficient j + 1 / 1000 ≤ (power16Center (j + 1)).1 := by
    have hr : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have hq : j / 8 < 8 := by omega
    have hb (b : ℕ) (hb : b < 8) (k : ℕ) (hk : k < 8) :
        horizontalCoefficient (b * 8 + k) + 1 / 1000 ≤ (power16Center (b * 8 + k + 1)).1 := by
      interval_cases b <;> norm_num only [Nat.reduceMul, zero_add]
      · exact horizontal_coeff0 k hk
      · exact horizontal_coeff1 k hk
      · exact horizontal_coeff2 k hk
      · exact horizontal_coeff3 k hk
      · exact horizontal_coeff4 k hk
      · exact horizontal_coeff5 k hk
      · exact horizontal_coeff6 k hk
      · exact horizontal_coeff7 k hk
    have h := hb (j / 8) hq (j % 8) hr
    have he : j / 8 * 8 + j % 8 = j := by omega
    rw [he] at h
    exact h
  have hc : (horizontalCoefficient j : ℝ) + 1 / 1000 ≤ ((power16Center (j + 1)).1 : ℝ) := by
    have h := Rat.cast_le (K := ℝ) |>.mpr hrat
    norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at h
    exact h
  have herr := power16Center_error (n := j + 1) (by omega) (by omega)
  have hre := (abs_re_le_norm
    (((j + 1 : ℕ) : ℂ) ^ (-criticalPoint 16) - (power16Center (j + 1)).toComplex)).trans herr
  simp only [sub_re, QComplex.toComplex, add_re, ratCast_re, mul_re, I_re, mul_zero,
    ratCast_im, I_im, zero_mul, sub_zero, add_zero] at hre
  linarith [(abs_le.mp hre).1]

private def prefixRational : ℕ → ℚ
  | 0 => 0
  | n + 1 => prefixRational n + horizontalCoefficient n

theorem horizontal_prefix_rational {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 64) :
    (1 / 3 : ℚ) ≤ ∑ j ∈ range n, horizontalCoefficient j := by
  have hP (n : ℕ) : prefixRational n = ∑ j ∈ range n, horizontalCoefficient j := by
    induction n with
    | zero => simp [prefixRational]
    | succ n ih => simp only [prefixRational, sum_range_succ, ih]
  have h : ∀ k : Fin 64, (1 / 3 : ℚ) ≤
      prefixRational (k.val + 1) := by decide +kernel
  have hh := h ⟨n - 1, by omega⟩
  dsimp only at hh
  rw [Nat.sub_add_cancel hn, hP] at hh
  exact hh

theorem horizontal_prefix_real {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 64) :
    (1 / 3 : ℝ) ≤ (zetaPartialSum (criticalPoint 16) n).re := by
  have h := horizontal_prefix_rational hn hN
  have hc : (1 / 3 : ℝ) ≤ ∑ j ∈ range n, (horizontalCoefficient j : ℝ) := by
    have hc := Rat.cast_le (K := ℝ) |>.mpr h
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_sum] using hc
  apply hc.trans
  rw [zetaPartialSum, re_sum]
  apply sum_le_sum
  intro j hj
  simpa only [Nat.cast_add, Nat.cast_one] using
    horizontal_coefficient_real (j := j) (lt_of_lt_of_le (mem_range.mp hj) hN)

theorem horizontal_tail_phase :
    ((64 : ℂ) ^ (-criticalPoint 16)).re < 0 ∧
      0 < ((64 : ℂ) ^ (-criticalPoint 16)).im := by
  have hr : ((power16Center 64).1 : ℝ) ≤ -1 / 100 := by
    have h := Rat.cast_le (K := ℝ) |>.mpr horizontal_tail_phase_rational.1
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] at h
    linarith
  have hi : (1 / 100 : ℝ) ≤ ((power16Center 64).2 : ℝ) := by
    have h := Rat.cast_le (K := ℝ) |>.mpr horizontal_tail_phase_rational.2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    exact h
  have he := power16Center_error (n := 64) (by norm_num) (by norm_num)
  have hre := (abs_re_le_norm ((64 : ℂ) ^ (-criticalPoint 16) - (power16Center 64).toComplex)).trans he
  have him := (abs_im_le_norm ((64 : ℂ) ^ (-criticalPoint 16) - (power16Center 64).toComplex)).trans he
  simp [QComplex.toComplex] at hre him
  constructor <;> linarith [(abs_le.mp hre).2, (abs_le.mp him).1]

#print axioms horizontal_prefix_real
#print axioms horizontal_tail_phase

end LiuWang.Proof.Campaign20260915.ZetaValidation
