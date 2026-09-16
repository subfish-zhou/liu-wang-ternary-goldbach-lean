import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesBlock00
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesBlock01
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesBlock02
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesBlock03
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesBlock04
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesBlock05
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesBlock06
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesBlock07

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem threeHalves_prefix_lower :
    (12436253 / 5000000 : ℝ) ≤
      ∑ n ∈ Finset.range 256, (n : ℝ) ^ (-3 / 2 : ℝ) := by
  have hp : (167100227 / 100000000 : ℝ) ≤
      ∑ n ∈ Finset.range 5, (n : ℝ) ^ (-3 / 2 : ℝ) := by
    have h1 := threeHalves_row_1.1
    have h2 := threeHalves_row_2.1
    have h3 := threeHalves_row_3.1
    have h4 := threeHalves_row_4.1
    norm_num [Finset.sum_range_succ] at *
    linarith
  have h0 := ThreeHalvesBlock00_lower
  have h1 := ThreeHalvesBlock01_lower
  have h2 := ThreeHalvesBlock02_lower
  have h3 := ThreeHalvesBlock03_lower
  have h4 := ThreeHalvesBlock04_lower
  have h5 := ThreeHalvesBlock05_lower
  have h6 := ThreeHalvesBlock06_lower
  have h7 := ThreeHalvesBlock07_lower
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 5 ≤ 37)] at h0
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 37 ≤ 69)] at h1
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 69 ≤ 101)] at h2
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 101 ≤ 133)] at h3
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 133 ≤ 165)] at h4
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 165 ≤ 197)] at h5
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 197 ≤ 229)] at h6
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 229 ≤ 256)] at h7
  linarith

theorem logPower_prefix_upper :
    (∑ n ∈ Finset.range 256, logPowerTerm n) ≤ (298841689 / 100000000 : ℝ) := by
  have hp : (∑ n ∈ Finset.range 5, logPowerTerm n) ≤ (62977959 / 100000000 : ℝ) := by
    have h1 := threeHalves_row_1.2
    have h2 := threeHalves_row_2.2
    have h3 := threeHalves_row_3.2
    have h4 := threeHalves_row_4.2
    have hz : logPowerTerm 0 = 0 := by simp [logPowerTerm]
    norm_num [Finset.sum_range_succ, hz]
    linarith
  have h0 := ThreeHalvesBlock00_upper
  have h1 := ThreeHalvesBlock01_upper
  have h2 := ThreeHalvesBlock02_upper
  have h3 := ThreeHalvesBlock03_upper
  have h4 := ThreeHalvesBlock04_upper
  have h5 := ThreeHalvesBlock05_upper
  have h6 := ThreeHalvesBlock06_upper
  have h7 := ThreeHalvesBlock07_upper
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 5 ≤ 37)] at h0
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 37 ≤ 69)] at h1
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 69 ≤ 101)] at h2
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 101 ≤ 133)] at h3
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 133 ≤ 165)] at h4
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 165 ≤ 197)] at h5
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 197 ≤ 229)] at h6
  rw [Finset.sum_Ico_eq_sub _ (by norm_num : 229 ≤ 256)] at h7
  linarith

theorem threeHalves_denominator_lower :
    (13061253 / 5000000 : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ) := by
  have h := rpow_three_halves_sum_lower (by norm_num : 1 ≤ 256)
  norm_num only [Nat.cast_ofNat] at h
  have hp := threeHalves_prefix_lower
  simp only [neg_div] at hp ⊢
  linarith

theorem norm_zeta_threeHalves_lower :
    (13061253 / 5000000 : ℝ) ≤ ‖riemannZeta (3 / 2 : ℂ)‖ := by
  have h := norm_zeta_real_eq_rpow_sum (by norm_num : (1 : ℝ) < 3 / 2)
  norm_num only [ofReal_div, ofReal_ofNat] at h
  rw [h]
  simpa only [neg_div] using threeHalves_denominator_lower

theorem logPower_tail_255_upper :
    (2 * Real.log 255 + 4) * (255 : ℝ) ^ (-1 / 2 : ℝ) ≤
      (16 * (6931471808 / 10000000000 : ℝ) + 4) / (1996 / 125) := by
  have hs : (1996 / 125 : ℝ) ≤ Real.sqrt 255 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 255), Real.sqrt_nonneg 255]
  have hl : Real.log (255 : ℝ) ≤ 8 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 255)
      (by norm_num : (255 : ℝ) ≤ 2 ^ (8 : ℕ))
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hu : 2 * Real.log (255 : ℝ) + 4 ≤
      16 * (6931471808 / 10000000000 : ℝ) + 4 := by
    linarith [Real.log_two_lt_d9]
  rw [neg_div, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 255), ← Real.sqrt_eq_rpow,
    ← div_eq_mul_inv]
  exact (div_le_div_of_nonneg_right hu (Real.sqrt_nonneg 255)).trans
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs)

theorem logPower_numerator_upper :
    (∑' n : ℕ, logPowerTerm n) ≤ (196279361851 / 49900000000 : ℝ) := by
  have h := logPowerTerm_sum_upper (by norm_num : 4 ≤ 255)
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at h
  linarith [logPower_prefix_upper, logPower_tail_255_upper]

theorem real_logDeriv_threeHalves_upper :
    -(logDeriv riemannZeta (3 / 2 : ℂ)).re ≤ (753 / 500 : ℝ) := by
  have hd := threeHalves_denominator_lower
  have hn := logPower_numerator_upper
  have h := neg_logDeriv_real_le_series_ratio (by norm_num : (1 : ℝ) < 3 / 2)
  norm_num only [ofReal_div, ofReal_ofNat] at h
  simp only [logPowerTerm, neg_div] at hn hd
  have hp : 0 < ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) := by linarith
  refine h.trans ((div_le_div_of_nonneg_right hn hp.le).trans ?_)
  refine (div_le_div_of_nonneg_left
    (by norm_num : (0 : ℝ) ≤ 196279361851 / 49900000000)
    (by norm_num : (0 : ℝ) < 13061253 / 5000000) hd).trans ?_
  norm_num

#print axioms norm_zeta_threeHalves_lower
#print axioms logPower_numerator_upper
#print axioms real_logDeriv_threeHalves_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
