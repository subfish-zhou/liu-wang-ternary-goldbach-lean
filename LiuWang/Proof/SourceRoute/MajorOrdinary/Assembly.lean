import LiuWang.Proof.SourceRoute.MajorOrdinary.SourceSums
import LiuWang.Proof.SingularSeries.Decimal.Consumer
import LiuWang.Proof.PrimePowerRemoval.Main

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorArcApproximation

namespace LiuWang.Proof.SourceRoute.MajorOrdinary

def totalCost (N : ℕ) : ℝ :=
  (∑ q ∈ denominators (sourceP N), linearCost N q) +
    (∑ q ∈ denominators (sourceP N), quadraticCost N q) +
    (∑ q ∈ denominators (sourceP N), cubicCost N q)

theorem interaction_lower {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    -totalCost N ≤ (interactionIntegral N).re := by
  have h12 := Complex.re_le_norm (-I12 N)
  have h13 := Complex.re_le_norm (-I13 N)
  have h14 := Complex.re_le_norm (-I14 N)
  simp only [Complex.neg_re, norm_neg] at h12 h13 h14
  rw [interactionIntegral_split (nat_pos_of_exp_le hN), Complex.add_re, Complex.add_re]
  unfold totalCost
  linarith [I12_bound hN, I13_bound hN, I14_bound hN]

theorem majorIntegral_lower {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.656145 * (N : ℝ) ^ 2 - totalCost N -
      6760 * (N : ℝ) ^ 2 / sourceL N ^ 4 ≤ (majorIntegral N).re := by
  have h := exp_2000_le_of_exp_3100_le hN
  linarith [re_major_lower_log_power h, interaction_lower h,
    Decimal.re_I11_decimal_lower_bound hN hodd]

theorem majorIntegral_lower_decimal {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.656144999 * (N : ℝ) ^ 2 - totalCost N ≤ (majorIntegral N).re := by
  linarith [majorIntegral_lower hN hodd,
    log_power_le_decimal (exp_2000_le_of_exp_3100_le hN)]

theorem lambdaCount_lower {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.48166084 * (N : ℝ) ^ 2 - totalCost N +
      (∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re -
      6760 * (N : ℝ) ^ 2 / sourceL N ^ 4 ≤ lambdaTripleCount N := by
  linarith [CircleLowerBound.lambdaTripleCount_ge_strong hN hodd,
    interaction_lower (exp_2000_le_of_exp_3100_le hN)]

theorem primeCount_lower {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.48166084 * (N : ℝ) ^ 2 - totalCost N +
      (∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re -
      6760 * (N : ℝ) ^ 2 / sourceL N ^ 4 -
      3 * (N : ℝ) ^ (3 / 2 : ℝ) * sourceL N ^ 3 ≤ I N := by
  linarith [lambdaCount_lower hN hodd, (PrimePowerRemoval.primePowerRemoval hN).2]

theorem source425_margin {N : ℕ} {L : ℝ} (hL : 3100 ≤ L) :
    0.5437 * (N : ℝ) ^ 2 ≤
      (0.656145 - 0.1108 - 0.0016 - 0.00002) * (N : ℝ) ^ 2 -
        3 * (N : ℝ) ^ 2 / L ^ 9 := by
  have hL0 : 0 < L := by linarith
  have hp : (3100 : ℝ) ^ 9 ≤ L ^ 9 := pow_le_pow_left₀ (by norm_num) hL 9
  have he : (3 : ℝ) / L ^ 9 ≤ 0.000025 := by
    apply (div_le_iff₀ (pow_pos hL0 9)).mpr
    norm_num at hp
    linarith
  have hh := mul_le_mul_of_nonneg_right he (sq_nonneg (N : ℝ))
  rw [show (3 / L ^ 9) * (N : ℝ) ^ 2 = 3 * (N : ℝ) ^ 2 / L ^ 9 by ring] at hh
  nlinarith

end LiuWang.Proof.SourceRoute.MajorOrdinary
