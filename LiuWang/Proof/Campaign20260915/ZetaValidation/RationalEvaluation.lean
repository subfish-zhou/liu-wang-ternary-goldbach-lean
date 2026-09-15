import LiuWang.Proof.Campaign20260915.ZetaValidation.NormalizedEvaluation
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def reciprocalSqrtLower (n D : ℕ) : ℚ :=
  (D : ℚ) / (Nat.sqrt (n * D ^ 2) + 1)

def reciprocalSqrtUpper (n D : ℕ) : ℚ :=
  (D : ℚ) / Nat.sqrt (n * D ^ 2)

theorem reciprocalSqrt_enclosure {n D : ℕ} (hn : 1 ≤ n) (hD : 1 ≤ D) :
    (reciprocalSqrtLower n D : ℝ) ≤ 1 / Real.sqrt (n : ℝ) ∧
      1 / Real.sqrt (n : ℝ) ≤ (reciprocalSqrtUpper n D : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hkN : 0 < Nat.sqrt (n * D ^ 2) := by
    rw [Nat.sqrt_pos]
    exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hn)
      (pow_pos (lt_of_lt_of_le Nat.zero_lt_one hD) _)
  have hk : (0 : ℝ) < Nat.sqrt (n * D ^ 2) := by exact_mod_cast hkN
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have he : Real.sqrt (n * D ^ 2 : ℕ) = Real.sqrt (n : ℝ) * (D : ℝ) := by
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (Nat.cast_nonneg D)]
  have hlo := Real.nat_sqrt_le_real_sqrt (a := n * D ^ 2)
  have hhi := Real.real_sqrt_lt_nat_sqrt_succ (a := n * D ^ 2)
  rw [he] at hlo hhi
  constructor
  · change (((D : ℚ) / (Nat.sqrt (n * D ^ 2) + 1) : ℚ) : ℝ) ≤ _
    push_cast
    apply (div_le_div_iff₀ (by positivity) hs).2
    nlinarith
  · change _ ≤ (((D : ℚ) / Nat.sqrt (n * D ^ 2) : ℚ) : ℝ)
    push_cast
    apply (div_le_div_iff₀ hs hk).2
    nlinarith

def halfZetaLower (m D : ℕ) : ℚ :=
  (∑ j ∈ Finset.range (m ^ 2), reciprocalSqrtLower (j + 1) D) -
    2 * (m : ℚ) - 1 / m

def halfZetaUpper (m D : ℕ) : ℚ :=
  (∑ j ∈ Finset.range (m ^ 2), reciprocalSqrtUpper (j + 1) D) -
    2 * (m : ℚ)

noncomputable section

open Complex

theorem cpow_neg_half_of_nat {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) ^ (-(1 / 2 : ℂ)) = ((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) := by
  have hnR : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le 1).trans hn
  have h := Complex.ofReal_cpow hnR (-(1 / 2 : ℝ))
  push_cast at h
  rw [← h, Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, one_div]

theorem abelApprox_half_re {N : ℕ} (hN : 1 ≤ N) :
    (abelApprox (criticalPoint 0) N).re =
      (∑ j ∈ Finset.range N, 1 / Real.sqrt (j + 1 : ℝ)) -
        2 * Real.sqrt (N : ℝ) - 1 / (2 * Real.sqrt (N : ℝ)) := by
  have hp : criticalPoint 0 = ((1 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> norm_num [criticalPoint]
  have hpos : (N : ℂ) ^ (1 - criticalPoint 0) = (Real.sqrt (N : ℝ) : ℂ) := by
    rw [hp]
    convert (Complex.ofReal_cpow (Nat.cast_nonneg N) (1 / 2 : ℝ)).symm using 1 <;>
      norm_num [Real.sqrt_eq_rpow]
  have hneg : (N : ℂ) ^ (-criticalPoint 0) =
      ((1 / Real.sqrt (N : ℝ) : ℝ) : ℂ) := by
    simpa [hp] using cpow_neg_half_of_nat hN
  have hsum : zetaPartialSum (criticalPoint 0) N =
      ((∑ j ∈ Finset.range N, 1 / Real.sqrt (j + 1 : ℝ) : ℝ) : ℂ) := by
    unfold zetaPartialSum
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    simpa [hp] using cpow_neg_half_of_nat (n := j + 1) (by omega)
  rw [abelApprox, hpos, hneg, hsum, hp]
  rw [show (((1 / 2 : ℝ) : ℂ) - 1) = ((-1 / 2 : ℝ) : ℂ) by norm_num,
    ← ofReal_div, ← ofReal_add, ← ofReal_ofNat 2, ← ofReal_div,
    ← ofReal_sub, ofReal_re]
  ring

theorem halfZeta_rational_enclosure {m D : ℕ} (hm : 1 ≤ m) (hD : 1 ≤ D) :
    (halfZetaLower m D : ℝ) ≤ normalizedCriticalZeta 0 ∧
      normalizedCriticalZeta 0 ≤ (halfZetaUpper m D : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hN : 1 ≤ m ^ 2 := by exact pow_pos (lt_of_lt_of_le Nat.zero_lt_one hm) _
  have he := normalized_abel_error 0 hN
  rw [criticalGammaPhase_zero, mul_one, abelApprox_half_re hN] at he
  have hp : criticalPoint 0 = ((1 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> norm_num [criticalPoint]
  have hs : Real.sqrt (m ^ 2 : ℕ) = (m : ℝ) := by
    push_cast
    exact Real.sqrt_sq hmR.le
  rw [Real.rpow_neg (Nat.cast_nonneg (m ^ 2)), ← Real.sqrt_eq_rpow, hs, hp] at he
  norm_num at he
  have hl :
      (∑ j ∈ Finset.range (m ^ 2), (reciprocalSqrtLower (j + 1) D : ℝ)) ≤
        ∑ j ∈ Finset.range (m ^ 2), 1 / Real.sqrt (j + 1 : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact_mod_cast (reciprocalSqrt_enclosure (n := j + 1) (by omega) hD).1
  have hu :
      (∑ j ∈ Finset.range (m ^ 2), 1 / Real.sqrt (j + 1 : ℝ)) ≤
        ∑ j ∈ Finset.range (m ^ 2), (reciprocalSqrtUpper (j + 1) D : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact_mod_cast (reciprocalSqrt_enclosure (n := j + 1) (by omega) hD).2
  have hei := abs_le.mp he
  dsimp [halfZetaLower, halfZetaUpper]
  push_cast
  simp only [one_div] at hl hu ⊢
  constructor <;> linarith [hei.1, hei.2]

theorem endpoint_zero_refined_enclosure :
    -(8 / 5 : ℝ) ≤ normalizedCriticalZeta 0 ∧ normalizedCriticalZeta 0 ≤ -(13 / 10) := by
  have h := halfZeta_rational_enclosure (m := 4) (D := 1000) (by norm_num) (by norm_num)
  have hl : -(8 / 5 : ℚ) ≤ halfZetaLower 4 1000 := by
    norm_num [halfZetaLower, reciprocalSqrtLower, Finset.sum_range_succ]
  have hu : halfZetaUpper 4 1000 ≤ -(13 / 10 : ℚ) := by
    norm_num [halfZetaUpper, reciprocalSqrtUpper, Finset.sum_range_succ]
  have hlR : ((-(8 / 5) : ℚ) : ℝ) ≤ (halfZetaLower 4 1000 : ℝ) := Rat.cast_le.mpr hl
  have huR : (halfZetaUpper 4 1000 : ℝ) ≤ ((-(13 / 10) : ℚ) : ℝ) := Rat.cast_le.mpr hu
  norm_num at hlR huR
  exact ⟨hlR.trans h.1, h.2.trans huR⟩

#print axioms halfZeta_rational_enclosure
#print axioms endpoint_zero_refined_enclosure

end

end LiuWang.Proof.Campaign20260915.ZetaValidation
