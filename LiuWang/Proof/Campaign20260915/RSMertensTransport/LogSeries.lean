import LiuWang.Proof.Campaign20260915.RSMertensTransport.RealTransport
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
noncomputable section

open AnalyticNumberTheory.Mertens
open Finset

namespace LiuWang.Proof.Campaign20260915.RSMertensTransport

theorem hasSum_logarithmicCorrection_prime {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => (1 / (p : ℝ)) ^ (k + 2) / (k + 2))
      (logarithmicCorrectionTerm p) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have ht : |1 / (p : ℝ)| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact (div_lt_one (by positivity)).mpr hp1
  have hs := (hasSum_nat_add_iff' 1).mpr
    (Real.hasSum_pow_div_log_of_abs_lt_one ht)
  simpa [logarithmicCorrectionTerm, hp, Finset.sum_range_one,
    Nat.add_assoc, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using hs

theorem logarithmicCorrection_prime_le {p : ℕ} (hp : p.Prime) :
    logarithmicCorrectionTerm p ≤ 1 / (2 * (p : ℝ) * (p - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have ht0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have ht1 : 1 / (p : ℝ) < 1 := (div_lt_one hp0).mpr hp1
  have hgeo := (hasSum_geometric_of_lt_one ht0 ht1).mul_left
    ((1 / (p : ℝ)) ^ 2 / 2)
  have hpoint (k : ℕ) :
      (1 / (p : ℝ)) ^ (k + 2) / (k + 2) ≤
        ((1 / (p : ℝ)) ^ 2 / 2) * (1 / (p : ℝ)) ^ k := by
    calc
      _ ≤ (1 / (p : ℝ)) ^ (k + 2) / 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      _ = _ := by rw [pow_add]; ring
  have hs := (hasSum_logarithmicCorrection_prime hp).summable.tsum_le_tsum
    hpoint hgeo.summable
  rw [(hasSum_logarithmicCorrection_prime hp).tsum_eq, hgeo.tsum_eq] at hs
  calc
    logarithmicCorrectionTerm p ≤
        ((1 / (p : ℝ)) ^ 2 / 2) * (1 - 1 / (p : ℝ))⁻¹ := hs
    _ = 1 / (2 * (p : ℝ) * (p - 1)) := by field_simp

theorem logarithmicCorrection_prime_le_weighted_square {x : ℝ} (hx : 1 < x)
    {p : ℕ} (hp : p.Prime) (hxp : x < (p : ℝ)) :
    logarithmicCorrectionTerm p ≤
      (x / (2 * (x - 1) * Real.log x)) * (Real.log p / (p : ℝ) ^ 2) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm : 0 < (p : ℝ) - 1 := by linarith
  have hxm : 0 < x - 1 := by linarith
  have hxl : 0 < Real.log x := Real.log_pos hx
  have hl : Real.log x ≤ Real.log p :=
    Real.log_le_log (by linarith) hxp.le
  apply (logarithmicCorrection_prime_le hp).trans
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < (p : ℝ) ^ 2)).mpr
    (show (1 / (2 * (p : ℝ) * (p - 1))) * (p : ℝ) ^ 2 ≤
      (x / (2 * (x - 1) * Real.log x)) * Real.log p from ?_)
  have hratio : (p : ℝ) / (p - 1) ≤ x / (x - 1) := by
    apply (div_le_div_iff₀ hpm hxm).mpr
    nlinarith
  calc
    1 / (2 * (p : ℝ) * (p - 1)) * (p : ℝ) ^ 2 =
        ((p : ℝ) / (p - 1)) / 2 := by field_simp
    _ ≤ (x / (x - 1)) / 2 := div_le_div_of_nonneg_right hratio (by norm_num)
    _ = (x / (2 * (x - 1) * Real.log x)) * Real.log x := by field_simp
    _ ≤ (x / (2 * (x - 1) * Real.log x)) * Real.log p :=
      mul_le_mul_of_nonneg_left hl (by positivity)

#print axioms hasSum_logarithmicCorrection_prime
#print axioms logarithmicCorrection_prime_le
#print axioms logarithmicCorrection_prime_le_weighted_square

end LiuWang.Proof.Campaign20260915.RSMertensTransport
