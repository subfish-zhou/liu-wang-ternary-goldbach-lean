import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate.Cells
import Mathlib.Data.Rat.Floor

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate

def taylorQ (x : ℚ) : ℚ := ∑ k ∈ Finset.range 8, x ^ k / (k.factorial : ℚ)

def expUpperQ (x : ℚ) : ℚ :=
  1 / ((27182818283 / 10000000000 : ℚ) ^ ⌊x⌋₊ * taylorQ (x - ⌊x⌋₊))

theorem exp_upperQ {x : ℚ} (hx : 0 ≤ x) :
    Real.exp (-(x : ℝ)) ≤ (expUpperQ x : ℝ) := by
  have hdq : 0 ≤ x - (⌊x⌋₊ : ℚ) := sub_nonneg.mpr (Nat.floor_le hx)
  have hd : 0 ≤ (x : ℝ) - (⌊x⌋₊ : ℝ) := by exact_mod_cast hdq
  have ht := Real.sum_le_exp_of_nonneg hd 8
  have ht0 : 1 ≤ (taylorQ (x - ⌊x⌋₊) : ℝ) := by
    have h := Finset.single_le_sum (f := fun k : ℕ =>
      ((x : ℝ) - (⌊x⌋₊ : ℝ)) ^ k / (k.factorial : ℝ))
      (fun k _ => by positivity) (by decide : 0 ∈ Finset.range 8)
    simpa [taylorQ] using h
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le ⌊x⌋₊
  rw [← Real.exp_nat_mul, mul_one] at hpow
  have hh := mul_le_mul hpow ht (by positivity) (Real.exp_pos _).le
  rw [← Real.exp_add, add_sub_cancel] at hh
  have htcast :
      (taylorQ (x - ⌊x⌋₊) : ℝ) =
        ∑ k ∈ Finset.range 8, ((x : ℝ) - (⌊x⌋₊ : ℝ)) ^ k / (k.factorial : ℝ) := by
    simp [taylorQ]
  rw [← htcast] at hh
  unfold expUpperQ
  push_cast
  rw [Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le
    (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 27182818283 / 10000000000) _)
      (lt_of_lt_of_le zero_lt_one ht0))
  convert hh using 1
  norm_num

def qA (v : ℚ) : ℚ := 17102 * (3100 / (3100 - 4 * v)) * (677 / 100) + 16541
def qB (v : ℚ) : ℚ := 254231 * (3100 / (3100 - 4 * v)) * (677 / 100)
def qSlope (u v : ℚ) : ℚ :=
  5 / ((u + v) / 2) + qA v / (qA v * ((u + v) / 2) + qB v) +
    (7409 / 5) / ((u + v) / 2) ^ (2 : ℕ) - 1
def qMass (u v : ℚ) : ℚ :=
  3100 ^ (4 : ℕ) * ((u + v) / 2) ^ (5 : ℕ) * (qA v * ((u + v) / 2) + qB v)
def qPhase (u v s : ℚ) : ℚ :=
  -(u + v) / 2 - (7409 / 5) / ((u + v) / 2) + qSlope u v * (s - (u + v) / 2)
def rationalCell (u v : ℚ) : ℚ :=
  (v - u) / 2 * qMass u v * (expUpperQ (-qPhase u v u) + expUpperQ (-qPhase u v v))

theorem cast_qMass (u v : ℚ) : (qMass u v : ℝ) = cellMass u v := by
  norm_num [qMass, qA, qB, cellMass, coeffA, coeffB]

theorem cast_qPhase (u v s : ℚ) : (qPhase u v s : ℝ) = cellPhase u v s := by
  norm_num [qPhase, qSlope, qA, qB, cellPhase, cellSlope, phase, coeffA, coeffB]
  ring

theorem cell_le_rational {u v : ℚ} (hu : 0 < u) (huv : u < v) (hv : v ≤ 100)
    (hpu : qPhase u v u ≤ 0) (hpv : qPhase u v v ≤ 0) :
    (∫ s in (u : ℝ)..(v : ℝ), integrand 3100 s) ≤ (rationalCell u v : ℝ) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have huvR : (u : ℝ) < v := by exact_mod_cast huv
  have hvR : (v : ℝ) ≤ 100 := by exact_mod_cast hv
  have h1 := exp_upperQ (neg_nonneg.mpr hpu)
  have h2 := exp_upperQ (neg_nonneg.mpr hpv)
  simp only [Rat.cast_neg, neg_neg, cast_qPhase] at h1 h2
  apply (cell_integral_upper huR huvR hvR).trans
  unfold cellBound rationalCell
  push_cast
  rw [cast_qMass]
  apply mul_le_mul_of_nonneg_left (add_le_add h1 h2)
  have hd : 0 < 3100 - 4 * (v : ℝ) := by linarith
  have hm : 0 < ((u : ℝ) + v) / 2 := by linarith
  unfold cellMass coeffA coeffB
  positivity

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate
