import LiuWang.Proof.SourceRoute.MajorOrdinary.SourceScaling

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorOrdinary

def totientWeight (q : ℕ) (s : ℝ) : ℝ :=
  |(ArithmeticFunction.moebius q : ℝ)| * (q : ℝ) ^ s / (q.totient : ℝ) ^ 2

def totientMoment (P s : ℝ) : ℝ :=
  ∑ q ∈ denominators P, totientWeight q s

def linearPrefactor : ℝ :=
  3 * (3.36 / (5 * Real.pi)) ^ (1 / 3 : ℝ) * (2.994006 / Real.pi) ^ (2 / 3 : ℝ)

def quadraticPrefactor : ℝ :=
  3 * (3.36 / (5 * Real.pi)) ^ (2 / 3 : ℝ) * (2.994006 / Real.pi) ^ (1 / 3 : ℝ)

theorem totientWeight_nonneg (q : ℕ) (s : ℝ) : 0 ≤ totientWeight q s := by
  unfold totientWeight
  positivity

theorem totientWeight_seven_sixths {q : ℕ} (hq : 0 < q) :
    totientWeight q (7 / 6) = totientWeight q (1 / 6) * (q : ℝ) := by
  have he : (7 / 6 : ℝ) = 1 / 6 + 1 := by norm_num
  rw [totientWeight, he, Real.rpow_add (Nat.cast_pos.mpr hq), Real.rpow_one, totientWeight]
  ring

theorem scaled_zeroEnvelope_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hlow : lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4) :
    sourceL N * (lowWeightSum N q + 5 * highWeightSum N q) ≤
      0.0194 + (5 * 0.0126 / sourceL N ^ 3) * (q : ℝ) := by
  have hL := sourceL_pos hN
  calc
    _ ≤ sourceL N * (0.0194 / sourceL N +
        5 * (0.0126 * (q : ℝ) / sourceL N ^ 4)) := by
      gcongr
    _ = _ := by field_simp

theorem linearCost_le_source_sums {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hlow : lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4) :
    linearCost N q ≤ linearPrefactor * (N : ℝ) ^ 2 *
      (0.0194 * totientWeight q (1 / 6) +
        (5 * 0.0126 / sourceL N ^ 3) * totientWeight q (7 / 6)) := by
  have hc : 0 ≤ linearPrefactor * (N : ℝ) ^ 2 * totientWeight q (1 / 6) := by
    exact mul_nonneg (by unfold linearPrefactor; positivity) (totientWeight_nonneg _ _)
  calc
    _ = linearPrefactor * (N : ℝ) ^ 2 * totientWeight q (1 / 6) *
        (sourceL N * (lowWeightSum N q + 5 * highWeightSum N q)) := by
      rw [linearCost_source hN]
      unfold linearPrefactor totientWeight
      ring
    _ ≤ linearPrefactor * (N : ℝ) ^ 2 * totientWeight q (1 / 6) *
        (0.0194 + (5 * 0.0126 / sourceL N ^ 3) * (q : ℝ)) :=
      mul_le_mul_of_nonneg_left (scaled_zeroEnvelope_le hN hlow hhigh) hc
    _ = _ := by rw [totientWeight_seven_sixths (NeZero.pos q)]; ring

theorem I12_source417 {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4) :
    ‖I12 N‖ ≤ linearPrefactor * (N : ℝ) ^ 2 *
      (0.0194 * totientMoment (sourceP N) (1 / 6) +
        (5 * 0.0126 / sourceL N ^ 3) * totientMoment (sourceP N) (7 / 6)) := by
  apply (I12_bound (exp_2000_le_of_exp_3100_le hN)).trans
  rw [totientMoment, totientMoment, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  exact linearCost_le_source_sums (exp_2000_le_of_exp_3100_le hN)
    (hlow q hq) (hhigh q hq)

theorem quadraticCost_le_source_sums {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hlow : lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4) :
    quadraticCost N q ≤ quadraticPrefactor * (N : ℝ) ^ 2 * totientWeight q (1 / 3) *
      (0.0194 + (5 * 0.0126 / sourceL N ^ 3) * (q : ℝ)) ^ 2 := by
  have hz : 0 ≤ sourceL N * (lowWeightSum N q + 5 * highWeightSum N q) := by
    rw [← zeroEnvelope_split]
    exact mul_nonneg (sourceL_pos hN).le (zeroEnvelope_nonneg N q)
  have hc : 0 ≤ quadraticPrefactor * (N : ℝ) ^ 2 * totientWeight q (1 / 3) := by
    exact mul_nonneg (by unfold quadraticPrefactor; positivity) (totientWeight_nonneg _ _)
  calc
    _ = quadraticPrefactor * (N : ℝ) ^ 2 * totientWeight q (1 / 3) *
        (sourceL N * (lowWeightSum N q + 5 * highWeightSum N q)) ^ 2 := by
      rw [quadraticCost_source hN]
      unfold quadraticPrefactor totientWeight
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hz (scaled_zeroEnvelope_le hN hlow hhigh) 2) hc

theorem cubicCost_le_source_sums {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hlow : lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4) :
    cubicCost N q ≤ (3.36 / (5 * Real.pi)) * (N : ℝ) ^ 2 *
      (Real.sqrt (q : ℝ) / (q.totient : ℝ) ^ 2) *
      (0.0194 + (5 * 0.0126 / sourceL N ^ 3) * (q : ℝ)) ^ 3 := by
  have hz : 0 ≤ sourceL N * (lowWeightSum N q + 5 * highWeightSum N q) := by
    rw [← zeroEnvelope_split]
    exact mul_nonneg (sourceL_pos hN).le (zeroEnvelope_nonneg N q)
  calc
    _ = (3.36 / (5 * Real.pi)) * (N : ℝ) ^ 2 *
        (Real.sqrt (q : ℝ) / (q.totient : ℝ) ^ 2) *
        (sourceL N * (lowWeightSum N q + 5 * highWeightSum N q)) ^ 3 := by
      rw [cubicCost_source hN]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hz (scaled_zeroEnvelope_le hN hlow hhigh) 3) (by positivity)

end LiuWang.Proof.SourceRoute.MajorOrdinary
