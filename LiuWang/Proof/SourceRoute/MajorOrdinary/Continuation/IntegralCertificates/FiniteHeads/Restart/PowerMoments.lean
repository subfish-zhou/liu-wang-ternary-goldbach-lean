import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.MeanBound
import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.SumIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
noncomputable section
open Finset Set MeasureTheory
open LiuWang.Proof.SingularSeries LiuWang.Proof.SingularSeries.Uniform

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart

theorem weighted_mean_comparison (w : ℕ → ℝ) {m B : ℕ} (hm : 1 ≤ m) (hB : m ≤ B)
    (hw : 0 ≤ w B) (hdec : ∀ k, m ≤ k → k < B → w (k + 1) ≤ w k) :
    (∑ q ∈ Finset.Icc m B, ratioSquare q * w q) ≤
      10.3 * (m : ℝ) * w m + 10.3 * ∑ q ∈ Finset.Icc (m + 1) B, w q := by
  have hc := weighted_sum_le_of_prefix_le ratioSquare
    (fun q => comparisonSequence m q * (10.3 / 22)) w hB (by
      intro k hmk _
      rw [← Finset.sum_mul, comparisonSequence_sum hmk]
      have h := (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc hm le_rfl)
        (fun q _ _ => ratioSquare_nonneg q)).trans (ratioSquare_sum_le_ten_point_three k)
      convert! h using 1
      ring) hw hdec
  have he :
      (∑ q ∈ Finset.Icc m B, comparisonSequence m q * (10.3 / 22) * w q) =
        (∑ q ∈ Finset.Icc m B, comparisonSequence m q * w q) * (10.3 / 22) := by
    rw [Finset.sum_mul]
    congr 1
    funext q
    ring
  rw [he, comparisonSequence_weighted_sum w hB] at hc
  convert! hc using 1
  ring

theorem power_sum_le_integral {e : ℝ} (he : e ≤ 0) {m B : ℕ}
    (hm : 0 < m) (hB : m ≤ B) :
    (∑ q ∈ Finset.Icc (m + 1) B, (q : ℝ) ^ e) ≤ ∫ x in (m : ℝ)..B, x ^ e := by
  rw [sum_Icc_shift]
  have hh : AntitoneOn (fun x : ℝ => x ^ e) (Set.Icc (m : ℝ) B) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos
      ((Nat.cast_pos.mpr hm).trans_le hx.1) hxy he
  simpa only [Nat.cast_add, Nat.cast_one] using hh.sum_le_integral_Ico hB

theorem power_tail_sum {e : ℝ} (he : e < -1) {m B : ℕ} (hm : 0 < m) :
    (∑ q ∈ Finset.Icc (m + 1) B, (q : ℝ) ^ e) ≤
      (m : ℝ) ^ (e + 1) / (-(e + 1)) := by
  by_cases hB : m ≤ B
  · apply (power_sum_le_integral (by linarith) hm hB).trans
    rw [integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le (Nat.cast_le.mpr hB)]
      intro h
      have := h.1
      have : (0 : ℝ) < m := Nat.cast_pos.mpr hm
      linarith⟩)]
    have hnon : 0 ≤ (B : ℝ) ^ (e + 1) := Real.rpow_nonneg (Nat.cast_nonneg B) _
    have he0 : 0 < -(e + 1) := by linarith
    calc
      _ = ((m : ℝ) ^ (e + 1) - (B : ℝ) ^ (e + 1)) / (-(e + 1)) := by
        rw [div_neg]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (sub_le_self _ hnon) he0.le
  · rw [Finset.Icc_eq_empty_of_lt (by omega), sum_empty]
    exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _) (by linarith)

theorem unweighted_term_eq_ratio {q : ℕ} (hq : 0 < q) (s : ℝ) :
    (q : ℝ) ^ s / (q.totient : ℝ) ^ 2 = ratioSquare q * (q : ℝ) ^ (s - 2) := by
  have hq0 : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  rw [ratioSquare, Real.rpow_sub hq0, Real.rpow_ofNat, div_pow]
  field_simp

theorem totient_weight_le_unweighted (q : ℕ) (s : ℝ) :
    totientWeight q s ≤ (q : ℝ) ^ s / (q.totient : ℝ) ^ 2 := by
  have hmu : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;> rw [h] <;> norm_num
  unfold totientWeight
  simpa only [one_mul, mul_div_assoc] using
    mul_le_mul_of_nonneg_right hmu (by positivity : 0 ≤ (q : ℝ) ^ s / (q.totient : ℝ) ^ 2)

theorem unweighted_tail_le {s : ℝ} (hs : s < 1) {m B : ℕ} (hm : 1 ≤ m) :
    (∑ q ∈ Finset.Icc m B, (q : ℝ) ^ s / (q.totient : ℝ) ^ 2) ≤
      10.3 * (1 + 1 / (1 - s)) * (m : ℝ) ^ (s - 1) := by
  by_cases hB : m ≤ B
  · have h := weighted_mean_comparison (fun q => (q : ℝ) ^ (s - 2)) hm hB
      (by positivity) (by
        intro k hmk _
        exact Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr (by omega))
          (Nat.cast_le.mpr (by omega)) (by linarith))
    have he : (m : ℝ) * (m : ℝ) ^ (s - 2) = (m : ℝ) ^ (s - 1) := by
      calc
        _ = (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ (s - 2) := by rw [Real.rpow_one]
        _ = (m : ℝ) ^ (1 + (s - 2)) :=
          (Real.rpow_add (Nat.cast_pos.mpr (by omega : 0 < m)) _ _).symm
        _ = _ := by congr 1; ring
    have ht := power_tail_sum (show s - 2 < -1 by linarith) (m := m) (B := B) (by omega)
    rw [show s - 2 + 1 = s - 1 by ring, show -(s - 1) = 1 - s by ring] at ht
    have heq :
        (∑ q ∈ Finset.Icc m B, (q : ℝ) ^ s / (q.totient : ℝ) ^ 2) =
          ∑ q ∈ Finset.Icc m B, ratioSquare q * (q : ℝ) ^ (s - 2) := by
      apply sum_congr rfl
      intro q hq
      exact unweighted_term_eq_ratio (by have := (Finset.mem_Icc.mp hq).1; omega) s
    rw [heq]
    calc
      _ ≤ 10.3 * (m : ℝ) * (m : ℝ) ^ (s - 2) +
          10.3 * ∑ q ∈ Finset.Icc (m + 1) B, (q : ℝ) ^ (s - 2) := h
      _ ≤ 10.3 * (m : ℝ) ^ (s - 1) + 10.3 * ((m : ℝ) ^ (s - 1) / (1 - s)) := by
        rw [mul_assoc, he]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left ht (by norm_num))
      _ = _ := by ring
  · rw [Finset.Icc_eq_empty_of_lt (by omega), sum_empty]
    have : 0 < 1 - s := by linarith
    positivity

theorem unweighted_high_prefix {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) {B : ℕ}
    (hB : 1 ≤ B) :
    (∑ q ∈ Finset.Icc 1 B, (q : ℝ) ^ s / (q.totient : ℝ) ^ 2) ≤
      10.3 * (1 + (B : ℝ) ^ (s - 1) / (s - 1)) := by
  have h := weighted_mean_comparison (fun q => (q : ℝ) ^ (s - 2)) (by norm_num) hB
    (by positivity) (by
      intro k hk _
      exact Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr hk)
        (Nat.cast_le.mpr (by omega)) (by linarith))
  have hp := power_sum_le_integral (show s - 2 ≤ 0 by linarith) (by norm_num : 0 < (1 : ℕ)) hB
  rw [integral_rpow (Or.inl (by linarith))] at hp
  norm_num only [Nat.cast_one, Real.one_rpow, show s - 2 + 1 = s - 1 by ring] at h hp
  have heq :
      (∑ q ∈ Finset.Icc 1 B, (q : ℝ) ^ s / (q.totient : ℝ) ^ 2) =
        ∑ q ∈ Finset.Icc 1 B, ratioSquare q * (q : ℝ) ^ (s - 2) :=
    sum_congr rfl fun q hq => unweighted_term_eq_ratio (Finset.mem_Icc.mp hq).1 s
  rw [heq]
  have hs0 : 0 < s - 1 := by linarith
  have hd := div_le_div_of_nonneg_right
    (sub_le_self ((B : ℝ) ^ (s - 1)) (by norm_num : (0 : ℝ) ≤ 1)) hs0.le
  nlinarith [hp.trans hd]

theorem unweighted_large_prefix {s P : ℝ} (hs : 2 ≤ s) (hP : 0 ≤ P) :
    (∑ q ∈ denominators P, (q : ℝ) ^ s / (q.totient : ℝ) ^ 2) ≤
      10.3 * P ^ (s - 1) := by
  by_cases hP0 : P = 0
  · subst P
    simp only [denominators, Nat.floor_zero, Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1),
      sum_empty]
    positivity
  have hp : 0 < P := lt_of_le_of_ne hP (Ne.symm hP0)
  calc
    _ ≤ ∑ q ∈ denominators P, ratioSquare q * P ^ (s - 2) := by
      apply sum_le_sum
      intro q hq
      rw [unweighted_term_eq_ratio (Finset.mem_Icc.mp hq).1]
      apply mul_le_mul_of_nonneg_left _ (ratioSquare_nonneg q)
      exact Real.rpow_le_rpow (Nat.cast_nonneg q)
        ((Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2).trans (Nat.floor_le hP)) (by linarith)
    _ = (∑ q ∈ denominators P, ratioSquare q) * P ^ (s - 2) := (sum_mul ..).symm
    _ ≤ (10.3 * P) * P ^ (s - 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (ratioSquare_sum_le_ten_point_three ⌊P⌋₊).trans
        (mul_le_mul_of_nonneg_left (Nat.floor_le hP) (by norm_num))
    _ = _ := by
      rw [mul_assoc]
      congr 1
      calc
        _ = P ^ (1 : ℝ) * P ^ (s - 2) := by rw [Real.rpow_one]
        _ = P ^ (1 + (s - 2)) := (Real.rpow_add hp _ _).symm
        _ = _ := by congr 1; ring

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart
