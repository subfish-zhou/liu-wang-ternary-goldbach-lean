import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.TailIntegrals

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation

theorem totientWeight_le_plain (q : ℕ) (s : ℝ) :
    totientWeight q s ≤ (q : ℝ) ^ s / (q.totient : ℝ) ^ 2 := by
  have hμ : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;> norm_num [h]
  simpa only [totientWeight, mul_div_assoc, one_mul] using
    mul_le_mul_of_nonneg_right hμ (by positivity : 0 ≤ (q : ℝ) ^ s / (q.totient : ℝ) ^ 2)

theorem totientMoment_split_le {P : ℝ} (hP : 100000 ≤ P) (s : ℝ) :
    totientMoment P s ≤ totientMoment 100000 s +
      ∑ q ∈ Finset.Icc 100001 ⌊P⌋₊, (q : ℝ) ^ s / (q.totient : ℝ) ^ 2 := by
  have hfloor : 100000 ≤ ⌊P⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hP)
  have hf : ⌊(100000 : ℝ)⌋₊ = 100000 := by norm_num
  have he : denominators P = denominators 100000 ∪ Finset.Icc 100001 ⌊P⌋₊ := by
    ext q
    simp only [denominators, hf, Finset.mem_union, Finset.mem_Icc]
    omega
  have hd : Disjoint (denominators 100000) (Finset.Icc 100001 ⌊P⌋₊) := by
    apply Finset.disjoint_left.mpr
    intro q hq hr
    simp only [denominators, hf, Finset.mem_Icc] at hq
    have := Finset.mem_Icc.mp hr
    omega
  rw [totientMoment, he, Finset.sum_union hd, totientMoment]
  exact add_le_add le_rfl (Finset.sum_le_sum (fun q _ => totientWeight_le_plain q s))

theorem source421_literal_initial_terms {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hRS : ∀ q ∈ Finset.Icc 100001 ⌊sourceP N⌋₊,
      (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    totientMoment (sourceP N) (1 / 6) ≤ totientMoment 100000 (1 / 6) +
      (∫ x in (100000 : ℝ)..10000000000, nuKernel (1 / 6) x) + 0.000000282 := by
  have hsplit := totientMoment_split_le
    ((by norm_num : (100000 : ℝ) ≤ 10000000000).trans (sourceP_ge_ten_billion hN)) (1 / 6)
  linarith [source419_comparison hN hRS, source419_tail hN]

theorem source422_literal_initial_terms {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hRS : ∀ q ∈ Finset.Icc 100001 ⌊sourceP N⌋₊,
      (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    totientMoment (sourceP N) (7 / 6) ≤ totientMoment 100000 (7 / 6) +
      (∫ x in (100000 : ℝ)..10000000000, nuKernel (7 / 6) x) +
        nu (sourceP N) ^ 2 * 6 *
          ((sourceP N) ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)) := by
  have hsplit := totientMoment_split_le
    ((by norm_num : (100000 : ℝ) ≤ 10000000000).trans (sourceP_ge_ten_billion hN)) (7 / 6)
  linarith [source422_comparison hN hRS, source422_tail hN]

theorem I12_literal_initial_terms {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4)
    (hRS : ∀ q ∈ Finset.Icc 100001 ⌊sourceP N⌋₊,
      (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    ‖I12 N‖ ≤ linearPrefactor * (N : ℝ) ^ 2 *
      (0.0194 * (totientMoment 100000 (1 / 6) +
          (∫ x in (100000 : ℝ)..10000000000, nuKernel (1 / 6) x) + 0.000000282) +
        (5 * 0.0126 / sourceL N ^ 3) *
          (totientMoment 100000 (7 / 6) +
            (∫ x in (100000 : ℝ)..10000000000, nuKernel (7 / 6) x) +
              nu (sourceP N) ^ 2 * 6 *
                ((sourceP N) ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)))) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  apply (I12_source417 hN hlow hhigh).trans
  apply mul_le_mul_of_nonneg_left _ (by unfold linearPrefactor; positivity)
  exact add_le_add
    (mul_le_mul_of_nonneg_left (source421_literal_initial_terms hN hRS) (by norm_num))
    (mul_le_mul_of_nonneg_left (source422_literal_initial_terms hN hRS) (by positivity))

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
