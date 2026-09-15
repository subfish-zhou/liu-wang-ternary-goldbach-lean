import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Consumers

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1

theorem source419_real_tail {P : ℝ} (hP : 10000000000 ≤ P)
    (hRS : ∀ q : ℕ, 3 ≤ q → (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    (∑ q ∈ Finset.Icc 100001 ⌊P⌋₊,
      (q : ℝ) ^ (1 / 6 : ℝ) / (q.totient : ℝ) ^ 2) ≤ 0.0025 + 0.000000282 := by
  have h := totient_tail_le_source_integral (by norm_num : (1 / 6 : ℝ) ≤ 7 / 6)
    (by linarith : 100000 ≤ P) (fun q hq =>
      hRS q (by have := (Finset.mem_Icc.mp hq).1; omega))
  rw [source_integral_split hP] at h
  linarith only [h, low_nuKernel_integral, low_finite_tail_le hP]

theorem source422_real_tail {P : ℝ} (hP : 10000000000 ≤ P)
    (hRS : ∀ q : ℕ, 3 ≤ q → (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    (∑ q ∈ Finset.Icc 100001 ⌊P⌋₊,
      (q : ℝ) ^ (7 / 6 : ℝ) / (q.totient : ℝ) ^ 2) ≤
      8794 + 6 * nu P ^ 2 * (P ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)) := by
  have h := totient_tail_le_source_integral (s := 7 / 6) le_rfl
    (by linarith : 100000 ≤ P) (fun q hq =>
      hRS q (by have := (Finset.mem_Icc.mp hq).1; omega))
  rw [source_integral_split hP] at h
  linarith only [h, high_nuKernel_integral, high_finite_tail_le hP]

theorem source421_real_cutoff {P : ℝ} (hP : 10000000000 ≤ P)
    (hRS : ∀ q : ℕ, 3 ≤ q → (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    totientMoment P (1 / 6) ≤ 3.2868 := by
  linarith only [totientMoment_split_le (by linarith : 100000 ≤ P) (1 / 6),
    original_first_head, source419_real_tail hP hRS]

theorem source422_real_cutoff {P : ℝ} (hP : 10000000000 ≤ P)
    (hRS : ∀ q : ℕ, 3 ≤ q → (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    totientMoment P (7 / 6) ≤
      8864 + 6 * nu P ^ 2 * (P ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)) := by
  linarith only [totientMoment_split_le (by linarith : 100000 ≤ P) (7 / 6),
    original_second_head, source422_real_tail hP hRS]

theorem source423_scalar_real_cutoff {P : ℝ} (hP : 10000000000 ≤ P) :
    linearPrefactor *
      (0.0194 * 3.2868 + (5 * 0.0126 / P) *
        (8864 + 6 * nu P ^ 2 *
          (P ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)))) ≤ 0.1108 := by
  have hP0 : 0 < P := by linarith
  have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 8864)
    (by norm_num : (0 : ℝ) < 10000000000) hP
  have ht := high_tail_div_P_le hP
  have hinner :
      0.0194 * 3.2868 + (5 * 0.0126 / P) *
        (8864 + 6 * nu P ^ 2 * (P ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ))) ≤
      0.0194 * 3.2868 + 0.063 * (8864 / 10000000000 + 6 / 5280000) := by
    calc
      _ = 0.0194 * 3.2868 + 0.063 *
          (8864 / P + 6 * (nu P ^ 2 *
            (P ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)) / P)) := by ring
      _ ≤ _ := by linarith
  calc
    _ ≤ linearPrefactor *
        (0.0194 * 3.2868 + 0.063 * (8864 / 10000000000 + 6 / 5280000)) :=
      mul_le_mul_of_nonneg_left hinner (by unfold linearPrefactor; positivity)
    _ ≤ 1.7376 *
        (0.0194 * 3.2868 + 0.063 * (8864 / 10000000000 + 6 / 5280000)) :=
      mul_le_mul_of_nonneg_right linearPrefactor_le (by norm_num)
    _ ≤ _ := by norm_num

theorem source423_arithmetic {L : ℝ} (hL : 3100 ≤ L)
    (hRS : ∀ q : ℕ, 3 ≤ q → (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    linearPrefactor *
      (0.0194 * totientMoment (L ^ 3) (1 / 6) +
        (5 * 0.0126 / L ^ 3) * totientMoment (L ^ 3) (7 / 6)) ≤ 0.1108 := by
  have hL0 : 0 < L := by linarith
  have hP : (10000000000 : ℝ) ≤ L ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) hL 3
    norm_num at h
    linarith
  apply le_trans _ (source423_scalar_real_cutoff hP)
  apply mul_le_mul_of_nonneg_left _ (by unfold linearPrefactor; positivity)
  exact add_le_add
    (mul_le_mul_of_nonneg_left (source421_real_cutoff hP hRS) (by norm_num))
    (mul_le_mul_of_nonneg_left (source422_real_cutoff hP hRS) (by positivity))

theorem I12_original_arithmetic_consumer {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4)
    (hRS : ∀ q : ℕ, 3 ≤ q → (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    ‖I12 N‖ ≤ 0.1108 * (N : ℝ) ^ 2 := by
  have ha := mul_le_mul_of_nonneg_right
    (source423_arithmetic (sourceL_ge_3100 hN) hRS) (sq_nonneg (N : ℝ))
  have hi := I12_source417 hN hlow hhigh
  change linearPrefactor * (0.0194 * totientMoment (sourceP N) (1 / 6) +
    (5 * 0.0126 / sourceL N ^ 3) * totientMoment (sourceP N) (7 / 6)) *
      (N : ℝ) ^ 2 ≤ _ at ha
  nlinarith only [hi, ha]

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1
