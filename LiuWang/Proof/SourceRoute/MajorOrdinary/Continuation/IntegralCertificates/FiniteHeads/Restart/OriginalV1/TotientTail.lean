import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1.NuDomain
import LiuWang.Proof.ArithmeticBounds.Main

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1

theorem small_totient_ratios {P : ℝ} (hP : 3 ≤ P) :
    (1 : ℝ) / (Nat.totient 1 : ℝ) ≤ nu P ∧
      (2 : ℝ) / (Nat.totient 2 : ℝ) ≤ nu P := by
  have h := two_le_nu hP
  norm_num
  constructor <;> linarith

theorem totient_ratio_le_nu_cutoff {P : ℝ} {q : ℕ}
    (hq : 27 ≤ q) (hqP : (q : ℝ) ≤ P)
    (hRS : ∀ n : ℕ, 3 ≤ n → (n : ℝ) / (n.totient : ℝ) ≤ nu n) :
    (q : ℝ) / (q.totient : ℝ) ≤ nu P := by
  have hqR : (27 : ℝ) ≤ q := by exact_mod_cast hq
  exact (hRS q (by omega)).trans (nu_monotone_27 hqR (hqR.trans hqP) hqP)

theorem weighted_totient_tail {P : ℝ} (hP : 1000 ≤ P)
    (hRS : ∀ q : ℕ, 3 ≤ q → (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    (∑ q ∈ Finset.Icc 1001 ⌊P⌋₊,
      |(ArithmeticFunction.moebius q : ℝ)| * (q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) ≤
      (P - 1000) * nu P ^ 2 := by
  have hP0 : 0 ≤ P := by linarith
  have hf : 1000 ≤ ⌊P⌋₊ :=
    (Nat.le_floor_iff hP0).mpr (by exact_mod_cast hP)
  have hc : ((Finset.Icc 1001 ⌊P⌋₊).card : ℝ) = (⌊P⌋₊ : ℝ) - 1000 := by
    rw [Nat.card_Icc, show ⌊P⌋₊ + 1 - 1001 = ⌊P⌋₊ - 1000 by omega,
      Nat.cast_sub hf, Nat.cast_ofNat]
  calc
    _ ≤ ∑ _q ∈ Finset.Icc 1001 ⌊P⌋₊, nu P ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' := Finset.mem_Icc.mp hq
      have hqP : (q : ℝ) ≤ P := (Nat.le_floor_iff hP0).mp hq'.2
      have hr := totient_ratio_le_nu_cutoff (by omega : 27 ≤ q) hqP hRS
      have hmu : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;> norm_num [h]
      have hrs : ((q : ℝ) / (q.totient : ℝ)) ^ 2 ≤ nu P ^ 2 :=
        pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg q.totient)) hr 2
      calc
        _ = |(ArithmeticFunction.moebius q : ℝ)| *
            ((q : ℝ) / (q.totient : ℝ)) ^ 2 := by rw [div_pow]; ring
        _ ≤ 1 * nu P ^ 2 :=
          mul_le_mul hmu hrs (sq_nonneg _) (by norm_num)
        _ = _ := one_mul _
    _ = ((⌊P⌋₊ : ℝ) - 1000) * nu P ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, hc]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (sub_le_sub_right (Nat.floor_le hP0) 1000) (sq_nonneg _)

theorem weighted_totient_sum_split {P : ℝ} (hP : 1000 ≤ P) :
    weightedTotientSum P =
      weightedTotientSum 1000 +
        ∑ q ∈ Finset.Icc 1001 ⌊P⌋₊,
          |(ArithmeticFunction.moebius q : ℝ)| * (q : ℝ) ^ 2 /
            (q.totient : ℝ) ^ 2 := by
  have hf : 1000 ≤ ⌊P⌋₊ :=
    (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hP)
  have he : denominators P = denominators 1000 ∪ Finset.Icc 1001 ⌊P⌋₊ := by
    ext q
    norm_num only [denominators, Nat.floor_ofNat, Finset.mem_union, Finset.mem_Icc]
    omega
  have hd : Disjoint (denominators 1000) (Finset.Icc 1001 ⌊P⌋₊) := by
    apply Finset.disjoint_left.mpr
    intro q hq hr
    norm_num only [denominators, Nat.floor_ofNat, Finset.mem_Icc] at hq
    have := Finset.mem_Icc.mp hr
    omega
  rw [weightedTotientSum, he, Finset.sum_union hd, weightedTotientSum]

theorem weighted_totient_sum_original {P : ℝ} (hP : 1000 ≤ P)
    (hRS : ∀ q : ℕ, 3 ≤ q → (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    weightedTotientSum P ≤ 1961 + (P - 1000) * nu P ^ 2 ∧
      1961 + (P - 1000) * nu P ^ 2 ≤ P * nu P ^ 2 := by
  have hh : weightedTotientSum 1000 ≤ 1961 := by
    simpa only [weightedTotientSum, denominators, Nat.floor_ofNat] using
      LiuWang.Proof.ArithmeticBounds.sum_moebius_totient_square_le_1961
  constructor
  · rw [weighted_totient_sum_split hP]
    exact add_le_add hh (weighted_totient_tail hP hRS)
  · have hn := two_le_nu (by linarith : 3 ≤ P)
    nlinarith [sq_nonneg (nu P - 2)]

theorem R14_bound {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hRS : ∀ q : ℕ, 3 ≤ q → (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    ‖arcError N‖ ≤ 2.82 * (N : ℝ) ^ 2 / sourceP N * nu (sourceP N) ^ 2 := by
  have hP := sourceP_ge_ten_billion hN
  have hP0 : 0 < sourceP N := by linarith
  have hw := weighted_totient_sum_original (by linarith : 1000 ≤ sourceP N) hRS
  calc
    _ ≤ 2.82 * (N : ℝ) ^ 2 / sourceP N ^ 2 * weightedTotientSum (sourceP N) :=
      arcError_bound hN
    _ ≤ 2.82 * (N : ℝ) ^ 2 / sourceP N ^ 2 *
        (sourceP N * nu (sourceP N) ^ 2) :=
      mul_le_mul_of_nonneg_left (hw.1.trans hw.2) (by positivity)
    _ = _ := by field_simp

theorem I11_source46_with_R14 {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hRS : ∀ q : ℕ, 3 ≤ q → (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    I11 N = (partialSeries N (sourceP N) : ℂ) *
        (∫ eta : ℝ, cubeIntegrand N eta) + (-arcError N) ∧
      ‖-arcError N‖ ≤ 2.82 * (N : ℝ) ^ 2 / sourceP N * nu (sourceP N) ^ 2 := by
  constructor
  · rw [integral_cube_eq_fullMass (nat_pos_of_exp_le hN),
      I11_eq_partial_main_sub_arcError (nat_pos_of_exp_le hN)]
    ring
  · simpa only [norm_neg] using R14_bound hN hRS

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1
