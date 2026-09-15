import LiuWang.Proof.SingularSeries.Uniform.Abel
import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.ExpandedMoments

set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta
open LiuWang.Proof.SingularSeries
open LiuWang.Proof.SingularSeries.Uniform

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart

def majorantFour : ArithmeticFunction ℝ :=
  (ζ : ArithmeticFunction ℝ) * (tau 4).pdiv (ArithmeticFunction.id : ArithmeticFunction ℝ)

theorem majorantFour_apply (q : ℕ) :
    majorantFour q = ∑ d ∈ q.divisors, tau 4 d / (d : ℝ) := by
  simp only [majorantFour, coe_zeta_mul_apply, pdiv_apply, natCoe_apply, id_apply]

theorem majorantFour_nonneg (q : ℕ) : 0 ≤ majorantFour q := by
  rw [majorantFour_apply]
  exact sum_nonneg fun d _ => div_nonneg (tau_nonneg 4 d) (Nat.cast_nonneg d)

theorem majorantFour_multiplicative : majorantFour.IsMultiplicative :=
  isMultiplicative_zeta.natCast.mul
    ((tau_multiplicative 4).pdiv isMultiplicative_id.natCast)

theorem majorantFour_prime_power {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    1 + 4 / (p : ℝ) ≤ majorantFour (p ^ k) := by
  rw [majorantFour_apply]
  have hsub : ({1, p} : Finset ℕ) ⊆ (p ^ k).divisors := by
    intro d hd
    rcases mem_insert.mp hd with rfl | hd
    · exact Nat.mem_divisors.mpr ⟨one_dvd _, pow_ne_zero _ hp.ne_zero⟩
    · have hd : d = p := mem_singleton.mp hd
      subst d
      exact Nat.mem_divisors.mpr ⟨dvd_pow_self _ hk.ne', pow_ne_zero _ hp.ne_zero⟩
  have h := sum_le_sum_of_subset_of_nonneg (f := fun d => tau 4 d / (d : ℝ)) hsub
    (fun d _ _ => div_nonneg (tau_nonneg 4 d) (Nat.cast_nonneg d))
  simpa [tau_one, tau_prime 4 hp, hp.ne_one.symm] using h

def twoCorrection (q : ℕ) : ℝ := if 2 ∣ q then 4 / 3 else 1

theorem twoCorrection_bounds (q : ℕ) : 1 ≤ twoCorrection q ∧ twoCorrection q ≤ 4 / 3 := by
  unfold twoCorrection
  split_ifs <;> norm_num

theorem twoCorrection_mul {a b : ℕ} (hab : a.Coprime b) :
    twoCorrection (a * b) = twoCorrection a * twoCorrection b := by
  have hnot : ¬ (2 ∣ a ∧ 2 ∣ b) := by
    rintro ⟨ha, hb⟩
    have h := Nat.dvd_gcd ha hb
    rw [hab.gcd_eq_one] at h
    norm_num at h
  simp only [twoCorrection, Nat.prime_two.dvd_mul]
  by_cases ha : 2 ∣ a
  · by_cases hb : 2 ∣ b
    · exact False.elim (hnot ⟨ha, hb⟩)
    · simp only [ha, hb, true_or, if_true, if_false, mul_one]
  · by_cases hb : 2 ∣ b
    · simp only [ha, hb, or_true, if_true, if_false, one_mul]
    · simp only [ha, hb, false_or, if_false, one_mul]

theorem prime_ratio_square_le_four {p : ℕ} (hp : 3 ≤ p) :
    ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 ≤ 1 + 4 / (p : ℝ) := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : 0 < (p : ℝ) := by linarith
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos hp1)]
  apply (mul_le_mul_iff_left₀ hp0).mp
  field_simp
  nlinarith [sq_nonneg ((p : ℝ) - 3)]

theorem ratioSquare_le_four (q : ℕ) :
    ratioSquare q ≤ majorantFour q * twoCorrection q := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => simp [ratioSquare, majorantFour]
  | one => simp [ratioSquare, majorantFour_multiplicative.map_one, twoCorrection]
  | prime_pow p k hp hk =>
    rw [ratioSquare_prime_power hp hk]
    by_cases hp2 : p = 2
    · subst p
      have hd : 2 ∣ 2 ^ k := dvd_pow_self _ hk.ne'
      have hm := majorantFour_prime_power Nat.prime_two hk
      simp only [twoCorrection, if_pos hd]
      norm_num at hm ⊢
      linarith
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      exact (prime_ratio_square_le_four hp3).trans
        ((majorantFour_prime_power hp hk).trans
          (le_mul_of_one_le_right (majorantFour_nonneg _) (twoCorrection_bounds _).1))
  | coprime a b _ _ hab ha hb =>
    rw [ratioSquare_mul hab, majorantFour_multiplicative.map_mul_of_coprime hab,
      twoCorrection_mul hab]
    convert! mul_le_mul ha hb (ratioSquare_nonneg b)
      (mul_nonneg (majorantFour_nonneg a) (by linarith [(twoCorrection_bounds a).1])) using 1
    ring

theorem ratioSquare_sum_le_ten_point_three (X : ℕ) :
    (∑ q ∈ Icc 1 X, ratioSquare q) ≤ 10.3 * (X : ℝ) := by
  calc
    _ ≤ ∑ q ∈ Icc 1 X, majorantFour q * (4 / 3) := by
      apply sum_le_sum
      intro q _
      exact (ratioSquare_le_four q).trans
        (mul_le_mul_of_nonneg_left (twoCorrection_bounds q).2 (majorantFour_nonneg q))
    _ = (∑ q ∈ Icc 1 X, ∑ d ∈ q.divisors, tau 4 d / (d : ℝ)) * (4 / 3) := by
      rw [← sum_mul]
      simp only [majorantFour_apply]
    _ ≤ ((X : ℝ) * squareSum (tau 4) X) * (4 / 3) :=
      mul_le_mul_of_nonneg_right (sum_divisor_quotient_le (tau_nonneg 4) X) (by norm_num)
    _ ≤ ((X : ℝ) * (5 / 3 : ℝ) ^ 4) * (4 / 3) := by
      gcongr
      exact squareSum_tau_le 4 X
    _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) X]

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart
