import LiuWang.Proof.SingularSeries.Uniform.Tau

/-! Uniform mean bound for the real totient ratio, with a finite positive divisor majorant. -/

set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace LiuWang.Proof.SingularSeries.Uniform

def ratioSquare (q : ℕ) : ℝ := ((q : ℝ) / (q.totient : ℝ)) ^ 2

theorem ratioSquare_nonneg (q : ℕ) : 0 ≤ ratioSquare q := sq_nonneg _

theorem ratioSquare_mul {a b : ℕ} (hab : Nat.Coprime a b) :
    ratioSquare (a * b) = ratioSquare a * ratioSquare b := by
  simp only [ratioSquare, Nat.totient_mul hab, Nat.cast_mul, mul_div_mul_comm, mul_pow]

theorem ratioSquare_prime_power {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ratioSquare (p ^ k) = ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
  have hpow : p ^ k = p ^ (k - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have hn : (p : ℝ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  simp only [ratioSquare, Nat.totient_prime_pow hp hk, Nat.cast_mul,
    Nat.cast_sub hp.one_le, Nat.cast_one, Nat.cast_pow]
  rw [show (p : ℝ) ^ k = (p : ℝ) ^ (k - 1) * p by exact_mod_cast hpow]
  congr 1
  exact mul_div_mul_left _ _ hn

theorem ratioSquare_prime_le {p : ℕ} (hp : p.Prime) :
    ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 ≤ 1 + 6 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p : ℝ) := by linarith
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos hp1)]
  apply (mul_le_mul_iff_left₀ hp0).mp
  field_simp
  nlinarith [sq_nonneg ((p : ℝ) - 2)]

def majorant : ArithmeticFunction ℝ :=
  (ζ : ArithmeticFunction ℝ) *
    (tau 6).pdiv (ArithmeticFunction.id : ArithmeticFunction ℝ)

theorem majorant_apply (q : ℕ) : majorant q = ∑ d ∈ q.divisors, tau 6 d / (d : ℝ) := by
  simp only [majorant, coe_zeta_mul_apply, pdiv_apply, natCoe_apply, id_apply]

theorem majorant_nonneg (q : ℕ) : 0 ≤ majorant q := by
  rw [majorant_apply]
  exact sum_nonneg fun d _ => div_nonneg (tau_nonneg 6 d) (Nat.cast_nonneg d)

theorem majorant_multiplicative : majorant.IsMultiplicative :=
  isMultiplicative_zeta.natCast.mul
    ((tau_multiplicative 6).pdiv isMultiplicative_id.natCast)

theorem majorant_prime_power_lower {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    1 + 6 / (p : ℝ) ≤ majorant (p ^ k) := by
  rw [majorant_apply]
  have hsub : ({1, p} : Finset ℕ) ⊆ (p ^ k).divisors := by
    intro d hd
    rcases mem_insert.mp hd with rfl | hd
    · exact Nat.mem_divisors.mpr ⟨one_dvd _, pow_ne_zero _ hp.ne_zero⟩
    · have hd : d = p := mem_singleton.mp hd
      subst d
      exact Nat.mem_divisors.mpr ⟨dvd_pow_self _ hk.ne', pow_ne_zero _ hp.ne_zero⟩
  have h := sum_le_sum_of_subset_of_nonneg (f := fun d => tau 6 d / (d : ℝ)) hsub
    (fun d _ _ => div_nonneg (tau_nonneg 6 d) (Nat.cast_nonneg d))
  simpa [tau_one, tau_prime 6 hp, hp.ne_one.symm] using h

theorem ratioSquare_le_majorant (q : ℕ) : ratioSquare q ≤ majorant q := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => simp [ratioSquare]
  | one => simp [ratioSquare, majorant_multiplicative.map_one]
  | prime_pow p k hp hk =>
    rw [ratioSquare_prime_power hp hk]
    exact ratioSquare_prime_le hp |>.trans (majorant_prime_power_lower hp hk)
  | coprime a b _ _ hab ha hb =>
    rw [ratioSquare_mul hab, majorant_multiplicative.map_mul_of_coprime hab]
    exact mul_le_mul ha hb (ratioSquare_nonneg _) (majorant_nonneg _)

theorem ratioSquare_sum_le (X : ℕ) :
    (∑ q ∈ Icc 1 X, ((q : ℝ) / (q.totient : ℝ)) ^ 2) ≤ 22 * (X : ℝ) := by
  calc
    _ ≤ ∑ q ∈ Icc 1 X, majorant q := sum_le_sum fun q _ => ratioSquare_le_majorant q
    _ = ∑ q ∈ Icc 1 X, ∑ d ∈ q.divisors, tau 6 d / (d : ℝ) := by
      simp only [majorant_apply]
    _ ≤ (X : ℝ) * squareSum (tau 6) X := sum_divisor_quotient_le (tau_nonneg 6) X
    _ ≤ (X : ℝ) * 22 := mul_le_mul_of_nonneg_left (squareSum_tau_six_lt X).le (Nat.cast_nonneg X)
    _ = _ := by ring

theorem ratioSquare_sum_real_le {P : ℝ} (hP : 0 ≤ P) :
    (∑ q ∈ denominators P, ((q : ℝ) / (q.totient : ℝ)) ^ 2) ≤ 22 * P := by
  exact (ratioSquare_sum_le ⌊P⌋₊).trans
    (mul_le_mul_of_nonneg_left (Nat.floor_le hP) (by norm_num))

theorem weightedTotientSum_le {P : ℝ} (hP : 0 ≤ P) :
    weightedTotientSum P ≤ 22 * P := by
  calc
    _ ≤ ∑ q ∈ denominators P, ((q : ℝ) / (q.totient : ℝ)) ^ 2 := by
      apply sum_le_sum
      intro q _
      have hμ : |(moebius q : ℝ)| ≤ 1 := by
        rcases moebius_eq_or q with h | h | h <;> rw [h] <;> norm_num
      have h := mul_le_mul_of_nonneg_right hμ
        (by positivity : 0 ≤ (q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2)
      simpa only [div_pow, one_mul, ← mul_div_assoc] using h
    _ ≤ _ := ratioSquare_sum_real_le hP

end LiuWang.Proof.SingularSeries.Uniform
