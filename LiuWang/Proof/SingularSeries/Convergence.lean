import LiuWang.Proof.SingularSeries.Ramanujan
import Mathlib.Analysis.PSeries

/-!
# Absolute convergence for positive source integers

The elementary estimate `q ≤ 2 φ(q)^2` and the integer Ramanujan formula
give a summable `q^(-3/2)` majorant for each fixed positive `N`.
This is not the uniform real-cutoff estimate needed in (4.7).
-/

set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction

namespace LiuWang.Proof.SingularSeries

def parityFactor (n : ℕ) : ℕ := if 2 ∣ n then 2 else 1

theorem parityFactor_mul {a b : ℕ} (hab : Nat.Coprime a b) :
    parityFactor (a * b) = parityFactor a * parityFactor b := by
  have hn : ¬ (2 ∣ a ∧ 2 ∣ b) := by
    rintro ⟨ha, hb⟩
    have : 2 ∣ 1 := hab ▸ Nat.dvd_gcd ha hb
    norm_num at this
  unfold parityFactor
  simp only [Nat.prime_two.dvd_mul]
  split_ifs <;> simp_all

theorem parityFactor_pow {p k : ℕ} (hk : 0 < k) :
    parityFactor (p ^ k) = parityFactor p := by
  have hd : 2 ∣ p ^ k ↔ 2 ∣ p :=
    ⟨Nat.prime_two.dvd_of_dvd_pow, fun h => dvd_pow h hk.ne'⟩
  simp only [parityFactor, hd]

theorem prime_le_parityFactor_mul_sub_sq {p : ℕ} (hp : p.Prime) :
    p ≤ parityFactor p * (p - 1) ^ 2 := by
  by_cases h2 : p = 2
  · subst p
    norm_num [parityFactor]
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hd : ¬ 2 ∣ p := by
      intro h
      exact h2 ((hp.eq_one_or_self_of_dvd 2 h).resolve_left (by decide)).symm
    simp only [parityFactor, if_neg hd, one_mul]
    have he := Nat.sub_add_cancel hp.one_le
    nlinarith

theorem le_parityFactor_mul_totient_sq (n : ℕ) :
    n ≤ parityFactor n * n.totient ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp [parityFactor]
  | prime_pow p k hp hk =>
    rw [parityFactor_pow hk, Nat.totient_prime_pow hp hk]
    have he : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ]
      congr 1
      omega
    rw [he]
    have hbase := prime_le_parityFactor_mul_sub_sq hp
    have hx : 1 ≤ p ^ (k - 1) := Nat.one_le_pow _ _ hp.pos
    calc
      _ ≤ p ^ (k - 1) * (parityFactor p * (p - 1) ^ 2) :=
        Nat.mul_le_mul_left _ hbase
      _ ≤ parityFactor p * (p ^ (k - 1) * (p - 1)) ^ 2 := by
        have hx2 : p ^ (k - 1) ≤ (p ^ (k - 1)) ^ 2 := by nlinarith
        nlinarith [Nat.mul_le_mul_right (parityFactor p * (p - 1) ^ 2) hx2]
  | coprime a b _ _ hab ha hb =>
    rw [parityFactor_mul hab, Nat.totient_mul hab]
    have h := Nat.mul_le_mul ha hb
    nlinarith only [h]

theorem le_two_mul_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 := by
  have hc : parityFactor n ≤ 2 := by unfold parityFactor; split_ifs <;> norm_num
  exact (le_parityFactor_mul_totient_sq n).trans (Nat.mul_le_mul_right _ hc)

def divisorMass (N : ℕ) : ℝ := ∑ d ∈ N.divisors, (d : ℝ)

theorem divisorMass_nonneg (N : ℕ) : 0 ≤ divisorMass N :=
  sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem norm_moebius_complex_le (q : ℕ) : ‖(moebius q : ℂ)‖ ≤ 1 := by
  rcases moebius_eq_or q with h | h | h <;> rw [h] <;> norm_num

theorem ramanujan_integer_formula' (N q : ℕ) :
    ramanujan N q =
      ∑ d ∈ q.divisors,
        (if d ∣ N then (d : ℂ) else 0) * (moebius (q / d) : ℂ) := by
  rw [ramanujan_eq_arithmetic]
  simp only [ramanujanArithmetic, mul_comm moebius, mul_apply, divisorWeight_apply]
  push_cast
  exact Nat.sum_divisorsAntidiagonal (fun d e =>
    (if d ∣ N then (d : ℂ) else 0) * (moebius e : ℂ))

theorem norm_ramanujan_le_divisorMass {N : ℕ} (hN : 0 < N) (q : ℕ) :
    ‖ramanujan N q‖ ≤ divisorMass N := by
  rw [ramanujan_integer_formula']
  calc
    _ ≤ ∑ d ∈ q.divisors,
        ‖(if d ∣ N then (d : ℂ) else 0) * (moebius (q / d) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ q.divisors, if d ∣ N then (d : ℝ) else 0 := by
      apply sum_le_sum
      intro d _
      split_ifs
      · simpa only [norm_mul, Complex.norm_natCast, mul_one] using
          mul_le_mul_of_nonneg_left (norm_moebius_complex_le (q / d)) (Nat.cast_nonneg d)
      · simp
    _ = ∑ d ∈ q.divisors.filter (fun d => d ∣ N), (d : ℝ) := (sum_filter ..).symm
    _ ≤ divisorMass N := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2, hN.ne'⟩
      · intros
        positivity

theorem inv_totient_cube_le {q : ℕ} (hq : 0 < q) :
    1 / (q.totient : ℝ) ^ 3 ≤
      (2 : ℝ) ^ (3 / 2 : ℝ) / (q : ℝ) ^ (3 / 2 : ℝ) := by
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have h : (q : ℝ) ≤ 2 * (q.totient : ℝ) ^ 2 := by
    exact_mod_cast le_two_mul_totient_sq q
  have hh := Real.rpow_le_rpow (Nat.cast_nonneg q) h (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  rw [Real.mul_rpow (by norm_num) (sq_nonneg _)] at hh
  have he : ((q.totient : ℝ) ^ 2) ^ (3 / 2 : ℝ) = (q.totient : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hφ.le]
    norm_num
  rw [he] at hh
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa using hh

theorem norm_coefficient_le_fixed_majorant {N : ℕ} (hN : 0 < N) (q : ℕ) :
    ‖coefficient N q‖ ≤
      (divisorMass N * (2 : ℝ) ^ (3 / 2 : ℝ)) *
        (1 / (q : ℝ) ^ (3 / 2 : ℝ)) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hφ : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
  rw [coefficient, if_neg hq, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ (1 / (q.totient : ℝ) ^ 3) * divisorMass N :=
      mul_le_mul
        (div_le_div_of_nonneg_right (norm_moebius_complex_le q) (by positivity))
        (norm_ramanujan_le_divisorMass hN q) (norm_nonneg _) (by positivity)
    _ ≤ ((2 : ℝ) ^ (3 / 2 : ℝ) / (q : ℝ) ^ (3 / 2 : ℝ)) * divisorMass N :=
      mul_le_mul_of_nonneg_right (inv_totient_cube_le (Nat.pos_of_ne_zero hq))
        (divisorMass_nonneg N)
    _ = _ := by ring

theorem coefficient_norm_summable {N : ℕ} (hN : 0 < N) :
    Summable (fun q : ℕ => ‖coefficient N q‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_coefficient_le_fixed_majorant hN)
  exact (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2)).mul_left _

theorem coefficient_summable {N : ℕ} (hN : 0 < N) : Summable (coefficient N) :=
  (coefficient_norm_summable hN).of_norm

end LiuWang.Proof.SingularSeries
