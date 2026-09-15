import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# 原文 (6.20) 的有限筛权

筛掉 4 的倍数后，对十五个奇素数的平方使用二阶 Bonferroni 上界。
这只是固定的筛权；被筛整数和区间端点没有上界。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds.ContinuationHelpers

open scoped BigOperators

def sievePrimes : Finset Nat :=
  {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53}

theorem sievePrimes_card : sievePrimes.card = 15 := by decide

theorem sievePrimes_prime {p : Nat} (hp : p ∈ sievePrimes) : p.Prime := by
  simp only [sievePrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def dvdIndicator (d n : Nat) : Real := if d ∣ n then 1 else 0

theorem dvdIndicator_mul (d e n : Nat) :
    dvdIndicator d n * dvdIndicator e n = dvdIndicator (Nat.lcm d e) n := by
  by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;>
    simp [dvdIndicator, Nat.lcm_dvd_iff, hd, he]

def oddSquareIndicator (d n : Nat) : Real :=
  dvdIndicator d n - dvdIndicator (Nat.lcm 4 d) n

theorem oddSquareIndicator_eq (d n : Nat) :
    oddSquareIndicator d n = (1 - dvdIndicator 4 n) * dvdIndicator d n := by
  rw [oddSquareIndicator, ← dvdIndicator_mul]
  ring

def sieveForm (f : Nat → Real) : Real :=
  f 1 - 3 / 2 * (∑ p ∈ sievePrimes, f (p ^ 2)) +
    1 / 2 * ∑ p ∈ sievePrimes, ∑ q ∈ sievePrimes, f (Nat.lcm (p ^ 2) (q ^ 2))

theorem sieveForm_indicator_eq (n : Nat) :
    sieveForm (fun d => oddSquareIndicator d n) =
      (1 - dvdIndicator 4 n) *
        (1 - 3 / 2 * (∑ p ∈ sievePrimes, dvdIndicator (p ^ 2) n) +
          1 / 2 * (∑ p ∈ sievePrimes, dvdIndicator (p ^ 2) n) ^ 2) := by
  simp only [sieveForm, oddSquareIndicator_eq, ← dvdIndicator_mul]
  simp only [dvdIndicator, one_dvd, ite_true]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem sieveForm_indicator_nonneg (n : Nat) :
    0 ≤ sieveForm (fun d => oddSquareIndicator d n) := by
  rw [sieveForm_indicator_eq]
  apply mul_nonneg
  · simp only [dvdIndicator]
    split_ifs <;> norm_num
  · let k := (sievePrimes.filter (fun p => p ^ 2 ∣ n)).card
    have hk : (∑ p ∈ sievePrimes, dvdIndicator (p ^ 2) n) = (k : Real) := by
      simp only [k, dvdIndicator, Finset.card_filter, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [hk]
    rcases k with _ | _ | k
    · norm_num
    · norm_num
    · push_cast
      nlinarith [sq_nonneg (k : Real), Nat.cast_nonneg (α := Real) k]

theorem abs_moebius_le_sieveForm (n : Nat) :
    |(ArithmeticFunction.moebius n : Real)| ≤
      sieveForm (fun d => oddSquareIndicator d n) := by
  by_cases hn : Squarefree n
  · have h4 : ¬4 ∣ n := by
      simpa using (Nat.squarefree_iff_prime_squarefree.mp hn 2 Nat.prime_two)
    have hp : ∀ p ∈ sievePrimes, dvdIndicator (p ^ 2) n = 0 := by
      intro p hp
      have h := Nat.squarefree_iff_prime_squarefree.mp hn p (sievePrimes_prime hp)
      simpa [dvdIndicator, pow_two] using h
    have hm : |(ArithmeticFunction.moebius n : Real)| = 1 := by
      rw [← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree hn]
      norm_num
    rw [hm, sieveForm_indicator_eq, Finset.sum_eq_zero hp]
    simp [dvdIndicator, h4]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
    simpa using sieveForm_indicator_nonneg n

theorem sum_sieveForm {α : Type*} (s : Finset α) (f : α → Nat → Real) :
    (∑ n ∈ s, sieveForm (f n)) = sieveForm (fun d => ∑ n ∈ s, f n d) := by
  simp only [sieveForm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]
  congr 2
  · exact Finset.sum_comm
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    exact Finset.sum_comm

def oddDensity (d : Nat) : Real := 1 / (d : Real) - 1 / (Nat.lcm 4 d : Real)

theorem sieveForm_le {f : Nat → Real} {M : Real}
    (hlo : ∀ d : Nat, 0 < d → M * oddDensity d - 2 ≤ f d)
    (hhi : ∀ d : Nat, 0 < d → f d ≤ M * oddDensity d + 2) :
    sieveForm f ≤ M * sieveForm oddDensity + 272 := by
  have hfirst := hhi 1 (by norm_num)
  have hsingle :
      M * (∑ p ∈ sievePrimes, oddDensity (p ^ 2)) - 30 ≤
        ∑ p ∈ sievePrimes, f (p ^ 2) := by
    have h := Finset.sum_le_sum (s := sievePrimes) fun p hp =>
      hlo (p ^ 2) (pow_pos (sievePrimes_prime hp).pos _)
    norm_num [Finset.sum_sub_distrib, ← Finset.mul_sum, sievePrimes_card] at h ⊢
    exact h
  have hdouble :
      (∑ p ∈ sievePrimes, ∑ q ∈ sievePrimes, f (Nat.lcm (p ^ 2) (q ^ 2))) ≤
        M * (∑ p ∈ sievePrimes, ∑ q ∈ sievePrimes,
          oddDensity (Nat.lcm (p ^ 2) (q ^ 2))) + 450 := by
    have h := Finset.sum_le_sum (s := sievePrimes) fun p hp =>
      Finset.sum_le_sum (s := sievePrimes) fun q hq =>
        hhi (Nat.lcm (p ^ 2) (q ^ 2))
          (Nat.lcm_pos (pow_pos (sievePrimes_prime hp).pos _)
            (pow_pos (sievePrimes_prime hq).pos _))
    norm_num [Finset.sum_add_distrib, ← Finset.mul_sum, sievePrimes_card] at h ⊢
    exact h
  dsimp [sieveForm]
  nlinarith

end LiuWang.Proof.ArithmeticBounds.ContinuationHelpers
