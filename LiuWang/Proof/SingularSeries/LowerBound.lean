import LiuWang.Proof.SingularSeries.MainTerm
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries

/-!
# A uniform positive lower bound and a finite-certificate admission interface

Only the generic universal product over odd primes is reused from the
older sieve file. Neither of its sieve-normalized singular series is used.
The equality below exposes the exact common product.

The finite-certificate theorem is a reduction, not a proof of its finite
premise. No prime enumeration is performed in this module.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped Topology
open MathlibNt.SieveTheory.SingularSeries

namespace LiuWang.Proof.SingularSeries

def universalProduct : ℝ := liuUniversalProduct

def universalTruncated (z : ℕ) : ℝ := liuUniversalProductTruncated z

theorem universalProduct_source :
    universalProduct = ∏' p : ℕ,
      if p.Prime ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 := by
  unfold universalProduct liuUniversalProduct
  apply tprod_congr
  intro p
  unfold liuBaseDeviation
  split_ifs <;> ring

theorem universalTruncated_source (z : ℕ) :
    universalTruncated z = ∏ p ∈ range (z + 1),
      if p.Prime ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 := by
  unfold universalTruncated liuUniversalProductTruncated
  apply prod_congr rfl
  intro p _
  unfold liuBaseDeviation
  split_ifs <;> ring

theorem universalProduct_pos : 0 < universalProduct := liuUniversalProduct_pos

theorem universalTruncated_pos (z : ℕ) : 0 < universalTruncated z :=
  liuUniversalProductTruncated_pos z

def primeFactor (N p : ℕ) : ℝ := if p.Prime then localFactor N p else 1

theorem primeFactor_hasProd {N : ℕ} (hN : 0 < N) :
    HasProd (primeFactor N) (series N) := by
  have he : primeFactor N =
      ({p : ℕ | p.Prime}.mulIndicator (fun p => ∑' k : ℕ, realCoefficient N (p ^ k))) := by
    funext p
    unfold primeFactor Set.mulIndicator
    simp only [Set.mem_ofPred_eq]
    by_cases hp : p.Prime
    · simp only [if_pos hp]
      exact localFactor_eq_prime_power_sum N hp
    · simp only [if_neg hp]
  rw [he]
  exact EulerProduct.eulerProduct_hasProd_mulIndicator
    (realCoefficient_one N) (fun {_ _} h => realCoefficient_mul N h)
    (realCoefficient_norm_summable hN) (realCoefficient_zero N)

theorem primeFactor_lower {N : ℕ} (hN : Odd N) (p : ℕ) :
    (if p = 2 then (2 : ℝ) else 1) * (1 + liuBaseDeviation p) ≤ primeFactor N p := by
  by_cases h2 : p = 2
  · subst p
    simp [primeFactor, localFactor_two_of_odd hN, liuBaseDeviation, Nat.prime_two]
  simp only [if_neg h2, one_mul]
  by_cases hp : p.Prime
  · have hp2 : 2 < p := by have := hp.two_le; omega
    simp only [primeFactor, if_pos hp,
      one_add_liuBaseDeviation_eq_baseFactor hp hp2, localFactor]
    split_ifs
    · rfl
    · have hpR : 0 < (p : ℝ) - 1 := by
        have h : (2 : ℝ) < p := by exact_mod_cast hp2
        linarith
      have hsq : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
      have hcube : 0 ≤ 1 / ((p : ℝ) - 1) ^ 3 := by positivity
      linarith
  · simp [primeFactor, hp, liuBaseDeviation]

theorem two_mul_universalProduct_le_series {N : ℕ} (hN : Odd N) :
    2 * universalProduct ≤ series N := by
  have hN0 : 0 < N := by obtain ⟨k, hk⟩ := hN; omega
  have hleft : Filter.Tendsto (fun n => 2 * universalTruncated n)
      Filter.atTop (nhds (2 * universalProduct)) :=
    tendsto_const_nhds.mul tendsto_liuUniversalProductTruncated
  have hright := (primeFactor_hasProd hN0).tendsto_prod_nat.comp (Filter.tendsto_add_atTop_nat 1)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have he : 2 * universalTruncated n =
      ∏ p ∈ range (n + 1),
        (if p = 2 then (2 : ℝ) else 1) * (1 + liuBaseDeviation p) := by
    rw [prod_mul_distrib, prod_ite_eq']
    simp [universalTruncated, liuUniversalProductTruncated, show 2 < n + 1 by omega]
  rw [he]
  apply prod_le_prod
  · intro p _
    exact mul_nonneg (by split_ifs <;> norm_num) (one_add_liuBaseDeviation_pos p).le
  · intro p _
    exact primeFactor_lower hN p

theorem all_integer_factor_le_universalFactor (p : ℕ) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 + liuBaseDeviation p := by
  unfold liuBaseDeviation
  split_ifs
  · ring_nf
    rfl
  · have h : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith

def adjustedUniversal (n : ℕ) : ℝ :=
  universalTruncated n * (((n : ℝ) - 1) / (n : ℝ))

theorem adjustedUniversal_step {n : ℕ} (hn : 2 ≤ n) :
    adjustedUniversal n ≤ adjustedUniversal (n + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hf := all_integer_factor_le_universalFactor (n + 1)
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hf
  have he : universalTruncated (n + 1) =
      universalTruncated n * (1 + liuBaseDeviation (n + 1)) := by
    exact prod_range_succ _ _
  unfold adjustedUniversal
  rw [he]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  calc
    _ = (universalTruncated n * (1 - 1 / (n : ℝ) ^ 2)) * ((n : ℝ) / ((n : ℝ) + 1)) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hf (universalTruncated_pos n).le) (by positivity)

theorem adjustedUniversal_le_truncated {n : ℕ} (hn : 2 ≤ n) :
    adjustedUniversal n ≤ universalTruncated n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply mul_le_of_le_one_right (universalTruncated_pos n).le
  exact (div_le_one hnR).mpr (by linarith)

theorem universalProduct_finite_lower_bound {z : ℕ} (hz : 2 ≤ z) :
    universalTruncated z * (((z : ℝ) - 1) / (z : ℝ)) ≤ universalProduct := by
  apply ge_of_tendsto tendsto_liuUniversalProductTruncated
  filter_upwards [Filter.eventually_ge_atTop z] with n hn
  have hmono : adjustedUniversal z ≤ adjustedUniversal n := by
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact ih.trans (adjustedUniversal_step (hz.trans hn))
  exact hmono.trans (adjustedUniversal_le_truncated (hz.trans hn))

theorem universal_decimal_of_finite_certificate
    (hfinite : (6601 : ℝ) / 10000 * (20000 / 19999 : ℝ) ≤
      universalTruncated 20000) :
    (0.6601 : ℝ) ≤ universalProduct := by
  have h := universalProduct_finite_lower_bound (z := 20000) (by norm_num)
  norm_num at h
  nlinarith

theorem re_I11_uniform_lower_bound {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    fullMass N * (2 * universalProduct) -
      fullMass N * absoluteTail N (LiuWang.Proof.Interfaces.sourceP N) -
      2.82 * (N : ℝ) ^ 2 / LiuWang.Proof.Interfaces.sourceP N ^ 2 *
        weightedTotientSum (LiuWang.Proof.Interfaces.sourceP N) ≤ (I11 N).re := by
  have h := re_I11_lower_bound hN
  have hu := mul_le_mul_of_nonneg_left (two_mul_universalProduct_le_series hodd) (fullMass_nonneg N)
  linarith

end LiuWang.Proof.SingularSeries
