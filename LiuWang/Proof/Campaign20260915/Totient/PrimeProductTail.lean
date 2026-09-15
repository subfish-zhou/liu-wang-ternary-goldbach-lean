import LiuWang.Proof.Campaign20260915.Totient.MertensDecay
import LiuWang.Proof.Campaign20260915.Totient.PrimorialReduction

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open AnalyticNumberTheory.Mertens
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation

namespace LiuWang.Proof.Campaign20260915.Totient

private theorem nat_pos_of_tail {n : ℕ}
    (hn : 2 * Real.exp 100 ≤ Real.log (n : ℝ)) : (0 : ℝ) < n := by
  have hL := log_large_of_tail hn
  by_contra! hz
  have hnz : n = 0 := by exact_mod_cast (le_antisymm hz (Nat.cast_nonneg n))
  subst n
  norm_num at hL

private theorem exp_gamma_le_three : Real.exp Real.eulerMascheroniConstant ≤ 3 :=
  (Real.exp_le_exp.mpr (by linarith [Real.eulerMascheroniConstant_lt_two_thirds])).trans
    Real.exp_one_lt_three.le

theorem reciprocal_primeProduct_le_exp_gamma {n : ℕ}
    (hn : 2 * Real.exp 100 ≤ Real.log (n : ℝ)) :
    1 / primeProduct n ≤ Real.exp Real.eulerMascheroniConstant * Real.log n +
      9282 / Real.log (n : ℝ) ^ 2 := by
  let L := Real.log (n : ℝ)
  let E := Real.exp Real.eulerMascheroniConstant
  have hL : 1000000 ≤ L := log_large_of_tail hn
  have hL0 : 0 < L := by linarith
  have hp := primeProduct_pos n
  have herr := (abs_le.mp (log_primeProduct_error_le_log_cube hn)).1
  have hexp : 1 / primeProduct n ≤ E * L * Real.exp (1547 / L ^ 3) := by
    have hh : -Real.log (primeProduct n) ≤
        Real.eulerMascheroniConstant + Real.log L + 1547 / L ^ 3 := by
      dsimp [L] at *
      linarith
    have h := Real.exp_le_exp.mpr hh
    rw [Real.exp_neg, Real.exp_log hp, Real.exp_add, Real.exp_add,
      Real.exp_log hL0] at h
    simpa only [one_div, E] using h
  have hsmall : 1547 / L ^ 3 ≤ 1 := by
    apply (div_le_one (pow_pos hL0 3)).mpr
    nlinarith [sq_nonneg (L - 1)]
  have hlin : Real.exp (1547 / L ^ 3) ≤ 1 + 3094 / L ^ 3 := by
    have h := Real.abs_exp_sub_one_le (x := 1547 / L ^ 3)
      (by rwa [abs_of_nonneg (by positivity)])
    rw [abs_of_nonneg (by positivity : 0 ≤ 1547 / L ^ 3)] at h
    have := (le_abs_self (Real.exp (1547 / L ^ 3) - 1)).trans h
    rw [show 2 * (1547 / L ^ 3) = 3094 / L ^ 3 by ring] at this
    linarith
  calc
    _ ≤ E * L * (1 + 3094 / L ^ 3) :=
      hexp.trans (mul_le_mul_of_nonneg_left hlin (by dsimp [E]; positivity))
    _ = E * L + E * (3094 / L ^ 2) := by field_simp
    _ ≤ E * L + 3 * (3094 / L ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right exp_gamma_le_three (by positivity))
    _ = _ := by ring

theorem reciprocal_primeProduct_le_nu_primorial {n : ℕ}
    (hn : 2 * Real.exp 100 ≤ Real.log (n : ℝ)) :
    1 / primeProduct n ≤ nu (primorial n) := by
  let L := Real.log (n : ℝ)
  let T := Chebyshev.theta (n : ℝ)
  let U := Real.log T
  let E := Real.exp Real.eulerMascheroniConstant
  have hn0 := nat_pos_of_tail hn
  have hL : 1000000 ≤ L := log_large_of_tail hn
  have hL0 : 0 < L := by linarith
  have hL3 : 1030 ≤ L ^ 3 := by nlinarith [sq_nonneg (L - 1)]
  have htheta := abs_le.mp (theta_error_le_log_cube hn0 hn)
  change -(515 * (n : ℝ) / L ^ 3) ≤ T - n ∧ T - n ≤ 515 * (n : ℝ) / L ^ 3 at htheta
  have hhalf : 515 * (n : ℝ) / L ^ 3 ≤ (n : ℝ) / 2 := by
    apply (div_le_iff₀ (pow_pos hL0 3)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hL3 hn0.le]
  have hTlo : (n : ℝ) / 2 ≤ T := by linarith
  have hThi : T ≤ 2 * (n : ℝ) := by linarith
  have hT0 : 0 < T := by linarith
  have hUlo : L - 1 ≤ U := by
    have h := Real.log_le_log (by positivity : 0 < (n : ℝ) / 2) hTlo
    rw [Real.log_div hn0.ne' (by norm_num)] at h
    dsimp [L, U] at *
    linarith [Real.log_two_lt_d9]
  have hU0 : 0 < U := by linarith
  have hUhi : U ≤ 2 * L := by
    have h := Real.log_le_log hT0 hThi
    rw [Real.log_mul (by norm_num) hn0.ne'] at h
    dsimp [L, U] at *
    linarith [Real.log_two_lt_d9]
  have hdiff : L - U ≤ 1030 / L ^ 3 := by
    have hlog := Real.log_le_sub_one_of_pos (div_pos hn0 hT0)
    rw [Real.log_div hn0.ne' hT0.ne'] at hlog
    change L - U ≤ (n : ℝ) / T - 1 at hlog
    apply hlog.trans
    apply (mul_le_mul_iff_right₀ hT0).mp
    field_simp
    have hlo : (n : ℝ) - T ≤ 515 * (n : ℝ) / L ^ 3 := by linarith [htheta.1]
    have hm := mul_le_mul_of_nonneg_right hTlo
      (show 0 ≤ 1030 / L ^ 3 by positivity)
    have hid : (n : ℝ) / 2 * (1030 / L ^ 3) = 515 * (n : ℝ) / L ^ 3 := by ring
    rw [hid] at hm
    have hm' := mul_le_mul_of_nonneg_right (hlo.trans hm) (pow_nonneg hL0.le 3)
    field_simp at hm'
    nlinarith only [hm']
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hmain : E * L ≤ E * U + 3090 / L ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hdiff hE0
    have he := mul_le_mul_of_nonneg_right exp_gamma_le_three
      (show 0 ≤ 1030 / L ^ 3 by positivity)
    rw [show 3 * (1030 / L ^ 3) = 3090 / L ^ 3 by ring] at he
    dsimp [E] at *
    nlinarith
  have hbudget : 3090 / L ^ 3 + 9282 / L ^ 2 ≤ 1 / L := by
    apply (mul_le_mul_iff_right₀ (pow_pos hL0 3)).mp
    field_simp
    nlinarith
  have hnu : 1 / L ≤ (2.50637 : ℝ) / U := by
    apply (div_le_div_iff₀ hL0 hU0).mpr
    linarith
  have htheta_eq : T = Real.log (primorial n) := by
    dsimp [T]
    simpa only [Nat.floor_natCast] using Chebyshev.theta_eq_log_primorial (n : ℝ)
  change 1 / primeProduct n ≤
    E * Real.log (Real.log (primorial n)) + 2.50637 / Real.log (Real.log (primorial n))
  rw [← htheta_eq]
  have hprod := reciprocal_primeProduct_le_exp_gamma hn
  change 1 / primeProduct n ≤ E * L + 9282 / L ^ 2 at hprod
  change 1 / primeProduct n ≤ E * U + 2.50637 / U
  linarith

private theorem primesUpTo_nth_eq_image {k : ℕ} (hk : 0 < k) :
    primesUpTo (Nat.nth Nat.Prime (k - 1)) =
      (Finset.univ : Finset (Fin k)).image (fun i : Fin k => Nat.nth Nat.Prime i) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hp, hle⟩ := mem_primesUpTo.mp hp
    have hj : Nat.count Nat.Prime p ≤ k - 1 := by
      apply (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mp
      simpa only [Nat.nth_count hp] using hle
    exact Finset.mem_image.mpr ⟨⟨Nat.count Nat.Prime p, by omega⟩,
      Finset.mem_univ _, Nat.nth_count hp⟩
  · intro hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact mem_primesUpTo.mpr ⟨Nat.prime_nth_prime i,
      (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mpr (by omega)⟩

theorem first_primes_Euler_product_tail {k : ℕ} (hk : 4 ≤ k)
    (htail : 2 * Real.exp 100 ≤ Real.log (Nat.nth Nat.Prime (k - 1) : ℝ)) :
    (∏ i : Fin k, (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1)) ≤
      nu (∏ i : Fin k, Nat.nth Nat.Prime i : ℕ) := by
  have himage := primesUpTo_nth_eq_image (show 0 < k by omega)
  have hprod {M : Type} [CommMonoid M] (f : ℕ → M) :
      (∏ p ∈ primesUpTo (Nat.nth Nat.Prime (k - 1)), f p) =
        ∏ i : Fin k, f (Nat.nth Nat.Prime i) := by
    rw [himage]
    apply Finset.prod_image
    intro i _ j _ hij
    exact Fin.ext ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij)
  have hprim : primorial (Nat.nth Nat.Prime (k - 1)) =
      ∏ i : Fin k, Nat.nth Nat.Prime i :=
    hprod (fun p => p)
  have hratio : 1 / primeProduct (Nat.nth Nat.Prime (k - 1)) =
      ∏ i : Fin k, (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1) := by
    rw [primeProduct, one_div, ← Finset.prod_inv_distrib, hprod]
    apply Finset.prod_congr rfl
    intro i _
    have hp0 : (Nat.nth Nat.Prime i : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.prime_nth_prime i).ne_zero
    field_simp
  simpa only [hratio, hprim] using reciprocal_primeProduct_le_nu_primorial htail

#print axioms reciprocal_primeProduct_le_exp_gamma
#print axioms reciprocal_primeProduct_le_nu_primorial
#print axioms first_primes_Euler_product_tail

end LiuWang.Proof.Campaign20260915.Totient
