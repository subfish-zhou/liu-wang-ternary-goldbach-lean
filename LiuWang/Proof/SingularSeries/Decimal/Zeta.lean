import LiuWang.Proof.SingularSeries.Decimal.Local
import Mathlib.NumberTheory.ZetaValues

/-! The finite zeta(2) Euler factors are bounded below by the actual zeta value. -/

set_option autoImplicit false
noncomputable section
open Finset

namespace LiuWang.Proof.SingularSeries.Decimal

def squareReciprocal : ℕ →* ℝ where
  toFun n := 1 / (n : ℝ) ^ 2
  map_one' := by norm_num
  map_mul' m n := by simp [mul_pow, mul_comm]

theorem squareReciprocal_summable : Summable squareReciprocal :=
  hasSum_zeta_two.summable

theorem finite_zeta_inverse_upper (s : Finset ℕ) :
    (∏ p ∈ s with p.Prime, b p)⁻¹ ≤ Real.pi ^ 2 / 6 := by
  have h := EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers
    squareReciprocal_summable s
  have hs := Summable.tsum_subtype_le squareReciprocal (Nat.factoredNumbers s)
    (fun _ => by dsimp [squareReciprocal]; positivity) squareReciprocal_summable
  rw [← h] at hs
  simpa only [squareReciprocal, MonoidHom.coe_mk, OneHom.coe_mk, b,
    prod_inv_distrib, hasSum_zeta_two.tsum_eq] using hs

theorem finite_zeta_product_lower (s : Finset ℕ) :
    6 / Real.pi ^ 2 ≤ ∏ p ∈ s with p.Prime, b p := by
  have hp : 0 < ∏ p ∈ s with p.Prime, b p := by
    apply prod_pos
    intro p hp
    apply b_pos
    exact_mod_cast (mem_filter.mp hp).2.one_lt
  have h := finite_zeta_inverse_upper s
  rw [← one_div, div_le_iff₀ hp] at h
  apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
  nlinarith

end LiuWang.Proof.SingularSeries.Decimal
