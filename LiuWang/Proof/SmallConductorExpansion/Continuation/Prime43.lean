import LiuWang.Proof.SmallConductorExpansion.Continuation.AlignedTables

/-! # Exact aligned certificate for every nonprincipal quadratic character modulo 43 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

instance prime43 : Fact (Nat.Prime 43) := ⟨by decide⟩

def values43 : List ℤ := [0, 1, -1, -1, 1, -1, 1, -1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1, 1, 1, -1, -1, -1, -1, -1, 1, -1, -1, -1, 1, 1, -1, 1, -1, 1, 1, -1]

theorem table43 :
    ∀ a : ZMod 43, primeCharacter 43 a = (values43.getD a.val 0 : ℂ) :=
  primeCharacter_table 43 values43 (by decide)

theorem amplitude43 :
    ∀ n ∈ range 43, |((∑ k ∈ range n, tableValue 43 values43 k : ℤ) : ℚ)| ≤ 5 := by
  decide +kernel

theorem margin43 :
    (113 / 100) * (∑ k ∈ range 43, (max (-(tableValue 43 values43 k)) 0 : ℚ) / k) +
      5 * (113 / 100) / 43 <
      ∑ k ∈ range 43, (max (tableValue 43 values43 k) 0 : ℚ) / k := by
  norm_num [tableValue, values43, Finset.sum_range_succ]

theorem certificate43 : RationalAlignedCertificate 43 values43 43 5 (113 / 100) :=
  ⟨amplitude43, margin43⟩

theorem quadratic_43_original_region (chi : DirichletCharacter ℂ 43)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 43 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  rw [quadratic_prime_eq 43 (by decide) chi hc hsq]
  apply rationalAligned_original_region (primeCharacter 43)
    (primeCharacter_ne_one 43 (by decide)) values43 table43
    (by decide) (dvd_refl 43) (n := 32) (by decide) certificate43
    (by norm_num) (by norm_num) _ hb
  exact log_scale_thirtytwo (by linarith)

end LiuWang.Proof.SmallConductorExpansion.Continuation
