import LiuWang.Proof.SmallConductorExpansion.Continuation.Weighted

/-! # A termwise weighted certificate at the hard conductor 163 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

instance prime163 : Fact (Nat.Prime 163) := ⟨by decide +kernel⟩

def values163 : List ℤ := [0, 1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, -1, 1, 1, 1, -1, -1, -1, -1, 1, 1, -1, 1, 1, 1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, -1, 1, -1, -1, 1, 1, -1, 1, -1, 1, -1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1, -1, -1, -1, 1, -1, 1, -1, -1, 1, -1, -1, 1, -1, -1, -1, 1, -1, 1, 1, 1, -1, 1, 1, -1, 1, 1, -1, 1, -1, 1, 1, 1, -1, -1, 1, -1, -1, -1, 1, -1, -1, -1, -1, -1, -1, 1, -1, 1, -1, 1, -1, -1, 1, 1, -1, 1, -1, -1, -1, -1, 1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, -1, -1, -1, 1, -1, -1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1, 1, -1]

theorem table163 :
    ∀ a : ZMod 163, primeCharacter 163 a = (values163.getD a.val 0 : ℂ) :=
  primeCharacter_table 163 values163 (by decide +kernel)

theorem certificate163 : RationalWeightedCertificate 163 values163 163 9 (127 / 125) := by
  constructor
  · decide +kernel
  · decide +kernel

theorem log_scale_fortysix {x : ℝ} (hx : 128 ≤ x) :
    (46 : ℝ) ≤ 9.645908801 * Real.log x := by
  have he : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 128) hx
  rw [he] at hl
  have ht := Real.log_two_gt_d9
  nlinarith

theorem quadratic_163_original_region (chi : DirichletCharacter ℂ 163)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 163 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  rw [quadratic_prime_eq 163 (by decide) chi hc hsq]
  apply rationalWeighted_original_region (primeCharacter 163)
    (primeCharacter_ne_one 163 (by decide)) values163 table163
    (by decide) (dvd_refl 163) (n := 46) (by decide) certificate163
    (by norm_num) (by norm_num) _ hb
  exact log_scale_fortysix (by linarith)

end LiuWang.Proof.SmallConductorExpansion.Continuation
