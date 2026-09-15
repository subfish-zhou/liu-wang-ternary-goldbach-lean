import LiuWang.Proof.SmallConductorExpansion.Continuation.AlignedTables

/-! # Exact aligned certificate for every nonprincipal quadratic character modulo 67 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

instance prime67 : Fact (Nat.Prime 67) := ⟨by decide⟩

def values67 : List ℤ := [0, 1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, -1, 1, 1, 1, 1, -1, 1, -1, 1, 1, 1, 1, 1, 1, -1, -1, 1, -1, -1, -1, 1, -1, 1, 1, 1, -1, 1, 1, -1, -1, -1, -1, -1, -1, 1, -1, 1, -1, -1, -1, -1, 1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1, 1, -1]

theorem table67 :
    ∀ a : ZMod 67, primeCharacter 67 a = (values67.getD a.val 0 : ℂ) :=
  primeCharacter_table 67 values67 (by decide +kernel)

theorem amplitude67 :
    ∀ n ∈ range 67, |((∑ k ∈ range n, tableValue 67 values67 k : ℤ) : ℚ)| ≤ 6 := by
  decide +kernel

def pos67 (k : ℕ) : ℚ := max (tableValue 67 values67 k) 0 / k

theorem pos67_block0 : (∑ k ∈ range 32, pos67 (k + 0)) = (1732059239179 / 776363187600 : ℚ) := by
  norm_num [pos67, tableValue, values67, Finset.sum_range_succ]

theorem pos67_block32 : (∑ k ∈ range 35, pos67 (k + 32)) = (65722951791071 / 192556927442880 : ℚ) := by
  norm_num [pos67, tableValue, values67, Finset.sum_range_succ]

theorem pos67_total : (∑ k ∈ range 67, pos67 k) = (533556562321508560271 / 207423285026107550400 : ℚ) := by
  have h0 := pos67_block0
  simp only [Nat.add_zero] at h0
  rw [show 67 = 32 + 35 by rfl, Finset.sum_range_add, h0]
  simp_rw [Nat.add_comm 32, pos67_block32]
  norm_num

def neg67 (k : ℕ) : ℚ := max (-(tableValue 67 values67 k)) 0 / k

theorem neg67_block0 : (∑ k ∈ range 32, neg67 (k + 0)) = (60198731 / 33513480 : ℚ) := by
  norm_num [neg67, tableValue, values67, Finset.sum_range_succ]

theorem neg67_block32 : (∑ k ∈ range 35, neg67 (k + 32)) = (399109322321497509 / 983355242901231200 : ℚ) := by
  norm_num [neg67, tableValue, values67, Finset.sum_range_succ]

theorem neg67_total : (∑ k ∈ range 67, neg67 k) = (1812494506400747675213 / 823068338308330514400 : ℚ) := by
  have h0 := neg67_block0
  simp only [Nat.add_zero] at h0
  rw [show 67 = 32 + 35 by rfl, Finset.sum_range_add, h0]
  simp_rw [Nat.add_comm 32, neg67_block32]
  norm_num

theorem margin67 :
    (28 / 25) * (∑ k ∈ range 67, (max (-(tableValue 67 values67 k)) 0 : ℚ) / k) +
      6 * (28 / 25) / 67 <
      ∑ k ∈ range 67, (max (tableValue 67 values67 k) 0 : ℚ) / k := by
  change (28 / 25) * (∑ k ∈ range 67, neg67 k) + 6 * (28 / 25) / 67 <
    ∑ k ∈ range 67, pos67 k
  rw [pos67_total, neg67_total]
  norm_num

theorem certificate67 : RationalAlignedCertificate 67 values67 67 6 (28 / 25) :=
  ⟨amplitude67, margin67⟩

theorem quadratic_67_original_region (chi : DirichletCharacter ℂ 67)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 67 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  rw [quadratic_prime_eq 67 (by decide) chi hc hsq]
  apply rationalAligned_original_region (primeCharacter 67)
    (primeCharacter_ne_one 67 (by decide)) values67 table67
    (by decide) (dvd_refl 67) (n := 40) (by decide) certificate67
    (by norm_num) (by norm_num) _ hb
  exact log_scale_forty (by linarith)

end LiuWang.Proof.SmallConductorExpansion.Continuation
