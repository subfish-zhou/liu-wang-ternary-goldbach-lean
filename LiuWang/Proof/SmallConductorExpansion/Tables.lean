import LiuWang.Proof.SmallConductorExpansion.Interval

/-!
# Exact rational table checker

The table is indexed by every residue, not merely by conductor. Its agreement
with an actual character is a separate proved obligation. The checker contains
only finite integer sums and rational arithmetic, not an L-value or zero.
-/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def tableValue (q : ℕ) (values : List ℤ) (k : ℕ) : ℤ :=
  values.getD (k % q) 0

def RationalCertificate (q : ℕ) (values : List ℤ) (m : ℕ) (P C : ℚ) : Prop :=
  (∀ n ∈ range q, |((∑ k ∈ range n, tableValue q values k : ℤ) : ℚ)| ≤ P) ∧
    C * (∑ k ∈ range m, (max (-(tableValue q values k)) 0 : ℚ) / k) +
      2 * P * C / m <
      ∑ k ∈ range m, (max (tableValue q values k) 0 : ℚ) / k

instance rationalCertificateDecidable (q : ℕ) (values : List ℤ) (m : ℕ) (P C : ℚ) :
    Decidable (RationalCertificate q values m P C) := by
  unfold RationalCertificate
  infer_instance

theorem tableValue_character {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (values : List ℤ) (hvalues : ∀ a : ZMod q, chi a = (values.getD a.val 0 : ℂ))
    (k : ℕ) : chi k = (tableValue q values k : ℂ) := by
  simpa [tableValue, ZMod.val_natCast] using hvalues (k : ZMod q)

theorem signedCertificate_of_rational {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (values : List ℤ)
    (hvalues : ∀ a : ZMod q, chi a = (values.getD a.val 0 : ℂ))
    {m : ℕ} {P C : ℚ} (hcert : RationalCertificate q values m P C) :
    SignedCertificate chi m (P : ℝ) (C : ℝ) := by
  have hval := tableValue_character chi values hvalues
  have hre (k : ℕ) : (chi k).re = (tableValue q values k : ℝ) := by
    rw [hval]
    simp
  refine ⟨?_, ?_⟩
  · intro n hn
    have h := hcert.1 n (mem_range.mpr hn)
    have he : (∑ k ∈ range n, chi k) = ((∑ k ∈ range n, tableValue q values k : ℤ) : ℂ) := by
      simp only [hval, Int.cast_sum]
    rw [he, Complex.norm_intCast]
    exact_mod_cast h
  · have hp :
        positiveHarmonic chi m =
          ((∑ k ∈ range m, (max (tableValue q values k) 0 : ℚ) / k : ℚ) : ℝ) := by
      unfold positiveHarmonic
      push_cast
      simp only [hre]
    have hn :
        negativeHarmonic chi m =
          ((∑ k ∈ range m, (max (-(tableValue q values k)) 0 : ℚ) / k : ℚ) : ℝ) := by
      unfold negativeHarmonic
      push_cast
      simp only [hre]
    rw [hp, hn]
    exact_mod_cast hcert.2

theorem rationalCertificate_original_region {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1) (values : List ℤ)
    (hvalues : ∀ a : ZMod q, chi a = (values.getD a.val 0 : ℂ))
    {m : ℕ} (hm : 1 ≤ m) (hm32 : m ≤ 32) {P : ℚ}
    (hcert : RationalCertificate q values m P (6 / 5))
    {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply signedCertificate_ne_zero_original_region chi hc hm hm32
    (P := (P : ℝ)) _ hx hb
  simpa only [Rat.cast_div, Rat.cast_ofNat] using signedCertificate_of_rational chi values hvalues hcert

end LiuWang.Proof.SmallConductorExpansion
