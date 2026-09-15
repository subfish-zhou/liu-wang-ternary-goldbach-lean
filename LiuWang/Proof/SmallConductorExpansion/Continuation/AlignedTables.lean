import LiuWang.Proof.SmallConductorExpansion.Continuation.AlignedTail
import LiuWang.Proof.SmallConductorExpansion.PrimeTables

/-! # Exact rational certificates for the one-amplitude tail -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def RationalAlignedCertificate (q : ℕ) (values : List ℤ) (m : ℕ) (P C : ℚ) : Prop :=
  (∀ n ∈ range q, |((∑ k ∈ range n, tableValue q values k : ℤ) : ℚ)| ≤ P) ∧
    C * (∑ k ∈ range m, (max (-(tableValue q values k)) 0 : ℚ) / k) +
      P * C / m < ∑ k ∈ range m, (max (tableValue q values k) 0 : ℚ) / k

theorem alignedCertificate_of_rational {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (values : List ℤ)
    (hvalues : ∀ a : ZMod q, chi a = (values.getD a.val 0 : ℂ))
    {m : ℕ} {P C : ℚ} (hcert : RationalAlignedCertificate q values m P C) :
    AlignedCertificate chi m (P : ℝ) (C : ℝ) := by
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
  · have hp : positiveHarmonic chi m =
        ((∑ k ∈ range m, (max (tableValue q values k) 0 : ℚ) / k : ℚ) : ℝ) := by
      unfold positiveHarmonic
      push_cast
      simp only [hre]
    have hn : negativeHarmonic chi m =
        ((∑ k ∈ range m, (max (-(tableValue q values k)) 0 : ℚ) / k : ℚ) : ℝ) := by
      unfold negativeHarmonic
      push_cast
      simp only [hre]
    rw [hp, hn]
    exact_mod_cast hcert.2

theorem original_region_of_log_scale {x beta : ℝ} {n : ℕ}
    (hn : 1 < n) (hlog : (n : ℝ) ≤ 9.645908801 * Real.log x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    1 - 1 / (n : ℝ) ≤ beta := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hw := one_div_le_one_div_of_le hn0 hlog
  linarith

theorem log_scale_thirtytwo {x : ℝ} (hx : 32 ≤ x) :
    (32 : ℝ) ≤ 9.645908801 * Real.log x := by
  have he : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 32) hx
  rw [he] at hl
  have ht := Real.log_two_gt_d9
  nlinarith

theorem log_scale_forty {x : ℝ} (hx : 64 ≤ x) :
    (40 : ℝ) ≤ 9.645908801 * Real.log x := by
  have he : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 64) hx
  rw [he] at hl
  have ht := Real.log_two_gt_d9
  nlinarith

theorem rationalAligned_original_region {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    (values : List ℤ) (hvalues : ∀ a : ZMod q, chi a = (values.getD a.val 0 : ℂ))
    {m n : ℕ} (hm : 1 ≤ m) (hqm : q ∣ m) (hn : 1 < n)
    {P C : ℚ} (hcert : RationalAlignedCertificate q values m P C)
    (hC : 0 ≤ C) (hpow : (m : ℚ) ≤ C ^ n)
    {x beta : ℝ} (hlog : (n : ℝ) ≤ 9.645908801 * Real.log x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  exact alignedCertificate_ne_zero_on_interval chi hc hm hqm hn
    (alignedCertificate_of_rational chi values hvalues hcert)
    (by exact_mod_cast hC) (by exact_mod_cast hpow)
    (original_region_of_log_scale hn hlog hb)

end LiuWang.Proof.SmallConductorExpansion.Continuation
