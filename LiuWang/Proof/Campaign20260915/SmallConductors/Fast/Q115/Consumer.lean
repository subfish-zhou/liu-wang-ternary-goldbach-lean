import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q115.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q115.Sign0
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q115.Sign1
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q115.Sign2
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q115.Sign3

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

open LiuWang.Proof.SmallConductorExpansion

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q115

theorem original_region (chi : DirichletCharacter ℂ 115)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 115 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  obtain ⟨signs, hs⟩ := square_word_signs chi hsq generators units
  have ht := square_word_table chi hsq generators words cover signs hs
  have hall : ∀ signs : Fin 2 → Bool,
    signs = ![false, false] ∨
    signs = ![true, false] ∨
    signs = ![false, true] ∨
    signs = ![true, true] := by
    decide +kernel
  rcases hall signs with rfl | rfl | rfl | rfl
  · have hz := DirichletLWeakStripDerivative.sum_one_period_eq_zero chi hc
    simp only [tableValue_character chi _ ht, ← Int.cast_sum] at hz
    exact False.elim (certificate0 (by
      rw [VerifiedScan.periodSum_eq]
      exact_mod_cast hz))
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 115) (by decide) (by decide) (n := 40) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate1)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 6) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 115) (by decide) (by decide) (n := 40) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate2)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 6) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 115) (by decide) (by decide) (n := 40) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate3)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 6) (by norm_num; linarith)
        (by norm_num)) hb

#print axioms original_region

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q115
