import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q840.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q840.Certificates

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxSize 4096
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

open LiuWang.Proof.SmallConductorExpansion

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q840

theorem original_region (chi : DirichletCharacter ℂ 840)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 840 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  obtain ⟨signs, hs⟩ := square_word_signs chi hsq generators units
  have ht := square_word_table chi hsq generators words cover signs hs
  have hall : ∀ signs : Fin 5 → Bool,
    signs = ![false, false, false, false, false] ∨
    signs = ![true, false, false, false, false] ∨
    signs = ![false, true, false, false, false] ∨
    signs = ![true, true, false, false, false] ∨
    signs = ![false, false, true, false, false] ∨
    signs = ![true, false, true, false, false] ∨
    signs = ![false, true, true, false, false] ∨
    signs = ![true, true, true, false, false] ∨
    signs = ![false, false, false, true, false] ∨
    signs = ![true, false, false, true, false] ∨
    signs = ![false, true, false, true, false] ∨
    signs = ![true, true, false, true, false] ∨
    signs = ![false, false, true, true, false] ∨
    signs = ![true, false, true, true, false] ∨
    signs = ![false, true, true, true, false] ∨
    signs = ![true, true, true, true, false] ∨
    signs = ![false, false, false, false, true] ∨
    signs = ![true, false, false, false, true] ∨
    signs = ![false, true, false, false, true] ∨
    signs = ![true, true, false, false, true] ∨
    signs = ![false, false, true, false, true] ∨
    signs = ![true, false, true, false, true] ∨
    signs = ![false, true, true, false, true] ∨
    signs = ![true, true, true, false, true] ∨
    signs = ![false, false, false, true, true] ∨
    signs = ![true, false, false, true, true] ∨
    signs = ![false, true, false, true, true] ∨
    signs = ![true, true, false, true, true] ∨
    signs = ![false, false, true, true, true] ∨
    signs = ![true, false, true, true, true] ∨
    signs = ![false, true, true, true, true] ∨
    signs = ![true, true, true, true, true] := by
    decide +kernel
  rcases hall signs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hz := DirichletLWeakStripDerivative.sum_one_period_eq_zero chi hc
    simp only [tableValue_character chi _ ht, ← Int.cast_sum] at hz
    exact False.elim (certificate0 (by
      rw [VerifiedScan.periodSum_eq]
      exact_mod_cast hz))
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate1)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate2)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate3)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate4)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate5)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate6)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate7)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate8)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate9)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate10)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate11)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate12)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate13)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate14)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate15)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate16)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate17)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate18)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate19)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate20)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate21)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate22)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate23)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate24)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate25)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate26)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate27)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate28)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate29)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate30)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 840) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate31)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb

#print axioms original_region

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q840
