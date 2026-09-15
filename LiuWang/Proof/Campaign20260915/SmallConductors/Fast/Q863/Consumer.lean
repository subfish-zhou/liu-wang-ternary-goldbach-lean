import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q863.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q863.Certificates

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option maxSynthPendingDepth 128
set_option synthInstance.maxSize 4096

open LiuWang.Proof.SmallConductorExpansion

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q863

theorem original_region (chi : DirichletCharacter ℂ 863)
    (hp : chi.IsPrimitive)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 863 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  obtain ⟨signs, hs⟩ := square_word_signs chi hsq generators units
  have ht := square_word_table chi hsq generators words cover signs hs
  have hall : ∀ signs : Fin 1 → Bool,
    signs = ![false] ∨
    signs = ![true] := by
    decide +kernel
  rcases hall signs with rfl | rfl
  · exact False.elim ((not_primitive_of_kernel_entries chi _
      (d := 1) (by decide) (by decide) ht
      (by rw [values0_eq]; decide +kernel) certificate0) hp)
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 863) (by decide) (by decide) (n := 60) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate1)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
        (by norm_num)) hb

#print axioms original_region

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q863
