import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q460.Cover
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q460.Certificates

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option maxSynthPendingDepth 128
set_option synthInstance.maxSize 4096

open LiuWang.Proof.SmallConductorExpansion

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q460

theorem original_region (chi : DirichletCharacter ℂ 460)
    (hp : chi.IsPrimitive)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 460 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  obtain ⟨signs, hs⟩ := square_word_signs chi hsq generators units
  have ht := square_word_table chi hsq generators words cover signs hs
  have hall : ∀ signs : Fin 3 → Bool,
    signs = ![false, false, false] ∨
    signs = ![true, false, false] ∨
    signs = ![false, true, false] ∨
    signs = ![true, true, false] ∨
    signs = ![false, false, true] ∨
    signs = ![true, false, true] ∨
    signs = ![false, true, true] ∨
    signs = ![true, true, true] := by
    decide +kernel
  rcases hall signs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim ((not_primitive_of_kernel_entries chi _
      (d := 230) (by decide) (by decide) ht
      (by rw [values0_eq]; decide +kernel) certificate0) hp)
  · exact False.elim ((not_primitive_of_kernel_entries chi _
      (d := 92) (by decide) (by decide) ht
      (by rw [values1_eq]; decide +kernel) certificate1) hp)
  · exact rationalWeighted_original_region chi hc _ ht
      (m := 460) (by decide) (by decide) (n := 53) (by decide)
      ((VerifiedScan.weighted_iff _ _ _ _ _).mp certificate2)
      (by norm_num) (by norm_num)
      (VerifiedScan.log_scale_dyadic (j := 8) (by norm_num; linarith)
        (by norm_num)) hb
  · exact False.elim ((not_primitive_of_kernel_entries chi _
      (d := 230) (by decide) (by decide) ht
      (by rw [values3_eq]; decide +kernel) certificate3) hp)
  · exact False.elim ((not_primitive_of_kernel_entries chi _
      (d := 20) (by decide) (by decide) ht
      (by rw [values4_eq]; decide +kernel) certificate4) hp)
  · exact False.elim ((not_primitive_of_kernel_entries chi _
      (d := 230) (by decide) (by decide) ht
      (by rw [values5_eq]; decide +kernel) certificate5) hp)
  · exact False.elim ((not_primitive_of_kernel_entries chi _
      (d := 230) (by decide) (by decide) ht
      (by rw [values6_eq]; decide +kernel) certificate6) hp)
  · exact False.elim ((not_primitive_of_kernel_entries chi _
      (d := 92) (by decide) (by decide) ht
      (by rw [values7_eq]; decide +kernel) certificate7) hp)

#print axioms original_region

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q460
