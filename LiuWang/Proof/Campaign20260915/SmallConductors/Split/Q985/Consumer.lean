import LiuWang.Proof.Campaign20260915.SmallConductors.Split.Q985.Sign0
import LiuWang.Proof.Campaign20260915.SmallConductors.Split.Q985.Sign1
import LiuWang.Proof.Campaign20260915.SmallConductors.Split.Q985.Sign2
import LiuWang.Proof.Campaign20260915.SmallConductors.Split.Q985.Sign3

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Split.Q985

theorem original_region (chi : DirichletCharacter ℂ 985)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 985 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply VerifiedScan.square_word_scan_original_region chi hc hsq generators
    (by decide +kernel) words cover (m := 985) (by decide) (by decide)
    (n := 60) (by decide) (A := 10117 / 10000) (by norm_num) (by norm_num) _
    (VerifiedScan.log_scale_dyadic (j := 9) (by norm_num; linarith)
      (by norm_num)) hb
  intro signs
  fin_cases signs <;> first
    | exact Or.inl certificate0
    | exact Or.inr ⟨15, certificate1⟩
    | exact Or.inr ⟨19, certificate2⟩
    | exact Or.inr ⟨2, certificate3⟩

#print axioms original_region

end LiuWang.Proof.Campaign20260915.SmallConductors.Split.Q985
