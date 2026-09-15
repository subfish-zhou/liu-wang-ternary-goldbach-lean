import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Split.Q101.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q103.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q104.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q105.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q107.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q109.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q111.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q113.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q115.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q116.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q119.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q120.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q123.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q124.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q127.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q129.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q131.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q132.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q133.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q136.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q137.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q139.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q140.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q141.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q143.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q145.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q148.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q149.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_101_150 {q : ℕ} [NeZero q]
    (hl : 101 ≤ q) (hu : q ≤ 150) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 151, 101 ≤ k.val → Admissible k.val →
    k.val = 101 ∨
    k.val = 103 ∨
    k.val = 104 ∨
    k.val = 105 ∨
    k.val = 107 ∨
    k.val = 109 ∨
    k.val = 111 ∨
    k.val = 113 ∨
    k.val = 115 ∨
    k.val = 116 ∨
    k.val = 119 ∨
    k.val = 120 ∨
    k.val = 123 ∨
    k.val = 124 ∨
    k.val = 127 ∨
    k.val = 129 ∨
    k.val = 131 ∨
    k.val = 132 ∨
    k.val = 133 ∨
    k.val = 136 ∨
    k.val = 137 ∨
    k.val = 139 ∨
    k.val = 140 ∨
    k.val = 141 ∨
    k.val = 143 ∨
    k.val = 145 ∨
    k.val = 148 ∨
    k.val = 149 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Split.Q101.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q103.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q104.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q105.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q107.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q109.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q111.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q113.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q115.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q116.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q119.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q120.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q123.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q124.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q127.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q129.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q131.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q132.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q133.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q136.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q137.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q139.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q140.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q141.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q143.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q145.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q148.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q149.original_region chi hc hsq hqx hb

#print axioms range_101_150

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
