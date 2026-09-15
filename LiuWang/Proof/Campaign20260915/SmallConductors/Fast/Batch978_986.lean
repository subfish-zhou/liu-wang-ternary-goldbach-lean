import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q979.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q983.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q984.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q985.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_978_986 {q : ℕ} [NeZero q]
    (hl : 978 ≤ q) (hu : q ≤ 986) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 987, 978 ≤ k.val → Admissible k.val →
    k.val = 979 ∨
    k.val = 983 ∨
    k.val = 984 ∨
    k.val = 985 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q979.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q983.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q984.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q985.original_region chi hc hsq hqx hb

#print axioms range_978_986

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
