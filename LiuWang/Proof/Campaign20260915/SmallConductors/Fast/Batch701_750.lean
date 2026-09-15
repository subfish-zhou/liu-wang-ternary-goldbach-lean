import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q701.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q703.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q705.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q707.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q708.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q709.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q712.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q713.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q715.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q716.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q717.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q719.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q721.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q723.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q724.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q727.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q728.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q731.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q732.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q733.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q737.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q739.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q740.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q741.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q743.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q744.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q745.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q748.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q749.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_701_750 {q : ℕ} [NeZero q]
    (hl : 701 ≤ q) (hu : q ≤ 750) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 751, 701 ≤ k.val → Admissible k.val →
    k.val = 701 ∨
    k.val = 703 ∨
    k.val = 705 ∨
    k.val = 707 ∨
    k.val = 708 ∨
    k.val = 709 ∨
    k.val = 712 ∨
    k.val = 713 ∨
    k.val = 715 ∨
    k.val = 716 ∨
    k.val = 717 ∨
    k.val = 719 ∨
    k.val = 721 ∨
    k.val = 723 ∨
    k.val = 724 ∨
    k.val = 727 ∨
    k.val = 728 ∨
    k.val = 731 ∨
    k.val = 732 ∨
    k.val = 733 ∨
    k.val = 737 ∨
    k.val = 739 ∨
    k.val = 740 ∨
    k.val = 741 ∨
    k.val = 743 ∨
    k.val = 744 ∨
    k.val = 745 ∨
    k.val = 748 ∨
    k.val = 749 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q701.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q703.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q705.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q707.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q708.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q709.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q712.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q713.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q715.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q716.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q717.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q719.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q721.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q723.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q724.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q727.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q728.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q731.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q732.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q733.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q737.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q739.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q740.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q741.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q743.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q744.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q745.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q748.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q749.original_region chi hp hc hsq hqx hb

#print axioms range_701_750

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
