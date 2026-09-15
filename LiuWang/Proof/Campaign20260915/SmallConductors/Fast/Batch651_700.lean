import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q651.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q652.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q653.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q655.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q659.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q660.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q661.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q663.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q664.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q665.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q667.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q668.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q669.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q671.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q673.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q677.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q679.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q680.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q681.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q683.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q685.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q687.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q689.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q691.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q692.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q695.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q696.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q697.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q699.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_651_700 {q : ℕ} [NeZero q]
    (hl : 651 ≤ q) (hu : q ≤ 700) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 701, 651 ≤ k.val → Admissible k.val →
    k.val = 651 ∨
    k.val = 652 ∨
    k.val = 653 ∨
    k.val = 655 ∨
    k.val = 659 ∨
    k.val = 660 ∨
    k.val = 661 ∨
    k.val = 663 ∨
    k.val = 664 ∨
    k.val = 665 ∨
    k.val = 667 ∨
    k.val = 668 ∨
    k.val = 669 ∨
    k.val = 671 ∨
    k.val = 673 ∨
    k.val = 677 ∨
    k.val = 679 ∨
    k.val = 680 ∨
    k.val = 681 ∨
    k.val = 683 ∨
    k.val = 685 ∨
    k.val = 687 ∨
    k.val = 689 ∨
    k.val = 691 ∨
    k.val = 692 ∨
    k.val = 695 ∨
    k.val = 696 ∨
    k.val = 697 ∨
    k.val = 699 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q651.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q652.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q653.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q655.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q659.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q660.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q661.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q663.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q664.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q665.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q667.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q668.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q669.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q671.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q673.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q677.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q679.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q680.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q681.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q683.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q685.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q687.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q689.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q691.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q692.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q695.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q696.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q697.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q699.original_region chi hp hc hsq hqx hb

#print axioms range_651_700

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
