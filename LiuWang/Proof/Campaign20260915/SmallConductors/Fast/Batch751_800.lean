import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q751.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q753.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q755.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q757.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q759.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q760.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q761.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q763.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q764.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q767.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q769.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q771.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q772.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q773.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q776.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q777.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q779.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q780.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q781.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q785.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q787.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q788.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q789.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q791.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q793.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q795.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q796.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q797.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q799.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_751_800 {q : ℕ} [NeZero q]
    (hl : 751 ≤ q) (hu : q ≤ 800) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 801, 751 ≤ k.val → Admissible k.val →
    k.val = 751 ∨
    k.val = 753 ∨
    k.val = 755 ∨
    k.val = 757 ∨
    k.val = 759 ∨
    k.val = 760 ∨
    k.val = 761 ∨
    k.val = 763 ∨
    k.val = 764 ∨
    k.val = 767 ∨
    k.val = 769 ∨
    k.val = 771 ∨
    k.val = 772 ∨
    k.val = 773 ∨
    k.val = 776 ∨
    k.val = 777 ∨
    k.val = 779 ∨
    k.val = 780 ∨
    k.val = 781 ∨
    k.val = 785 ∨
    k.val = 787 ∨
    k.val = 788 ∨
    k.val = 789 ∨
    k.val = 791 ∨
    k.val = 793 ∨
    k.val = 795 ∨
    k.val = 796 ∨
    k.val = 797 ∨
    k.val = 799 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q751.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q753.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q755.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q757.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q759.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q760.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q761.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q763.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q764.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q767.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q769.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q771.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q772.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q773.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q776.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q777.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q779.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q780.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q781.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q785.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q787.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q788.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q789.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q791.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q793.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q795.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q796.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q797.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q799.original_region chi hp hc hsq hqx hb

#print axioms range_751_800

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
