import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q803.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q804.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q805.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q807.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q808.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q809.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q811.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q812.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q813.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q815.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q817.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q820.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q821.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q823.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q824.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q827.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q829.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q831.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q835.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q836.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q839.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q840.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q843.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q844.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q849.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_801_850 {q : ℕ} [NeZero q]
    (hl : 801 ≤ q) (hu : q ≤ 850) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 851, 801 ≤ k.val → Admissible k.val →
    k.val = 803 ∨
    k.val = 804 ∨
    k.val = 805 ∨
    k.val = 807 ∨
    k.val = 808 ∨
    k.val = 809 ∨
    k.val = 811 ∨
    k.val = 812 ∨
    k.val = 813 ∨
    k.val = 815 ∨
    k.val = 817 ∨
    k.val = 820 ∨
    k.val = 821 ∨
    k.val = 823 ∨
    k.val = 824 ∨
    k.val = 827 ∨
    k.val = 829 ∨
    k.val = 831 ∨
    k.val = 835 ∨
    k.val = 836 ∨
    k.val = 839 ∨
    k.val = 840 ∨
    k.val = 843 ∨
    k.val = 844 ∨
    k.val = 849 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q803.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q804.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q805.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q807.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q808.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q809.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q811.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q812.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q813.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q815.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q817.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q820.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q821.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q823.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q824.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q827.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q829.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q831.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q835.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q836.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q839.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q840.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q843.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q844.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q849.original_region chi hp hc hsq hqx hb

#print axioms range_801_850

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
