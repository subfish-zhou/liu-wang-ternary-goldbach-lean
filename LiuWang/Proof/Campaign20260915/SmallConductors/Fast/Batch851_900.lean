import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q851.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q852.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q853.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q856.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q857.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q859.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q860.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q861.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q863.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q865.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q868.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q869.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q871.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q872.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q876.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q877.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q879.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q881.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q883.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q884.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q885.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q887.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q888.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q889.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q892.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q893.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q895.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q897.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q899.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_851_900 {q : ℕ} [NeZero q]
    (hl : 851 ≤ q) (hu : q ≤ 900) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 901, 851 ≤ k.val → Admissible k.val →
    k.val = 851 ∨
    k.val = 852 ∨
    k.val = 853 ∨
    k.val = 856 ∨
    k.val = 857 ∨
    k.val = 859 ∨
    k.val = 860 ∨
    k.val = 861 ∨
    k.val = 863 ∨
    k.val = 865 ∨
    k.val = 868 ∨
    k.val = 869 ∨
    k.val = 871 ∨
    k.val = 872 ∨
    k.val = 876 ∨
    k.val = 877 ∨
    k.val = 879 ∨
    k.val = 881 ∨
    k.val = 883 ∨
    k.val = 884 ∨
    k.val = 885 ∨
    k.val = 887 ∨
    k.val = 888 ∨
    k.val = 889 ∨
    k.val = 892 ∨
    k.val = 893 ∨
    k.val = 895 ∨
    k.val = 897 ∨
    k.val = 899 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q851.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q852.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q853.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q856.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q857.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q859.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q860.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q861.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q863.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q865.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q868.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q869.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q871.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q872.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q876.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q877.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q879.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q881.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q883.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q884.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q885.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q887.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q888.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q889.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q892.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q893.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q895.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q897.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q899.original_region chi hp hc hsq hqx hb

#print axioms range_851_900

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
