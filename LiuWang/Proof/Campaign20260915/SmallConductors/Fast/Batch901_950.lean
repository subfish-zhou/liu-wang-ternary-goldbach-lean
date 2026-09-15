import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q901.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q903.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q904.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q905.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q907.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q908.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q911.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q913.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q915.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q916.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q917.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q919.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q920.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q921.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q923.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q924.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q929.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q932.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q933.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q935.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q937.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q939.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q940.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q941.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q943.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q947.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q948.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q949.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_901_950 {q : ℕ} [NeZero q]
    (hl : 901 ≤ q) (hu : q ≤ 950) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 951, 901 ≤ k.val → Admissible k.val →
    k.val = 901 ∨
    k.val = 903 ∨
    k.val = 904 ∨
    k.val = 905 ∨
    k.val = 907 ∨
    k.val = 908 ∨
    k.val = 911 ∨
    k.val = 913 ∨
    k.val = 915 ∨
    k.val = 916 ∨
    k.val = 917 ∨
    k.val = 919 ∨
    k.val = 920 ∨
    k.val = 921 ∨
    k.val = 923 ∨
    k.val = 924 ∨
    k.val = 929 ∨
    k.val = 932 ∨
    k.val = 933 ∨
    k.val = 935 ∨
    k.val = 937 ∨
    k.val = 939 ∨
    k.val = 940 ∨
    k.val = 941 ∨
    k.val = 943 ∨
    k.val = 947 ∨
    k.val = 948 ∨
    k.val = 949 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q901.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q903.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q904.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q905.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q907.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q908.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q911.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q913.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q915.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q916.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q917.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q919.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q920.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q921.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q923.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q924.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q929.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q932.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q933.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q935.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q937.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q939.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q940.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q941.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q943.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q947.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q948.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q949.original_region chi hp hc hsq hqx hb

#print axioms range_901_950

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
