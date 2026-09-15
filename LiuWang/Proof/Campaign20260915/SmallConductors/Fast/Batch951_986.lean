import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q951.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q952.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q953.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q955.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q956.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q957.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q959.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q964.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q965.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q967.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q969.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q971.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q973.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q977.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q979.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q983.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q984.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q985.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_951_986 {q : ℕ} [NeZero q]
    (hl : 951 ≤ q) (hu : q ≤ 986) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 987, 951 ≤ k.val → Admissible k.val →
    k.val = 951 ∨
    k.val = 952 ∨
    k.val = 953 ∨
    k.val = 955 ∨
    k.val = 956 ∨
    k.val = 957 ∨
    k.val = 959 ∨
    k.val = 964 ∨
    k.val = 965 ∨
    k.val = 967 ∨
    k.val = 969 ∨
    k.val = 971 ∨
    k.val = 973 ∨
    k.val = 977 ∨
    k.val = 979 ∨
    k.val = 983 ∨
    k.val = 984 ∨
    k.val = 985 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q951.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q952.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q953.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q955.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q956.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q957.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q959.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q964.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q965.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q967.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q969.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q971.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q973.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q977.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q979.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q983.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q984.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q985.original_region chi hc hsq hqx hb

#print axioms range_951_986

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
