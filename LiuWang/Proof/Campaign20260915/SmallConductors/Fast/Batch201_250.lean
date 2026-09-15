import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q201.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q203.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q204.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q205.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q209.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q211.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q212.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q213.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q215.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q217.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q219.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q220.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q221.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q223.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q227.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q228.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q229.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q231.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q232.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q233.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q235.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q236.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q237.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q239.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q241.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q244.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q247.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q248.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q249.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_201_250 {q : ℕ} [NeZero q]
    (hl : 201 ≤ q) (hu : q ≤ 250) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 251, 201 ≤ k.val → Admissible k.val →
    k.val = 201 ∨
    k.val = 203 ∨
    k.val = 204 ∨
    k.val = 205 ∨
    k.val = 209 ∨
    k.val = 211 ∨
    k.val = 212 ∨
    k.val = 213 ∨
    k.val = 215 ∨
    k.val = 217 ∨
    k.val = 219 ∨
    k.val = 220 ∨
    k.val = 221 ∨
    k.val = 223 ∨
    k.val = 227 ∨
    k.val = 228 ∨
    k.val = 229 ∨
    k.val = 231 ∨
    k.val = 232 ∨
    k.val = 233 ∨
    k.val = 235 ∨
    k.val = 236 ∨
    k.val = 237 ∨
    k.val = 239 ∨
    k.val = 241 ∨
    k.val = 244 ∨
    k.val = 247 ∨
    k.val = 248 ∨
    k.val = 249 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q201.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q203.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q204.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q205.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q209.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q211.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q212.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q213.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q215.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q217.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q219.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q220.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q221.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q223.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q227.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q228.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q229.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q231.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q232.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q233.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q235.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q236.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q237.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q239.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q241.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q244.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q247.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q248.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q249.original_region chi hp hc hsq hqx hb

#print axioms range_201_250

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
