import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q251.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q253.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q255.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q257.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q259.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q260.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q263.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q264.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q265.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q267.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q268.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q269.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q271.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q273.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q276.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q277.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q280.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q281.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q283.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q284.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q285.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q287.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q291.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q292.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q293.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q295.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q296.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q299.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_251_300 {q : ℕ} [NeZero q]
    (hl : 251 ≤ q) (hu : q ≤ 300) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 301, 251 ≤ k.val → Admissible k.val →
    k.val = 251 ∨
    k.val = 253 ∨
    k.val = 255 ∨
    k.val = 257 ∨
    k.val = 259 ∨
    k.val = 260 ∨
    k.val = 263 ∨
    k.val = 264 ∨
    k.val = 265 ∨
    k.val = 267 ∨
    k.val = 268 ∨
    k.val = 269 ∨
    k.val = 271 ∨
    k.val = 273 ∨
    k.val = 276 ∨
    k.val = 277 ∨
    k.val = 280 ∨
    k.val = 281 ∨
    k.val = 283 ∨
    k.val = 284 ∨
    k.val = 285 ∨
    k.val = 287 ∨
    k.val = 291 ∨
    k.val = 292 ∨
    k.val = 293 ∨
    k.val = 295 ∨
    k.val = 296 ∨
    k.val = 299 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q251.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q253.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q255.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q257.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q259.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q260.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q263.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q264.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q265.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q267.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q268.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q269.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q271.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q273.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q276.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q277.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q280.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q281.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q283.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q284.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q285.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q287.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q291.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q292.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q293.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q295.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q296.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q299.original_region chi hp hc hsq hqx hb

#print axioms range_251_300

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
