import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q301.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q303.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q305.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q307.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q308.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q309.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q311.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q312.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q313.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q316.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q317.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q319.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q321.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q323.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q327.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q328.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q329.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q331.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q332.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q335.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q337.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q339.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q340.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q341.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q344.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q345.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q347.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q348.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q349.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_301_350 {q : ℕ} [NeZero q]
    (hl : 301 ≤ q) (hu : q ≤ 350) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 351, 301 ≤ k.val → Admissible k.val →
    k.val = 301 ∨
    k.val = 303 ∨
    k.val = 305 ∨
    k.val = 307 ∨
    k.val = 308 ∨
    k.val = 309 ∨
    k.val = 311 ∨
    k.val = 312 ∨
    k.val = 313 ∨
    k.val = 316 ∨
    k.val = 317 ∨
    k.val = 319 ∨
    k.val = 321 ∨
    k.val = 323 ∨
    k.val = 327 ∨
    k.val = 328 ∨
    k.val = 329 ∨
    k.val = 331 ∨
    k.val = 332 ∨
    k.val = 335 ∨
    k.val = 337 ∨
    k.val = 339 ∨
    k.val = 340 ∨
    k.val = 341 ∨
    k.val = 344 ∨
    k.val = 345 ∨
    k.val = 347 ∨
    k.val = 348 ∨
    k.val = 349 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q301.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q303.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q305.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q307.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q308.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q309.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q311.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q312.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q313.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q316.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q317.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q319.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q321.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q323.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q327.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q328.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q329.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q331.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q332.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q335.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q337.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q339.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q340.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q341.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q344.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q345.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q347.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q348.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q349.original_region chi hp hc hsq hqx hb

#print axioms range_301_350

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
